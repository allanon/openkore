############################
# MonsterDB plugin for OpenKore by Damokles
#
# This software is open source, licensed under the GNU General Public
# License, version 2.
#
# This plugin extends all functions which use 'checkMonsterCondition'.
# Basically these are AttackSkillSlot, equipAuto, AttackComboSlot, monsterSkill.
#
# Following new checks are possible:
#
# target_Element (list)
# target_notElement (list)
# target_Race (list)
# target_notRace (list)
# target_Size (list)
# target_notSize (list)
# target_hpLeft (range)
#
# In equipAuto you have to leave the target_ part,
# this is due some coding inconsistency in the funtions.pl
#
# You can use monsterEquip if you think that equipAuto is to slow.
# It supports the new equip syntax. It is event-driven and is called
# when a monster: is attacked, changes status, changes element
#
# Note: It will check all monsterEquip blocks but it respects priority.
# If you check in the first block for element fire and in the second
# for race Demi-Human and in both you use different arrows but in the
# Demi-Human block you use a bow, it will take the arrows form the first
# matching block and equip the bow since the fire block didn't specified it.
#
#
# Note: monsterEquip will modify your attackEquip_{slot} so don't be surprised
# about having other attackEquips as you set before.
#
# Be careful with right and leftHand those slots will not be checked for
# two-handed weapons that may conflict.
#
# Example:
# monsterEquip {
# 	target_Element Earth
# 	equip_arrow Fire Arrow
# }
#
# For the element names just scroll a bit down and you'll find it.
# You can check for element Lvls too, eg. target_Element Dark4
#
# $Revision: 5549 $
# $Id: monsterDB.pl 5549 2007-03-21 00:55:47Z h4rry_84 $
############################

package monsterDB;

use strict;
use Plugins;
use Globals qw(%config %monsters $accountID %equipSlot_lut @ai_seq @ai_seq_args $char $monstersList %jobs_lut);
use Settings;
use Log qw(message warning error debug);
use Misc qw(bulkConfigModify checkMonsterCondition checkSelfCondition);
use Translation qw(T TF);
use Utils;
use Plugins::DBI;

use constant HP           => 0;
use constant SIZE         => 1;
use constant RACE         => 2;
use constant ELEMENT      => 3;
use constant RANGE        => 4;
use constant DEF          => 5;
use constant MDEF         => 6;
use constant SEC_PER_TILE => 7;
use constant TOTAL_FIELDS => 8;

Plugins::register('monsterDB', 'extends Monster infos', \&onUnload);
my $hooks = Plugins::addHooks(
    [ 'checkSelfCondition'         => \&extendedSelfCheck ],
    [ 'checkPlayerCondition'       => \&extendedPlayerCheck ],
    [ 'checkMonsterCondition'      => \&extendedCheck ],
    [ 'packet_skilluse'            => \&onPacketSkillUse ],
    [ 'packet/skill_use_no_damage' => \&onPacketSkillUseNoDamage ],
    [ 'packet_attack'              => \&onPacketAttack ],
    [ 'attack_start'               => \&onAttackStart ],
    [ 'changed_status'             => \&onStatusChange ],
    [ 'Actor::setStatus::change'   => \&onSetStatus ],
    [ 'packet/monster_hp_info'     => \&onPacketMonsterHpInfo ],
);


our $dbh = Plugins::DBI->new;
our @per_attack_blocks;
our @monsterDB;
our @element_lut = qw(Neutral Water Earth Fire Wind Poison Holy Dark Sense Undead);
our @race_lut = qw(Formless Undead Brute Plant Insect Fish Demon Demi-Human Angel Dragon);
our @size_lut = qw(Small Medium Large);
our %skillChangeElement = qw(
	NPC_CHANGEWATER Water
	NPC_CHANGEGROUND Earth
	NPC_CHANGEFIRE Fire
	NPC_CHANGEWIND Wind
	NPC_CHANGEPOISON Poison
	NPC_CHANGEHOLY Holy
	NPC_CHANGEDARKNESS Dark
	NPC_CHANGETELEKINESIS Sense
);
our $elementBonus_lut = [];
our $calcSpellDamage = {
    'Cold Bolt'      => sub { return { element => 1, dmg => $_[0] * matk() * ( 1 + equipped_card( 'Siroma' ) * 0.25 ) }; },
    'Fire Bolt'      => sub { return { element => 3, dmg => $_[0] * matk() * ( 1 + equipped_card( 'Imp' ) * 0.25 ) }; },
    'Lightning Bolt' => sub { return { element => 4, dmg => $_[0] * matk() }; },
    'Thunderstorm'   => sub { return { element => 4, dmg => $_[0] * matk() * 0.8 }; },
    'Fire Ball'      => sub { return { element => 3, dmg => ( 0.7 + 0.1 * $_[0] ) * matk() }; },
    'Soul Strike'    => sub { return { element => 8, dmg => ( 1 + int( $_[0] / 2 ) ) * matk() }; },
};

our $card_map ||= {    #
    'Imp'           => 4433,
    'Siroma'        => 4416,
    'Draco Egg'     => 4471,
    'Bradium Golem' => 4472,
};

sub matk {

    # Variance on weapon matk is 0.1 * weapon_level * weapon_base_matk. Let's assume that:
    #  1. Given that attack_magic_max has refine rate factored in, it's more than weapon_base_matk anyway, and
    #  2. Half the time, the variance will be a positive number.
    # So let's use 85% of attack_magic_max, and we'll be over that most (or possibly all, if the refine rate is very high) of the time.
    # return $char->{attack_magic_min} + $char->{attack_magic_max} * 0.85;

    # Try to calculate the real minimum matk.
    my $matk_min = $char->{attack_magic_min} + $char->{attack_magic_max} - matk_variance();;
    $matk_min *= 1.5 if $char->{statuses}->{'EFST_MAGICPOWER'};
    return $matk_min;
}

sub matk_variance {

    # Ignore left hand (dual-wielded dagger).
    my $weapon = $char->{equipment}->{rightHand};
    return 0 if !$weapon;

    # Assume weapon is level 3.
    my $weapon_lv   = 3;
    my $weapon_matk = $char->{attack_magic_max} - $weapon->{upgrade} * 5;
    return 0.1 * $weapon_lv * $weapon_matk;
}

sub equipped_card {
    my ( $card_name ) = @_;
    my $card_id = $card_map->{$card_name};
    return if !$card_id;
    my $count = 0;
    foreach my $item ( @{ $char->inventory->getItems } ) {
        next if !$item->{identified};
        $count += grep { $_ == $card_id } unpack 'vvvv', $item->{cards};
    }
    return $count;
}

debug ("MonsterDB: Finished init.\n",'monsterDB',2);
loadMonDB(); # Load MonsterDB into Memory

sub onUnload {
	Plugins::delHooks($hooks);
	@monsterDB = undef;
}

sub loadMonDB {
	@monsterDB = undef;

	debug( "MonsterDB: Loading DataBase\n", 'monsterDB', 2 );
	foreach my $filename ( qw( monsterDB.txt monsterDB_updates.txt ) ) {
		my $file = Settings::getTableFilename( $filename );
		if ( !$file ) {
			error( "MonsterDB: cannot find $filename\n", 'monsterDB' );
			next;
		}
		if ( !-r $file ) {
			error( "MonsterDB: cannot load $file\n", 'monsterDB' );
			next;
		}
		my $fp = Utils::TextReader->new( $file );
		while ( !$fp->eof ) {
			my $line = $fp->readLine;
			$line =~ s/\#.*//gos;
			my @data = $line =~ /(-1|\d+)/go;
			next if @data < 2;
			next if $data[0] < 1001 || $data[0] > 9999;
			my $id = ( shift @data ) - 1000;
			$monsterDB[$id] ||= [];
			$monsterDB[$id][$_] = $data[$_] foreach grep { $data[$_] != -1 } 0 .. $#data;
		}
	}
	message TF( "MonsterDB: %d monsters in database\n", scalar grep {$_} @monsterDB ), 'monsterDB';

	loadElements();
}

sub onPacketMonsterHpInfo {
    my ( undef, $args ) = @_;

    # Ignore invalid data.
    return if !$args->{hp_max};
    return if $args->{hp_max} < 1;
    return if $args->{hp_max} > 0x7fffffff;

    my $mob = $monstersList->getByID( $args->{ID} );
    return if !$mob;

    my $monsterInfo = $monsterDB[ $mob->{nameID} - 1000 ] ||= [];
    return if $monsterInfo && $monsterInfo->[HP] == $args->{hp_max};

    my $file = Settings::getTableFilename( 'monsterDB_updates.txt' );
    return if !$file;

    message "Updating max hp [$monsterInfo->[HP] => $args->{hp_max}] for monster [$mob->{nameID}].\n", 'monsterDB';

    $monsterInfo->[HP] = $args->{hp_max};

    open my $fp, '>>', $file;
    print $fp join( ' ', $mob->{nameID}, @$monsterInfo ) . "\n";
    close $fp;
}

sub loadElements {
    my $file = Settings::getTableFilename( 'monsterDB_elements.txt' );
    error( "MonsterDB: cannot load $file\n", 'monsterDB', 0 ) unless -r $file;
    open my $fp, '<', $file;
    $elementBonus_lut = [];
    my $level    = 1;
    my $def_elem = 0;
    while ( my $line = <$fp> ) {
        $line =~ s/\s+$//os;
        next if $line =~ /^\s*(#|$)/os;
        my @fields = split /\t/, $line;

        if ( $fields[0] =~ /^L(\d)$/ ) {
            $level    = $1;
            $def_elem = 0;
            next;
        }

        foreach my $atk_elem ( 0 .. 9 ) {
            $elementBonus_lut->[$level]->[$atk_elem]->[$def_elem] = $fields[ $atk_elem + 1 ] / 100;
        }

        $def_elem++;
    }
}

sub extendedSelfCheck {
    my ( undef, $args ) = @_;

    return $args->{return} = 0 if !extendedActorCheck( undef, { prefix => $args->{prefix}, actor => $char } );

    if ( $config{"$args->{prefix}_actionQueued"} ) {
        return $args->{return} = 0 if !grep { existsInList( $config{"$args->{prefix}_actionQueued"}, $_ ) } @ai_seq;
    }
    if ( $config{"$args->{prefix}_notActionQueued"} ) {
        return $args->{return} = 0 if grep { existsInList( $config{"$args->{prefix}_notActionQueued"}, $_ ) } @ai_seq;
    }

    if ( $config{"$args->{prefix}_aggressives"} ) {
        my $nmobs = scalar @{ $monstersList && $monstersList->getItems || [] };
        return $args->{return} = 0 if !inRange( $nmobs, $config{"$args->{prefix}_aggressives"} );
    }

    if ( $config{"$args->{prefix}_nearbyMonsters"} ) {
        my $exists = 0;
        foreach ( @{ $monstersList->getItems } ) {
            $exists = 1, last if existsInList( $config{"$args->{prefix}_nearbyMonsters"}, $_->{name} );
        }
        return $args->{return} = 0 if !$exists;
    }

    if ( $config{"$args->{prefix}_expPercent"} && $char->{exp_max} ) {
        return $args->{return} = 0 if !inRange( 100 * $char->{exp} / $char->{exp_max}, $config{"$args->{prefix}_expPercent"} );
    }

    if ( $config{"$args->{prefix}_expPercent"} && $char->{exp_job_max} ) {
        return $args->{return} = 0 if !inRange( 100 * $char->{exp_job} / $char->{exp_job_max}, $config{"$args->{prefix}_jobExpPercent"} );
    }

    if ( $config{"$args->{prefix}_weaponType"} ) {
        my $weapon1 = $dbh->subtype( $char->{equipment}->{rightHand} );
        my $weapon2 = $dbh->subtype( $char->{equipment}->{leftHand} );
        return $args->{return} = 0 if !grep { existsInList( $config{"$args->{prefix}_weaponType"}, $_ ) } $weapon1, $weapon2;
    }

    return 1;
}

sub extendedPlayerCheck {
    my ( undef, $args ) = @_;

    return $args->{return} = 0 if !extendedActorCheck( undef, { prefix => $args->{prefix}, actor => $args->{player} } );
}

sub extendedActorCheck {
    my ( undef, $args ) = @_;

    my $actor = $args->{actor};

    if ( $config{"$args->{prefix}_maxHp"} ) {
        return $args->{return} = 0 if !inRange( $actor->{max_hp}, $config{"$args->{prefix}_maxHp"} );
    }

    if ( $config{"$args->{prefix}_maxSp"} ) {
        return $args->{return} = 0 if !inRange( $actor->{max_sp}, $config{"$args->{prefix}_maxSp"} );
    }

    if ( $config{"$args->{prefix}_job"} ) {
        return $args->{return} = 0 if !existsInList( $config{"$args->{prefix}_job"}, $jobs_lut{ $actor->{jobID} } );
    }

    if ( $config{"$args->{prefix}_notJob"} ) {
        return $args->{return} = 0 if existsInList( $config{"$args->{prefix}_notJob"}, $jobs_lut{ $actor->{jobID} } );
    }

    if ( $config{"$args->{prefix}_whenGround"} ) {
        return $args->{return} = 0 if !Misc::whenGroundStatus( calcPosition( $actor ), $config{"$args->{prefix}_whenGround"} );
    }

    if ( $config{"$args->{prefix}_whenNotGround"} ) {
        return $args->{return} = 0 if Misc::whenGroundStatus( calcPosition( $actor ), $config{"$args->{prefix}_whenNotGround"} );
    }

    if ( $config{"$args->{prefix}_moving"} ) {
        my $moving = 0;
        if ( $actor->{time_move_calc} && time < $actor->{time_move} + $actor->{time_move_calc} ) {
            $moving = 1 if $actor->{pos}->{x} != $actor->{pos_to}->{x};
            $moving = 1 if $actor->{pos}->{y} != $actor->{pos_to}->{y};
        }

        return $args->{return} = 0 if !$moving;
    }

    if ( $config{"$args->{prefix}_notMoving"} ) {
        my $moving = 0;
        if ( $actor->{time_move_calc} && time < $actor->{time_move} + $actor->{time_move_calc} ) {
            $moving = 1 if $actor->{pos}->{x} != $actor->{pos_to}->{x};
            $moving = 1 if $actor->{pos}->{y} != $actor->{pos_to}->{y};
        }

        return $args->{return} = 0 if $moving;
    }

    if ( $config{"$args->{prefix}_monstersNearby"} ) {
        my ( $needed, $range ) = split /\s+/, $config{"$args->{prefix}_monstersNearby"}, 2;
        my $mobs = $monstersList && $monstersList->getItems || [];
        my $nearby = 0;
        foreach my $mob ( @$mobs ) {
            next if $mob eq $actor;
            my $dist = distance( $actor->{pos_to}, $mob->{pos_to} );
            next if !inRange( $dist, $range );
            $nearby++;
        }
        return $args->{return} = 0 if $nearby < $needed;
    }

    return 1;
}

sub extendedCheck {
	my (undef, $args) = @_;

	return 0 if !$args->{monster} || $args->{monster}->{nameID} eq '';

    return $args->{return} = 0 if !extendedActorCheck( undef, { prefix => $args->{prefix}, actor => $args->{monster} } );

	my $monsterInfo = $monsterDB[(int($args->{monster}->{nameID}) - 1000)];

	if (!defined $monsterInfo) {
		debug("monsterDB: Monster {$args->{monster}->{name}} not found\n", 'monsterDB', 2);
		#return 0;
		$monsterInfo ||= [];
		$monsterInfo->[HP] = 0;
	}


    my $base_prefix = ( $args->{prefix} =~ /^(.*)_target$/o )[0] || $args->{prefix};
    my $element_id  = $monsterInfo->[ELEMENT] % 10;
    my $element     = $element_lut[$element_id];
    my $element_lvl = int( $monsterInfo->[ELEMENT] / 20 );
    my $race        = $race_lut[ $monsterInfo->[RACE] ];
    my $size        = $size_lut[ $monsterInfo->[SIZE] ];
    my $mdef        = $monsterInfo->[MDEF] || 0;
    my $spt         = $monsterInfo->[SEC_PER_TILE] || 0;

	if ($args->{monster}->{element} && $args->{monster}->{element} ne '') {
		$element = $args->{monster}->{element};
		debug("monsterDB: Monster $args->{monster}->{name} has changed element to $args->{monster}->{element}\n", 'monsterDB', 3);
	}

	if ($args->{monster}->statusActive('BODYSTATE_STONECURSE, BODYSTATE_STONECURSE_ING')) {
		$element = 'Earth';
		debug("monsterDB: Monster $args->{monster}->{name} is petrified changing element to Earth\n", 'monsterDB', 3);
	}

	if ($args->{monster}->statusActive('BODYSTATE_FREEZING')) {
		$element = 'Water';
		debug("monsterDB: Monster $args->{monster}->{name} is frozen changing element to Water\n", 'monsterDB', 3);
	}

# Porcellio MDEF: soft -60, hard 0.75
# soft = int+(vit+dex)/5+lv/4 = 40+(28+62)/5+85/4 = 79.25
# Metaling  MDEF: soft -23, hard 0.797
# soft = int+(vit+dex)/5+lv/4 = 17+(49+50)/5+81/4 = 40.05
    if ( $config{ $args->{prefix} . '_smartLevel' } ) {
        my $max_level = $config{ "$args->{prefix}_smartLevel" };
        my ( $slot ) = $args->{prefix} =~ /^(attackSkillSlot_\d+)_target$/o;
        if ( $slot && $calcSpellDamage->{ $config{$slot} } ) {
            my $hp = $monsterInfo->[HP] + $args->{monster}->{deltaHp};
            foreach ( 1 .. $max_level ) {
                my $calc = $calcSpellDamage->{ $config{$slot} }->( $_ );
                my $dmg = $calc->{dmg} * $elementBonus_lut->[$element_lvl]->[ $calc->{element} ]->[$element_id] * 110 / ( 110 + $mdef );
                $dmg *= 1 + 0.1 * equipped_card( 'Draco Egg' )     if $race eq 'Dragon';
                $dmg *= 1 + 0.1 * equipped_card( 'Bradium Golem' ) if $race eq 'Brute';
                $config{"${slot}_lvl"} = $_;
                $config{"${slot}_lvl"} = int $_ / 2 + 0.5 if $char->{statuses}->{EFST_DOUBLECASTING} && $config{$slot} =~ / Bolt$/;
                # message( "monsterDB: [$config{$slot}] (element $calc->{element}) smart level [$_] does $dmg/$hp damage to L$element_lvl $element_id mob with [$elementBonus_lut->[$element_lvl]->[ $calc->{element} ]->[$element_id]] multiplier\n" ) if $dmg >= $hp;
                last if $dmg >= $hp;
            }
        }
    }

	if ($config{$args->{prefix} . '_Element'}
	&& (!existsInList($config{$args->{prefix} . '_Element'},$element)
		&& !existsInList($config{$args->{prefix} . '_Element'},$element.$element_lvl))) {
	return $args->{return} = 0;
	}

	if ($config{$args->{prefix} . '_notElement'}
	&& (existsInList($config{$args->{prefix} . '_notElement'},$element)
		|| existsInList($config{$args->{prefix} . '_notElement'},$element.$element_lvl))) {
	return $args->{return} = 0;
	}

	if ($config{$args->{prefix} . '_Race'}
	&& !existsInList($config{$args->{prefix} . '_Race'},$race)) {
	return $args->{return} = 0;
	}

	if ($config{$args->{prefix} . '_notRace'}
	&& existsInList($config{$args->{prefix} . '_notRace'},$race)) {
	return $args->{return} = 0;
	}

	if ($config{$args->{prefix} . '_Size'}
	&& !existsInList($config{$args->{prefix} . '_Size'},$size)) {
	return $args->{return} = 0;
	}

    if ( $config{ $args->{prefix} . '_range' } && !inRange( $monsterInfo->[RANGE] || 0, $config{"$args->{prefix}_range"} ) ) {
        return $args->{return} = 0;
    }

    # Normal player speed is 0.15s/tile.
    return $args->{return} = 0 if $config{ "$args->{prefix}_moveSecPerTile" } && !inRange( $spt || 0, $config{"$args->{prefix}_moveSecPerTile"} );

    return $args->{return} = 0 if $config{"$args->{prefix}_timeToArrival"} && !inRange( countSteps( calcPosition( $args->{monster} ), calcPosition( $char ) ) * $spt || 0, $config{"$args->{prefix}_timeToArrival"} );

	if ($config{$args->{prefix} . '_notSize'}
	&& existsInList($config{$args->{prefix} . '_notSize'},$size)) {
	return $args->{return} = 0;
	}

    if ( $config{"$args->{prefix}_hpLeft"} ) {
        my $amt = $config{"$args->{prefix}_hpLeft"};
        $amt =~ s{(\d+)\%}{$monsterInfo->[HP] * $1 / 100}eos;
        return $args->{return} = 0 if !inRange( $monsterInfo->[HP] + $args->{monster}->{deltaHp}, $amt );
    }

    if ( $config{"$args->{prefix}_def"} ) {
        return $args->{return} = 0 if !inRange( $monsterInfo->[DEF], $config{"$args->{prefix}_def"} );
    }

    if ( $config{"$args->{prefix}_mdef"} ) {
        return $args->{return} = 0 if !inRange( $monsterInfo->[MDEF], $config{"$args->{prefix}_mdef"} );
    }

	return 1;
}

sub onPacketSkillUse {
    monsterHp( $monsters{ $_[1]->{targetID} }, $_[1]->{disp} ) if $_[1]->{disp};
    if ( $_[1]->{sourceID} eq $accountID && @per_attack_blocks ) {
        monsterEquip( $monsters{ $_[1]->{targetID} }, \@per_attack_blocks );
    }
}

sub onPacketSkillUseNoDmg {
	my (undef,$args) = @_;
	return 1 unless $monsters{$args->{targetID}} && $monsters{$args->{targetID}}{nameID};
	if (
		$args->{targetID} eq $args->{sourceID} && $args->{targetID} ne $accountID
		&& $skillChangeElement{$args->{skillID}}
	) {
		$monsters{$args->{targetID}}{element} = $skillChangeElement{$args->{skillID}};
		monsterEquip($monsters{$args->{targetID}});
		return 1;
	}
}

sub onPacketAttack {
    monsterHp( $monsters{ $_[1]->{targetID} }, $_[1]->{msg} ) if $_[1]->{msg};
    if ( $_[1]->{sourceID} eq $accountID && @per_attack_blocks ) {
        monsterEquip( $monsters{ $_[1]->{targetID} }, \@per_attack_blocks );
    }
}

sub monsterHp {
	my ($mob, $message) = @_;
	return 1 unless $mob && $mob->{nameID};
	
	my $monsterInfo = $monsterDB[(int($mob->{nameID}) - 1000)] || [];
	
    my $dist = Utils::distance( Utils::calcPosition( $mob ), Utils::calcPosition( $char ) );
    my $hp = $monsterInfo->[HP] || 0;
	$$message =~ s~(?=\n)~TF(" (Dist: %.1f) (HP: %d/%d) (MATK: %d+%d)", $dist, $hp + $mob->{deltaHp}, $hp, $char->{attack_magic_min}, $char->{attack_magic_max})~seo;
}

sub monsterDB {
    my ( $mob ) = @_;
    return if !$mob;
    return if !$mob->{nameID};
    return $monsterDB[ int $mob->{nameID} - 1000 ];
}

sub onAttackStart {
	my (undef,$args) = @_;
	monsterEquip($monsters{$args->{ID}});
}

sub onSetStatus {
    my ( undef, $args ) = @_;

    return if $args->{actor_type} ne 'Actor::You';
    return if $args->{handle} ne 'EFST_SIT';
    my $armor = $char->{equipment}->{armor};

    if ( $args->{flag} ) {

        # Are we wearing an armor compounded with Earth Deleter Card or Sky Deleter Card? If so, take them off.
        return if !$armor;
        my $card = unpack 'v', $armor->{cards};
        if ( $card == 4158 || $card == 4279 ) {
            Log::message "Removing armor which would prevent regen: $armor\n";
            $config{attackEquip_armor} = $armor->{name};
            $armor->unequip;
        }
    } else {
        return if $armor;

        # Put the armor back on? Or wait until we attack?
    }
}

sub onStatusChange {
	my (undef, $args) = @_;

	return unless $args->{changed};
	my $actor = $args->{actor};
	return unless (UNIVERSAL::isa($actor, 'Actor::Monster'));
	my $index = binFind(\@ai_seq, 'attack');
	return unless defined $index;
	return unless $ai_seq_args[$index]->{target} == $actor->{ID};
	monsterEquip($actor);
}

sub monsterEquip {
    my ( $monster, $blocks ) = @_;
    return unless $monster;

    if ( !$blocks ) {
        $blocks            = [];
        @per_attack_blocks = ();
        for ( my $i = 0 ; exists $config{"monsterEquip_$i"} ; $i++ ) {
            push @$blocks,           $i if !$config{"monsterEquip_${i}_disabled"};
            push @per_attack_blocks, $i if $config{"monsterEquip_${i}_checkEachAttack"};
        }
    }

    my %equip_list;

    foreach my $i ( @$blocks ) {
		next if !checkMonsterCondition( "monsterEquip_${i}_target", $monster );
		next if !checkSelfCondition( "monsterEquip_$i" );
        foreach my $slot ( values %equipSlot_lut ) {
            next if $equip_list{$slot};
            my ( $name ) = grep { $_ eq 'nothing' || Actor::Item::get( $_ ) } split /\s*,\s*/, $config{"monsterEquip_${i}_equip_$slot"} || '';
            next if !$name;
            $equip_list{$slot} = $name;
            debug "monsterDB: using $name\n", 'monsterDB';
        }
    }

    foreach ( keys %equip_list ) {
        if ( $equip_list{$_} eq 'nothing' ) {
            my $item = $char->{equipment}->{$_};
            Log::warning( "WEIRD ITEM $item " . ref( $item ) . "\n" ) if $item && ref $item =~ /^(|HASH|ARRAY)$/os;
            $item->unequipFromSlot( $_ ) if $item && ref $item !~ /^(|HASH|ARRAY)$/os;
            $config{"attackEquip_$_"} = undef;
        } else {
            $config{"attackEquip_$_"} = $equip_list{$_};
        }
    }

    Actor::Item::scanConfigAndEquip( 'attackEquip' );
}

1;
