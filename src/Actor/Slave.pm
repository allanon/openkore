package Actor::Slave;

use strict;
use Actor;
use Globals;
use base qw/Actor/;

sub new {
	my ($class, $type) = @_;
	
	my $actorType =
		(($type >= 6001 && $type <= 6016) || ($type >= 6048 && $type <= 6052)) ? 'Homunculus' :
		($type >= 6017 && $type <= 6046) ? 'Mercenary' :
		($type < 6000) ? 'Mercenary' :
	'Unknown';
Log::warning( "SLAVE with unknown type [$type] found! Assuming to be Homunculus.\n" ) if $actorType eq 'Unknown';
	
	return $class->SUPER::new ($actorType);
}

1;