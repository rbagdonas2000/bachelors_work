-------------------------------- MODULE SystemSpec --------------------------------
EXTENDS Hashing, TLC
CONSTANTS Min, Max, Secret
VARIABLES x, y

Init == x = "stringas" /\ y = "stringas"

INSTANCE Hashing

Next == PrintT(GetHashCode(x, Secret, Min, Max)) /\ PrintT(GetHashCode(y, Secret, Min, Max))

=============================================================================