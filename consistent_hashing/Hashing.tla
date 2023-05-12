----------------------------- MODULE Hashing -----------------------------
EXTENDS Integers
CONSTANTS Min, Max

GetHashCode(val, key, min, max) == CHOOSE n \in Min..Max : TRUE
=============================================================================