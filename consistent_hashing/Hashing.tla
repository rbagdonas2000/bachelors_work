----------------------------- MODULE Hashing -----------------------------
EXTENDS Naturals

GetHashCode(input, secret, min, max) == CHOOSE n \in min..max : TRUE
=============================================================================