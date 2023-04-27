------------------------ MODULE PointToPointChannel ------------------------
EXTENDS Naturals
CONSTANTS NULL
VARIABLE src, dst

Send == /\ src /= NULL
        /\ dst = NULL
        /\ src' = NULL
        /\ dst' = src
=============================================================================