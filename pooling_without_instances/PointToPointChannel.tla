------------------------ MODULE PointToPointChannel ------------------------
CONSTANTS NULL
VARIABLE src, dst

Send == /\ src /= NULL
        /\ dst = NULL
        /\ src' = NULL
        /\ dst' = src
=============================================================================