----------------------------- MODULE Aggregator -----------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANTS NULL
VARIABLES dst, pool, ring
        


Send(hash, messages) == 
    /\ LET instance == CHOOSE agg \in pool : hash > agg[2] /\ hash <= agg[3]
       IN IF instance[4] = FALSE

ClearRing(messages) == ring' = ring \ messages

Aggregate(hash, messages) == Send(hash, messages) /\ ClearRing(messages)
=============================================================================