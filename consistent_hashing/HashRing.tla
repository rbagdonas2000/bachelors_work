----------------------------- MODULE HashRing -----------------------------
EXTENDS Naturals, Sequences, TLC, Hashing, FiniteSets
CONSTANTS NULL, NumOfMessages, MaxInstances, Key, Min, Max
VARIABLES dst, ring, src, pool

Aggregators == INSTANCE Aggregator

AddToRing(item) ==
    /\ item \notin ring
    /\ ring' = ring \union {item}

AddMessage == 
    /\ src /= NULL
    /\ src.correlationId /= NULL
    /\ src.content /= NULL
    /\ Cardinality(pool) < MaxInstances
    /\ LET hash == GetHashCode(src.correlationId, Key, Min, Max)
       IN AddToRing(<<hash, src>>)

Check == 
    /\ \E rec \in ring : rec[2].isFinal = TRUE
    /\ LET x == (CHOOSE rec \in ring : rec[2].isFinal = TRUE)[1]
         IN LET set == \A r \in ring : r[1] = x 
            IN /\ Aggregators!Aggregate(x, set)
               /\ RemoveFromRing(set)
               /\ UNCHANGED <<src, pool>>

        
=============================================================================
\* 1. Input the value to be assigned, let's call it X
\* 2. Calculate the absolute difference between X and each node's value: 
\*        A_diff = abs(X - 100)
\*        B_diff = abs(X - 34)
\*        C_diff = abs(X - 67)
\* 3. Find the minimum difference among the three:
\*        min_diff = min(A_diff, B_diff, C_diff)
\* 4. Assign X to the node with the closest higher value:
\*        if min_diff == A_diff:
\*              Assign X to A
\*        else if min_diff == B_diff:
\*              Assign X to B
\*        else:
\*              Assign X to C
