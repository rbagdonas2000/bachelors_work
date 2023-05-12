----------------------------- MODULE HashRing -----------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets
CONSTANTS NULL, Key, Min, Max
VARIABLES dst, src, nodes, aggs, node_ids

Aggregators == INSTANCE Aggregator
Hash == INSTANCE Hashing

\* <<[Id |-> 1, Hash |-> 3],
\* [Id |-> 2, Hash |-> 39],
\* [Id |-> 3, Hash |-> 75]>>

LOCAL IsBetween(lower, upper, hash) ==
LET wrapsOver == upper < lower
    aboveLower == hash >= lower
    belowUpper == upper >= hash
IN  IF wrapsOver
    THEN aboveLower \/ belowUpper
    ELSE aboveLower /\ belowUpper

LOCAL FindNodeBefore(node_num, hash) ==
IF node_num = Cardinality(node_ids) \*Len(nodes) 
    THEN IsBetween(nodes[node_num], nodes[1], hash)
    ELSE IsBetween(nodes[node_num], nodes[node_num+1], hash)

LOCAL FindNodes(hash) ==
LET nodeBefore == CHOOSE i \in 1..Cardinality(node_ids) : FindNodeBefore(i, hash)
IN IF nodeBefore = Cardinality(node_ids)
    THEN <<1, 2>> 
    ELSE IF nodeBefore = Cardinality(node_ids) - 1
            THEN <<Cardinality(node_ids), 1>>
            ELSE <<nodeBefore+1, nodeBefore+2>>


LOCAL AddToRing(hash, item) == 
LET processingNodes == FindNodes(hash)
IN LET primaryNode == processingNodes[1]
       secondaryNode == processingNodes[2]
   IN /\ Aggregators!AddPrimaryMessage(aggs[primaryNode].Id, <<hash, item>>)
      /\ Aggregators!AddSecondaryMessage(aggs[secondaryNode].Id, <<hash, item>>)


AddMessage == 
    /\ src /= NULL
    /\ src.correlationId /= NULL
    /\ src.content /= NULL
    /\ LET hash == Hash!GetHashCode(src.correlationId, Key, Min, Max)
       IN AddToRing(hash, src)
    /\ src' = NULL

Next ==
\/ /\ AddMessage
   /\ UNCHANGED <<dst, nodes, node_ids>>
\/ /\ Aggregators!Check
   /\ /\ UNCHANGED <<src, nodes, node_ids>>
        
=============================================================================