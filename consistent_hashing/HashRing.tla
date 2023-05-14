----------------------------- MODULE HashRing -----------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets, Hashing
CONSTANTS NULL, Key, Min, Max
VARIABLES dst, src, nodes, aggs, node_ids

Aggregators == INSTANCE Aggregator

LOCAL IsBetween(lower, upper, hash) ==
LET wrapsOver == upper < lower
    aboveLower == hash >= lower
    belowUpper == upper >= hash
IN  IF wrapsOver
    THEN aboveLower \/ belowUpper
    ELSE aboveLower /\ belowUpper

LOCAL FindNodeBefore(node_num, hash) ==
IF node_num = Cardinality(node_ids)
THEN IsBetween(nodes[node_num], nodes[1], hash)
ELSE IsBetween(nodes[node_num], nodes[node_num+1], hash)

LOCAL FindNextNode(nodeBefore) == 
    CHOOSE i \in DOMAIN aggs : aggs[i].NodeBefore = nodeBefore

LOCAL AddToRing(hash, item) ==
LET nodeBefore == CHOOSE i \in 1..Cardinality(node_ids) : FindNodeBefore(i, hash)
IN  LET primaryNode == FindNextNode(nodeBefore)
    IN  LET secondaryNode == FindNextNode(primaryNode)
        IN  Aggregators!AddMessage(primaryNode, secondaryNode, <<hash, item>>)

AddMessage == 
    /\ src /= NULL
    /\ src.correlationId /= NULL
    /\ src.content /= NULL
    /\ LET hash == GetHashCode(src.correlationId, Key, Min, Max)
       IN AddToRing(hash, src)
    /\ src' = NULL

Next ==
\/ /\ AddMessage
   /\ UNCHANGED <<dst, nodes, node_ids>>
\/ /\ Aggregators!Check
   /\ /\ UNCHANGED <<src, nodes, node_ids>>
        
=============================================================================