----------------------------- MODULE Aggregator -----------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets, Hashing, Sorting
CONSTANTS NULL, Key, Min, Max, dst, MaxQueueSize
VARIABLES aggs, nodes, node_ids, endpts

LOCAL AddMessage(primaryId, secondaryId, hash_item) ==
/\ aggs' = [ aggs EXCEPT ![primaryId].PrimaryMsgs = @ \cup {hash_item[2]},
                         ![secondaryId].SecondaryMsgs = @ \cup {hash_item[2]} ]
/\ UNCHANGED <<nodes, node_ids>>

LOCAL ClearNodesFromMessages(correlationId, p_id) ==
LET s_id == CHOOSE n \in DOMAIN aggs : aggs[n].NodeBefore = p_id
IN  LET msgs1 == { msg \in aggs[p_id].PrimaryMsgs : msg.correlationId = correlationId }
        msgs2 == { msg \in aggs[s_id].SecondaryMsgs : msg.correlationId = correlationId }
    IN  aggs' = 
            [ aggs EXCEPT ![p_id].PrimaryMsgs = @ \ msgs1,
                          ![s_id].SecondaryMsgs = @ \ msgs2 ]

LOCAL AggregateAndSend(c_id, nodeId) ==
    endpts' = [ endpts EXCEPT ![dst] = 
                    { msg \in aggs[nodeId].PrimaryMsgs : msg.correlationId = c_id } ]

LOCAL IsBetween(lower, upper, hash) ==
LET wrapsOver == upper < lower
    aboveLower == hash >= lower
    belowUpper == upper >= hash
IN  IF wrapsOver
    THEN aboveLower \/ belowUpper
    ELSE aboveLower /\ belowUpper

LOCAL FindNextNode(nodeBefore) == 
CHOOSE i \in DOMAIN aggs : aggs[i].NodeBefore = nodeBefore

LOCAL FindNodeBefore(node_num, hash) ==
    IsBetween(nodes[node_num], nodes[FindNextNode(node_num)], hash)

LOCAL AddToRing(hash, item) ==
LET nodeBefore == CHOOSE i \in node_ids : FindNodeBefore(i, hash)
IN  LET primaryNode == FindNextNode(nodeBefore)
    IN  LET secondaryNode == FindNextNode(primaryNode)
        IN  AddMessage(primaryNode, secondaryNode, <<hash, item>>)

LOCAL TakeFromEndpoint == 
LET point == 
IF \E agg \in DOMAIN endpts : agg \in node_ids /\ Len(endpts[agg]) > 0 /\ Head(endpts[agg]).isFinal = FALSE
THEN CHOOSE agg \in DOMAIN endpts : agg \in node_ids /\ Len(endpts[agg]) > 0 /\ Head(endpts[agg]).isFinal = FALSE
ELSE CHOOSE agg \in DOMAIN endpts : agg \in node_ids /\ Len(endpts[agg]) > 0               
IN  /\ Head(endpts[point]) /= NULL
    /\ LET msg == Head(endpts[point])
       IN  /\ msg.correlationId /= NULL
           /\ msg.content /= NULL
           /\ LET hash == GetHashCode(msg.correlationId, Key, Min, Max)
              IN AddToRing(hash, msg)
    /\ endpts' = [ endpts EXCEPT ![point] = Tail(endpts[point]) ]

Check ==
\/ /\ \E id \in DOMAIN aggs : \E msg \in aggs[id].PrimaryMsgs : msg.isFinal
   /\ LET AggId == CHOOSE id \in DOMAIN aggs : \E msg \in aggs[id].PrimaryMsgs : msg.isFinal
      IN LET CorrId == (CHOOSE msg \in aggs[AggId].PrimaryMsgs : msg.isFinal).correlationId
         IN  /\ AggregateAndSend(CorrId, AggId)
             /\ ClearNodesFromMessages(CorrId, AggId)
\/ /\ \E agg \in DOMAIN endpts : agg \in node_ids /\ Len(endpts[agg]) > 0
   /\ TakeFromEndpoint

NotifyTurnedOff(n_id) ==
/\ node_ids' = node_ids \ {n_id}
/\ nodes' = [n \in DOMAIN nodes \ {n_id} |-> nodes[n]]
/\ IF endpts[n_id] = <<>>
    THEN endpts' = [e \in DOMAIN endpts \ {n_id} |-> endpts[e]]
    ELSE endpts' = [e \in DOMAIN endpts \ {n_id} |-> 
                    CASE e = CHOOSE i \in DOMAIN endpts \ {n_id} : 
                                    i \in Nat /\ Len(endpts[i]) < MaxQueueSize -> SortCustomRecords(endpts[e] \o endpts[n_id])[1]
                    []OTHER -> endpts[e]]
/\ LET newPrimary == FindNextNode(n_id)
   IN  aggs' = [a \in DOMAIN aggs \ {n_id} |->
                CASE a = newPrimary -> [Id |-> aggs[a].Id,
                                        Hash |-> aggs[a].Hash,
                                        NodeBefore |-> aggs[n_id].NodeBefore,
                                        PrimaryMsgs |-> aggs[a].PrimaryMsgs \cup aggs[a].SecondaryMsgs,
                                        SecondaryMsgs |-> {}]
                []OTHER -> aggs[a]]
=============================================================================
\* [Id: Nat, 
\* Hash: Nat,  
\* NodeBefore: node_ids,
\* PrimaryMsgs: {msg}, 
\* SecondaryMsgs: {msg}]