----------------------------- MODULE Aggregator -----------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANTS NULL
VARIABLES dst, aggs

\* [Id: Nat, 
\* Hash: Nat,  
\* NodeBefore: STRING,
\* PrimaryMsgs: {<<hash, msg>>}, 
\* SecondaryMsgs: {<<hash, msg>>}]
        
AddPrimaryMessage(id, hash_item) ==
/\ aggs' = [a \in DOMAIN aggs |->
            CASE aggs[a].Id = id -> [aggs[a] EXCEPT !.PrimaryMsgs = @ \cup {hash_item}]
            []OTHER -> aggs[a]]
/\ UNCHANGED dst

AddSecondaryMessage(id, hash_item) ==
/\ aggs' = [a \in DOMAIN aggs |->
            CASE aggs[a].Id = id -> [aggs[a] EXCEPT !.SecondaryMsgs = @ \cup {hash_item}]
            []OTHER -> aggs[a]]
/\ UNCHANGED dst

LOCAL AggregateAndSend(correlationId, nodeId) ==
LET finalMessage == <<>>
    msgs == { msg \in aggs[nodeId].PrimaryMsgs : msg[2].correlationId = correlationId }
IN  /\ \A m \in msgs : finalMessage' = Append(finalMessage, m[2].content)
    /\ dst' = finalMessage

LOCAL ClearPrimaryNode(correlationId, nodeId) ==
LET msgs == { msg \in aggs[nodeId].PrimaryMsgs : msg[2].correlationId = correlationId }
IN  aggs' = [a \in DOMAIN aggs |->
             CASE aggs[a].Id = nodeId -> [aggs[a] EXCEPT !.PrimaryMsgs = @ \ msgs]
             []OTHER -> aggs[a]]

LOCAL ClearSecondaryNode(correlationId, mainNodeId) ==
LET nodeId == CHOOSE n \in DOMAIN aggs : aggs[n].NodeBefore = mainNodeId
IN  LET msgs == { msg \in aggs[nodeId].PrimaryMsgs : msg[2].correlationId = correlationId }
    IN  aggs' = [a \in DOMAIN aggs |->
                CASE aggs[a].Id = nodeId -> [aggs[a] EXCEPT !.SecondaryMsgs = @ \ msgs]
                []OTHER -> aggs[a]]

Check ==
/\ \E id \in DOMAIN aggs : \E msg \in aggs[id].PrimaryMsgs : msg[2].isFinal
/\ LET AggId == CHOOSE id \in DOMAIN aggs : \E msg \in aggs[id].PrimaryMsgs : msg[2].isFinal
   IN LET CorrId == (CHOOSE msg \in aggs[AggId].PrimaryMsgs : msg[2].isFinal).correlationId
      IN /\ AggregateAndSend(CorrId, AggId)
         /\ ClearPrimaryNode(CorrId, AggId)
         /\ ClearSecondaryNode(CorrId, AggId)
=============================================================================