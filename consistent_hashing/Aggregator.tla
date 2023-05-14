----------------------------- MODULE Aggregator -----------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANTS NULL
VARIABLES dst, aggs

\* [Id: Nat, 
\* Hash: Nat,  
\* NodeBefore: STRING,
\* PrimaryMsgs: {<<hash, msg>>}, 
\* SecondaryMsgs: {<<hash, msg>>}]

AddMessage(primaryId, secondaryId, hash_item) ==
/\ aggs' = [ aggs EXCEPT ![primaryId].PrimaryMsgs = @ \cup {hash_item[2]},
                         ![secondaryId].SecondaryMsgs = @ \cup {hash_item[2]} ]
/\ UNCHANGED dst

LOCAL AggregateAndSend(c_id, nodeId) ==
    dst' = { msg \in aggs[nodeId].PrimaryMsgs : msg.correlationId = c_id }

ClearNodesFromMessages(correlationId, p_id) ==
LET s_id == CHOOSE n \in DOMAIN aggs : aggs[n].NodeBefore = p_id
IN  LET msgs1 == { msg \in aggs[p_id].PrimaryMsgs : msg.correlationId = correlationId }
        msgs2 == { msg \in aggs[s_id].SecondaryMsgs : msg.correlationId = correlationId }
    IN  aggs' = 
            [ aggs EXCEPT ![p_id].PrimaryMsgs = @ \ msgs1,
                          ![s_id].SecondaryMsgs = @ \ msgs2 ]

Check ==
/\ \E id \in DOMAIN aggs : \E msg \in aggs[id].PrimaryMsgs : msg.isFinal
/\ LET AggId == CHOOSE id \in DOMAIN aggs : \E msg \in aggs[id].PrimaryMsgs : msg.isFinal
   IN LET CorrId == (CHOOSE msg \in aggs[AggId].PrimaryMsgs : msg.isFinal).correlationId
      IN  /\ AggregateAndSend(CorrId, AggId)
          /\ ClearNodesFromMessages(CorrId, AggId)
=============================================================================