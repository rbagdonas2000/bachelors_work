-------------------------------- MODULE SystemSpec --------------------------------
EXTENDS Naturals, Sequences, SystemSpecMC, Hashing, TLC
CONSTANTS Key, Min, Max, NULL, NumOfInitialNodes
VARIABLES start_pt, ring, end_pt, aggs, msgs, nodes, node_ids

Vars == <<start_pt, ring, end_pt, aggs, msgs, nodes, node_ids>>

PutMessages == 
    /\ start_pt = NULL
    /\ Len(msgs) > 0
    /\ start_pt' = Head(msgs)
    /\ msgs' = Tail(msgs)
    /\ UNCHANGED <<ring, end_pt, aggs, nodes, node_ids>>

Channel == INSTANCE PointToPointChannel WITH src <- start_pt, dst <- ring

Ring == INSTANCE HashRing WITH src <- ring, dst <- end_pt

Init == /\ start_pt = NULL
        /\ ring = NULL
        /\ end_pt = NULL
        /\ msgs = Msgs
        /\ node_ids = 1..NumOfInitialNodes
        /\ nodes = [n \in 1..NumOfInitialNodes |-> ((Max - Min) \div NumOfInitialNodes) * n]
        /\ aggs = [a \in 1..NumOfInitialNodes |-> [Id |-> a, 
                                                   PrimaryMsgs |-> {}, 
                                                   SecondaryMsgs |-> {},
                                                   NodeBefore |-> 
                                                   IF a = 1
                                                   THEN NumOfInitialNodes
                                                   ELSE a - 1,
                                                   Hash |-> ((Max - Min) \div NumOfInitialNodes) * a]]

CheckIfDone == 
    /\ end_pt = NULL
    /\ start_pt = NULL
    /\ \A a \in DOMAIN aggs : (aggs[a].PrimaryMsgs = {} /\ aggs[a].SecondaryMsgs = {})
    /\ ring = NULL
    /\ Len(msgs) = 0
    /\ PrintT(aggs)
    /\ UNCHANGED Vars

ClearEndPt == 
    /\ end_pt /= NULL
    /\ PrintT(end_pt)
    /\ end_pt' = NULL
    /\ UNCHANGED <<start_pt, ring, aggs, msgs, nodes, node_ids>>
                                     
Next == \/ /\ Channel!Send
           /\ UNCHANGED <<end_pt, aggs, msgs, nodes, node_ids>>
        \/ /\ Ring!Next
           /\ UNCHANGED <<start_pt, msgs, nodes, node_ids>>
        \/ PutMessages
        \/ ClearEndPt
        \/ CheckIfDone
        
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
-----------------------------------------------------------------------------
\*THEOREM Spec => []TypeOK
=============================================================================