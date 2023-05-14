-------------------------------- MODULE SystemSpec --------------------------------
EXTENDS Naturals, Sequences, SystemSpecMC, Hashing, TLC, FiniteSets, Sorting
CONSTANTS Key, Min, Max, NULL, NumOfInitialNodes, start_pt, end_pt, 
MsgCountWhenToTurnOffNode, MaxQueueSize
VARIABLES aggs, msgs, nodes, node_ids, endpts, turnedOff

Vars == <<aggs, msgs, nodes, node_ids, endpts, turnedOff>>

PutMessages == 
    /\ endpts[start_pt] = NULL
    /\ Len(msgs) > 0
    /\ endpts' = [ endpts EXCEPT ![start_pt] = Head(msgs) ]
    /\ msgs' = Tail(msgs)
    /\ UNCHANGED <<aggs, nodes, node_ids, turnedOff>>

MessageChannel == INSTANCE Channel WITH src <- start_pt
Aggregators == INSTANCE Aggregator WITH dst <- end_pt

Init == 
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
/\ endpts = [pt \in (1..NumOfInitialNodes \cup {start_pt, end_pt}) |-> 
                CASE pt \in 1..NumOfInitialNodes -> <<>>
                []OTHER -> NULL]
/\ turnedOff = FALSE

CheckIfDone == 
    /\ endpts[end_pt] = NULL
    /\ endpts[start_pt] = NULL
    /\ \A a \in DOMAIN aggs : (aggs[a].PrimaryMsgs = {} /\ aggs[a].SecondaryMsgs = {})
    /\ Len(msgs) = 0
    /\ PrintT("done")
    /\ UNCHANGED Vars

ClearEndPt == 
    /\ endpts[end_pt] /= NULL
    /\ endpts' = [ endpts EXCEPT ![end_pt] = NULL]
    /\ UNCHANGED <<aggs, msgs, nodes, node_ids, turnedOff>>

TurnOffNode == 
/\ turnedOff = FALSE
/\ Len(msgs) < MsgCountWhenToTurnOffNode
/\ \E aggId \in DOMAIN aggs : Cardinality(aggs[aggId].PrimaryMsgs) > 0
/\ Aggregators!NotifyTurnedOff(CHOOSE aggId \in DOMAIN aggs : Cardinality(aggs[aggId].PrimaryMsgs) > 0)
/\ turnedOff' = TRUE

TypeOK == 
/\ endpts[start_pt] \in MessageRecord \cup {NULL}
/\ endpts[end_pt] = NULL \/ endpts[end_pt] \subseteq MessageRecord
/\ \A id \in node_ids : 
        \A c \in 1..Len(endpts[id]) : endpts[id][c] \in MessageRecord \cup {NULL}
/\ node_ids \subseteq Nat
/\ \A id \in DOMAIN nodes : nodes[id] \in Nat
/\ \A id \in DOMAIN aggs : 
        /\ aggs[id].Id \in node_ids
        /\ aggs[id].Hash \in Nat
        /\ aggs[id].NodeBefore \in node_ids
        /\ aggs[id].PrimaryMsgs \subseteq MessageRecord
        /\ aggs[id].SecondaryMsgs \subseteq MessageRecord

Next == \/ /\ TurnOffNode
           /\ UNCHANGED msgs
        \/ /\ MessageChannel!Send(CHOOSE aggId \in node_ids : Len(endpts[aggId]) < MaxQueueSize)
           /\ UNCHANGED <<aggs, msgs, nodes, node_ids, turnedOff>>
        \/ /\ Aggregators!Check
           /\ UNCHANGED <<nodes, node_ids, msgs, turnedOff>>
        \/ PutMessages
        \/ ClearEndPt
        \/ CheckIfDone

GuaranteedDelivery == <>(endpts[end_pt] /= NULL)
        
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
=============================================================================