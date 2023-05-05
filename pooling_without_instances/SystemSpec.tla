-------------------------------- MODULE SystemSpec --------------------------------
EXTENDS Naturals, Sequences, SystemSpecMC
CONSTANTS TimeOut, AggregatorsPool, NULL
VARIABLES start_pt, manager, end_pt, aggs, msgs

Vars == <<start_pt, manager, end_pt, aggs, msgs>>

PutMessages == 
    /\ start_pt = NULL
    /\ Len(msgs) > 0
    /\ start_pt' = Head(msgs)
    /\ msgs' = Tail(msgs)
    /\ UNCHANGED <<manager, end_pt, aggs>>

Channel == INSTANCE PointToPointChannel WITH src <- start_pt, dst <- manager

NodeManagerIns == INSTANCE NodeManager WITH src <- manager, dst <- end_pt

Init == /\ start_pt = NULL
        /\ manager = NULL
        /\ end_pt = NULL
        /\ msgs = Msgs
        /\ aggs = [a \in AggregatorsPool |-> [Id |-> a, 
                                              Buffer |-> <<>>, 
                                              Time |-> 0,
                                              CorrelationId |-> NULL]]

CheckIfDone == 
    /\ end_pt = NULL
    /\ start_pt = NULL
    /\ \A a \in AggregatorsPool : aggs[a].Time = 0
    /\ manager = NULL
    /\ Len(msgs) = 0
    /\ UNCHANGED Vars

ClearEndPt == 
    /\ end_pt /= NULL
    /\ end_pt' = NULL
    /\ UNCHANGED <<start_pt, manager, aggs, msgs>>

TypeOK == 
/\ start_pt \in MessageRecord \/ start_pt = NULL
/\ manager \in MessageRecord \/ manager = NULL
/\ \/ end_pt = <<>> 
   \/ end_pt = NULL
   \/ \A i \in 1..Len(end_pt) : end_pt[i] \in STRING
/\ \A a_id \in AggregatorsPool : /\ aggs[a_id].Id \in AggregatorsPool
                                 /\ aggs[a_id].Time \in 0..TimeOut
                                 /\ \/ aggs[a_id].Buffer = <<>> 
                                    \/ \A i \in 1..Len(aggs[a_id].Buffer) 
                                                : aggs[a_id].Buffer[i] \in STRING
                                 /\ \/ aggs[a_id].CorrelationId = NULL 
                                    \/ aggs[a_id].CorrelationId \in STRING
                                     
Next == \/ /\ Channel!Send
           /\ UNCHANGED <<end_pt, aggs, msgs>>
        \/ /\ NodeManagerIns!Next
           /\ UNCHANGED <<start_pt, msgs>>
        \/ PutMessages
        \/ ClearEndPt
        \/ CheckIfDone
        
GuaranteedDelivery == <>(end_pt /= NULL)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
=============================================================================