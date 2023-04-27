-------------------------------- MODULE SystemSpec --------------------------------
EXTENDS Naturals, Sequences, TLC, SystemSpecMC
CONSTANTS TimeOut, AggregatorsPool, NULL
VARIABLES start_pt, manager, end_pt, aggs, msgs

Msgs == <<[correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "This"],
          [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "is"],
          [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "whole"],
          [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "message"],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "This"],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "is"],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "another"],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "message"]>>

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
    \*/\ Print(<<"DONE">>, TRUE)
    /\ UNCHANGED <<start_pt, manager, aggs, msgs, end_pt>>

PrintReceivedMessage == 
    /\ end_pt /= NULL
    \*/\ Print(<<end_pt>>, TRUE)
    /\ end_pt' = NULL
    /\ UNCHANGED <<start_pt, manager, aggs, msgs>>


TypeOK == 
    /\ start_pt \in UNION {MessageRecord, {NULL}}

Next == \/ /\ Channel!Send
           /\ UNCHANGED <<end_pt, aggs, msgs>>
        \/ /\ NodeManagerIns!Next
           /\ UNCHANGED <<start_pt, msgs>>
        \/ PutMessages
        \/ PrintReceivedMessage
        \/ CheckIfDone
        
=============================================================================