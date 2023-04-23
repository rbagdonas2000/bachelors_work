-------------------------------- MODULE SystemSpec --------------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANTS TimeOut, AggregatorsPool, NULL, MaxQueueSize
VARIABLES start_pt, manager, end_pt, q_buffer

Msg == [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "message"]

Channel == INSTANCE PointToPointChannel WITH src <- start_pt, queue <- q_buffer, dst <- manager

NodeManagerIns == INSTANCE NodeManager WITH src <- manager, dst <- end_pt

Init == /\ start_pt = Msg
        /\ manager = NULL
        /\ end_pt = NULL
        /\ q_buffer = <<>>

Next == \/ /\ Channel!Receive
           /\ UNCHANGED <<manager, end_pt>>
        \/ /\ Channel!Send
           /\ UNCHANGED <<start_pt, end_pt>>
        \/ \*/\ Print(<<"preparing to aggregate">>, TRUE)
           /\ NodeManagerIns!Next
           /\ UNCHANGED <<start_pt, q_buffer>>
=============================================================================