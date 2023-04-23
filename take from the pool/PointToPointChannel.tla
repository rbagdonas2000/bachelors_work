------------------------ MODULE PointToPointChannel ------------------------
EXTENDS Naturals, Sequences
CONSTANTS NULL, MaxQueueSize
VARIABLE src, dst, queue

Receive == /\ src /= NULL
           /\ Len(queue) < MaxQueueSize
           /\ queue' = Append(queue, src)
           /\ src' = NULL
           /\ UNCHANGED dst

Send == /\ Len(queue) > 0
        /\ dst = NULL
        /\ dst' = Head(queue)
        /\ queue' = Tail(queue)
        /\ UNCHANGED src
=============================================================================