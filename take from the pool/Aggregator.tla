----------------------------- MODULE Aggregator -----------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANTS NULL, TimeOut, AggId
VARIABLES src, dst, time, buffer, correlationId

\* TypeInvariant == /\ buffer \in FullReport
\*                  /\ time \in Nat
\*                  /\ src \in UNION {reports, {NULL}}
                 
Init == /\ buffer = <<>>
        /\ time = 0
        /\ src = NULL
        /\ dst = NULL
        /\ correlationId = NULL

GetCorrelationId == correlationId

SetCorrelationId(cid) == /\ correlationId = NULL
                         /\ correlationId' = cid
                         /\ Print(<<"preparing to aggregate", GetCorrelationId, cid, src, dst, time, buffer>>, TRUE)
                         /\ UNCHANGED <<src, dst, time, buffer>>
                         

AddToSource(content) == /\ src = NULL
                        /\ src' = content
                        /\ UNCHANGED <<dst, time, buffer, correlationId>>
        
ProcessMessage == /\ src /= NULL
                  /\ buffer' = Append(buffer, src)
                  /\ src' = NULL
                  /\ time' = time + 1
                  /\ UNCHANGED <<dst, correlationId>>

Send == /\ Len(buffer) > 0
        /\ dst = NULL
        /\ dst' = buffer
        /\ buffer' = <<>>
        /\ time' = 0
        /\ correlationId' = NULL
        /\ UNCHANGED src

Aggregate == /\ IF time = TimeOut
                    THEN Send
                    ELSE ProcessMessage
=============================================================================