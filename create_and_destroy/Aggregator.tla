----------------------------- MODULE Aggregator -----------------------------
EXTENDS Naturals, Sequences
CONSTANTS NULL, TimeOut
VARIABLES aggs, dst, pool
        
ProcessMessage(id, item) == 
/\ aggs[id].Time < TimeOut
/\ aggs' = [a \in DOMAIN aggs |-> 
            CASE aggs[a].Id = id -> [Id |-> id, 
                                    Buffer |-> Append(aggs[a].Buffer, item.content), 
                                    Time |-> aggs[a].Time + 1, 
                                    CorrelationId |-> item.correlationId]
            []OTHER -> aggs[a]]
/\ UNCHANGED <<dst, pool>>

LOCAL Send(id) == 
    /\ Len(aggs[id].Buffer) > 0
    /\ dst = NULL
    /\ dst' = aggs[id].Buffer
    /\ aggs' = [a \in pool \ {id} |-> aggs[a]]
    /\ pool' = pool \ {id}

LOCAL IncrementTime(id) ==
    /\ aggs' = [a \in DOMAIN aggs |-> 
                CASE aggs[a].Id = id -> [Id |-> aggs[a].Id, 
                                        Buffer |-> aggs[a].Buffer, 
                                        Time |-> aggs[a].Time + 1, 
                                        CorrelationId |-> aggs[a].CorrelationId]
                []OTHER -> aggs[a]]
    /\ UNCHANGED <<dst, pool>>

LOCAL AggregateInner(id) == /\ IF aggs[id].Time >= TimeOut
                               THEN Send(id)
                               ELSE IncrementTime(id)

Aggregate == 
    /\ \E AggId \in pool : Len(aggs[AggId].Buffer) > 0
    /\ AggregateInner(CHOOSE a \in pool : Len(aggs[a].Buffer) > 0)
=============================================================================