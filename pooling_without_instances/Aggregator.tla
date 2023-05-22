----------------------------- MODULE Aggregator -----------------------------
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS NULL, TimeOut
VARIABLES aggs, dst
        
ProcessMessage(id, item) == 
    /\ aggs[id].Time < TimeOut
    /\ aggs' = [a \in DOMAIN aggs |-> 
                CASE aggs[a].Id = id -> [Id |-> id, 
                                        Buffer |-> Append(aggs[a].Buffer, item.content), 
                                        Time |-> aggs[a].Time + 1, 
                                        CorrelationId |-> item.correlationId]
                []OTHER -> aggs[a]]
    /\ UNCHANGED dst

Send(id) == 
    /\ Len(aggs[id].Buffer) > 0
    /\ dst = NULL
    /\ dst' = aggs[id].Buffer
    /\ aggs' = [a \in DOMAIN aggs |-> 
                CASE aggs[a].Id = id -> [Id |-> aggs[a].Id, 
                                        Buffer |-> <<>>, 
                                        Time |-> 0, 
                                        CorrelationId |-> NULL]
                []OTHER -> aggs[a]]

IncrementTime(id) ==
    /\ aggs' = [a \in DOMAIN aggs |-> 
                CASE aggs[a].Id = id -> [Id |-> aggs[a].Id, 
                                        Buffer |-> aggs[a].Buffer, 
                                        Time |-> aggs[a].Time + 1, 
                                        CorrelationId |-> aggs[a].CorrelationId]
                []OTHER -> aggs[a]]
    /\ UNCHANGED dst

AggregateInner(id) == IF aggs[id].Time >= TimeOut
                            THEN Send(id)
                            ELSE IncrementTime(id)
                           
                    
Aggregate == /\ \E AggId \in DOMAIN aggs : Len(aggs[AggId].Buffer) > 0
             /\ AggregateInner(CHOOSE a \in DOMAIN aggs : Len(aggs[a].Buffer) > 0)
=============================================================================