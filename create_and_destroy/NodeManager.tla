----------------------------- MODULE NodeManager -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS NULL, TimeOut, MaxInstances
VARIABLES src, dst, aggs, pool, versionCounter

Aggregators == INSTANCE Aggregator

LOCAL InitializeAggregator(id, correlationId) == 
    aggs' = [a \in pool \cup {id} |-> 
                CASE a \in DOMAIN aggs -> [Id |-> aggs[a].Id, 
                                           Buffer |-> aggs[a].Buffer, 
                                           Time |-> aggs[a].Time, 
                                           CorrelationId |-> aggs[a].CorrelationId]
                []OTHER -> [Id |-> id, 
                            Buffer |-> <<>>, 
                            Time |-> 0, 
                            CorrelationId |-> correlationId]]

RouteMessage == 
    /\ src /= NULL
    /\ src.correlationId /= NULL
    /\ src.content /= NULL
    /\ Cardinality(pool) < MaxInstances
    /\ IF \E a \in pool : aggs[a].CorrelationId = src.correlationId
        THEN /\ Aggregators!ProcessMessage(CHOOSE a \in pool : aggs[a].CorrelationId = src.correlationId, src)
             /\ src' = NULL
             /\ UNCHANGED versionCounter
        ELSE /\ LET newAggId == versionCounter 
                IN /\ pool' = pool \cup {newAggId}
                   /\ InitializeAggregator(newAggId, src.correlationId) 
             /\ versionCounter' = versionCounter + 1
             /\ UNCHANGED src
                
                 
Next == 
    \/ /\ RouteMessage /\ UNCHANGED dst
    \/ /\ \E AggId \in pool : Len(aggs[AggId].Buffer) > 0
       /\ Aggregators!Aggregate(CHOOSE a \in pool : Len(aggs[a].Buffer) > 0)
       /\ UNCHANGED <<src, versionCounter>>
=============================================================================