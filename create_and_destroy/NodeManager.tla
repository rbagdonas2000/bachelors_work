----------------------------- MODULE NodeManager -----------------------------
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS NULL, TimeOut, MaxInstances
VARIABLES src, dst, aggs, pool, versionCounter

Aggregators == INSTANCE Aggregator

LOCAL InitializeAggregator(id, item) == 
    aggs' = [a \in pool \cup {id} |-> 
                CASE a = id -> [Id |-> id, 
                                Buffer |-> <<item.content>>, 
                                Time |-> 0, 
                                CorrelationId |-> item.correlationId]
                []OTHER -> aggs[a]]

RouteMessage == 
/\ src /= NULL
/\ src.correlationId /= NULL
/\ src.content /= NULL
/\ IF \E a \in pool : aggs[a].CorrelationId = src.correlationId
    THEN /\ Aggregators!ProcessMessage(CHOOSE a \in pool : 
                                    aggs[a].CorrelationId = src.correlationId, src)
         /\ src' = NULL
         /\ UNCHANGED versionCounter
    ELSE /\ Cardinality(pool) < MaxInstances
         /\ LET newAggId == versionCounter 
            IN /\ pool' = pool \cup {newAggId}
               /\ InitializeAggregator(newAggId, src) 
         /\ versionCounter' = versionCounter + 1
         /\ src' = NULL
                
                 
Next == 
    \/ /\ RouteMessage 
       /\ UNCHANGED dst
    \/ /\ Aggregators!Aggregate
       /\ UNCHANGED <<src, versionCounter>>
=============================================================================