----------------------------- MODULE NodeManager -----------------------------
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS NULL, TimeOut, AggregatorsPool
VARIABLES src, dst, aggs

Aggregators == INSTANCE Aggregator

RouteMessage == 
/\ src /= NULL
/\ src.correlationId /= NULL
/\ src.content /= NULL
/\ Cardinality(AggregatorsPool) > 0
/\ IF \E a \in AggregatorsPool : aggs[a].CorrelationId = src.correlationId
   THEN Aggregators!ProcessMessage(CHOOSE a \in AggregatorsPool : 
                                            aggs[a].CorrelationId = src.correlationId, src)
   ELSE Aggregators!ProcessMessage(CHOOSE a \in AggregatorsPool : 
                                            aggs[a].CorrelationId = NULL, src)
/\ src' = NULL
                
                 
Next == 
    \/ /\ RouteMessage 
       /\ UNCHANGED dst
    \/ /\ Aggregators!Aggregate
       /\ UNCHANGED src
=============================================================================