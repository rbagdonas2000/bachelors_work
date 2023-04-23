----------------------------- MODULE NodeManager -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS NULL, TimeOut, AggregatorsPool
VARIABLES src, dst

Aggregator(AggId) == INSTANCE Aggregator WITH src <- NULL, 
                                                dst <- dst, 
                                                time <- 0, 
                                                buffer <- <<>>, 
                                                correlationId <- NULL

RouteMessage == /\ src /= NULL
                /\ Cardinality(AggregatorsPool) > 0
                /\ src.correlationId /= NULL
                /\ src.content /= NULL
                /\ IF \E a \in AggregatorsPool : Aggregator(a)!GetCorrelationId = src.correlationId
                   THEN LET Agg == CHOOSE a \in AggregatorsPool : Aggregator(a)!GetCorrelationId = src.correlationId 
                        IN Aggregator(Agg)!AddToSource(src.content)
                   ELSE LET Agg == CHOOSE a \in AggregatorsPool : /\ Aggregator(a)!GetCorrelationId = NULL IN
                            /\ Aggregator(Agg)!Init 
                            /\ Aggregator(Agg)!SetCorrelationId(src.correlationId)
                            /\ Aggregator(Agg)!AddToSource(src.content)
                            /\ Print(<<Aggregator(Agg)!GetCorrelationId>>, TRUE)
                
                 
Next == \/ /\ RouteMessage /\ UNCHANGED dst
        \/ /\ \E Agg \in AggregatorsPool : Aggregator(Agg)!Aggregate /\ UNCHANGED src
=============================================================================