----------------------------- MODULE NodeManager -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS NULL, TimeOut, AggregatorsPool
VARIABLES src, dst

Aggregator(AggId) == INSTANCE Aggregator WITH src <- NULL, 
                                                dst <- dst, 
                                                time <- 0, 
                                                buffer <- <<>>, 
                                                correlationId <- NULL

AggregatorWithCorr(AggId, correlationId) == INSTANCE Aggregator WITH src <- NULL, 
                                                                        dst <- dst, 
                                                                        time <- 0, 
                                                                        buffer <- <<>>

NewAggregator(id, msg, end, t, buf, cid) == INSTANCE Aggregator WITH AggId <- id,
                                                                     src <- msg, 
                                                                     dst <- end, 
                                                                     time <- t, 
                                                                     buffer <- buf, 
                                                                     correlationId <- cid

RouteMessage == /\ src /= NULL
                /\ Cardinality(AggregatorsPool) > 0
                /\ src.correlationId /= NULL
                /\ src.content /= NULL
                /\ IF \E a \in AggregatorsPool : Aggregator(a)!GetCorrelationId = src.correlationId
                   THEN LET Agg == CHOOSE a \in AggregatorsPool : Aggregator(a)!GetCorrelationId = src.correlationId 
                        IN Aggregator(Agg)!AddToSource(src.content)
                   ELSE LET Agg == CHOOSE a \in AggregatorsPool : Aggregator(a)!GetCorrelationId = NULL IN
                            \* /\ Aggregator(Agg)!SetCorrelationId(src.correlationId)
                            \* /\ AggregatorWithCorr(Agg, src.correlationId)!AddToSource(src.content)
                            /\ NewAggregator(Agg, src.content, dst, 0, <<>>, src.correlationId)!Aggregate
                            /\ Print(<<Aggregator(Agg)!GetCorrelationId>>, TRUE)
                
                 
Next == \/ /\ RouteMessage /\ UNCHANGED dst
        \/ /\ \E Agg \in AggregatorsPool : Aggregator(Agg)!Aggregate /\ UNCHANGED src
=============================================================================