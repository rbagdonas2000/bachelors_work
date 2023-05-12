-------------------------------- MODULE SystemSpecMC --------------------------------
EXTENDS Naturals, Sequences, TLC

MessageRecord == [correlationId: STRING, content: STRING]

Msgs == <<[correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "data1", isFinal |-> FALSE],
          [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "data2", isFinal |-> FALSE],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "value1", isFinal |-> FALSE],
          [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "data3", isFinal |-> FALSE],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "value2", isFinal |-> FALSE],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "value3", isFinal |-> FALSE],
          [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "data4", isFinal |-> TRUE],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "value4", isFinal |-> TRUE]>>
        
=============================================================================