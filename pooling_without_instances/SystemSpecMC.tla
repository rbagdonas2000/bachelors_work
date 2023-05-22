-------------------------------- MODULE SystemSpecMC --------------------------------
EXTENDS Naturals, Sequences

MessageRecord == [correlationId: STRING, content: STRING]

Msgs == <<[correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "This"],
          [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "is"],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "This"],
          [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "whole"],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "is"],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "another"],
          [correlationId |-> "nguenuhe39g4e8eg1e8", content |-> "message"],
          [correlationId |-> "nguenuhe39g4e8eg1e7", content |-> "message"]>>
        
=============================================================================