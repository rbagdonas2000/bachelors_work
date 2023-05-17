------------------------ MODULE Channel ------------------------
EXTENDS Naturals, Sequences
CONSTANTS NULL, src
VARIABLE endpts

Send(dst) == 
/\ endpts[src] /= NULL
/\ endpts' = [e \in DOMAIN endpts |-> 
              CASE e = src -> NULL
              []e = dst /\ dst \in Nat -> Append(endpts[dst], endpts[src])
              []e = dst /\ dst \notin Nat /\ endpts[dst] = NULL-> endpts[src]
              []OTHER -> endpts[e]]
=============================================================================