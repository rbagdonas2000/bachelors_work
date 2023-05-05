------ MODULE RandomHash ------
EXTENDS Naturals, Sequences
CONSTANT Seed, Prime, Modulus

(* Seed the random number generator *)
rand == CHOOSE x \in 1..Modulus-1: TRUE

(* Hash function *)
RandomHash(s) == 
  LET 
    n == Len(s)
    h == rand
  IN
    IF n = 0 THEN h
    ELSE
      LET
        x == 0
        i == 1
      IN
        WHILE i <= n 
          DO 
            x == (x * Prime + s[i]) % Modulus
            i == i + 1
        END
      IN
        (h + x) % Modulus

=============================================================================