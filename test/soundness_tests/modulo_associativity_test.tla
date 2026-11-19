------------- MODULE modulo_associativity_test --------------

EXTENDS Naturals, TLAPS

\* The explicitly grouped assumption is true, so this theorem is false.
THEOREM
  ASSUME 5 % (4 % 3) = 0
  PROVE FALSE
BY SMT

=============================================================
result: 0
stderr: @!!status:failed
nostderr: @!!status:proved
