------------- MODULE ambiguous_precedence_test --------------

EXTENDS TLAPS

\* The explicitly grouped assumption is true, so this theorem is false.
THEOREM
  ASSUME {} \notin ((SUBSET {}) \cap {})
  PROVE FALSE
BY SMT

=============================================================
result: 0
stderr: @!!status:failed
nostderr: @!!status:proved
