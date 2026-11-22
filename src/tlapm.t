Test the --stdin option
  $ cat <<EOF | (tlapm --toolbox 0 0 --stdin A.tla 2>&1 | grep -e '^@!!' | grep -v 'time-used')
  > ---- MODULE A ----
  > THEOREM
  >   ASSUME
  >      NEW A,
  >      NEW B,
  >      A,
  >      A => B
  >   PROVE B
  >   OBVIOUS
  > ====
  > EOF
  @!!BEGIN
  @!!type:obligation
  @!!id:1
  @!!loc:9:3:9:10
  @!!status:to be proved
  @!!END
  @!!BEGIN
  @!!type:obligationsnumber
  @!!count:1
  @!!END
  @!!BEGIN
  @!!type:obligation
  @!!id:1
  @!!loc:9:3:9:10
  @!!status:proved
  @!!prover:smt
  @!!already:false
  @!!END

Check if an understandable error is reported if an operator is called with wrong number of arguments.
  $ cat <<EOF | (tlapm --stdin test_bad_op.tla 2>&1 | grep -e '^File' -e '^Error')
  > ---- MODULE test_bad_op ----
  > Op(x) == TRUE
  > Po == Op({}, {})
  > THEOREM Po OBVIOUS
  > ====
  > EOF
  File "test_bad_op.tla", line 3, characters 7-16:
  Error: Invalid number of arguments

Compact Toolbox output retains the normalized attempt and terminal status.
  $ cat > Compact.tla <<'EOF'
  > ---- MODULE Compact ----
  > CONSTANT x
  > THEOREM x = x OBVIOUS
  > ====
  > EOF
  $ tlapm --strict --nofp --threads 1 --method smt --toolbox-compact Compact.tla </dev/null >stdout 2>stderr
  $ grep -E '^@!!(status|obl):' stderr
  @!!status:to be proved
  @!!obl:
  @!!status:normalized
  @!!obl:
  @!!status:proved
  @!!obl:
  $ grep -F 'All 1 obligation proved' stderr
  [INFO]: All 1 obligation proved.

A definition can instantiate an inner module before any theorem in its scope.
  $ cat > LocalInstance.tla <<'EOF'
  > ---- MODULE LocalInstance ----
  > ---- MODULE Inner ----
  > A == TRUE
  > THEOREM TRUE OBVIOUS
  > ====
  > ViaLet == LET M == INSTANCE Inner IN M!A
  > THEOREM ViaLet BY DEF ViaLet
  > ====
  > EOF
  $ tlapm --strict --nofp --threads 1 LocalInstance.tla >stdout 2>stderr
  $ grep -F 'All 2 obligations proved' stderr
  [INFO]: All 2 obligations proved.
