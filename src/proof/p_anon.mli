(*
 * proof/anon.mli --- anonymise proofs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Anonymize proofs *)

class anon : object
  inherit [string list] P_visit.map
  method find_name : Expr.T.ctx -> string -> (int * Expr.T.hyp) option
  method has_name : Expr.T.ctx -> string -> bool
end
val anon : anon
