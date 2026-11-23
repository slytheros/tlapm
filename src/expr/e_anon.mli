(*
 * expr/anon.mli --- expressions (anonymization)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open E_t

val hyp_is_named: string -> hyp -> bool

class anon: object
  inherit [string list] E_visit.map
  method find_name : ctx -> string -> (int * hyp) option
  method has_name : ctx -> string -> bool
end

val anon: anon
