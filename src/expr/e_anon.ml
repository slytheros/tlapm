(* Conversion of identifiers to De Bruijn indices.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Property
open E_t
open E_subst

module Elab = E_elab
module Visit = E_visit
module Deref = E_deref
module Eq = E_eq


let ( |> ) x f = f x


(* see also `Expr.T.hyp_name` *)
exception Unresolved_tuple

let name_of_hyp h = match h.core with
    | Fresh (nm, _, _, _)
    | Flex nm
    | Defn ({core =
              Operator (nm, _)
            | Instance (nm, _)
            | Bpragma(nm,_,_)
            | Recursive (nm, _)},
            _, _, _) ->
        Some nm.core
    | Fact (_, _, _) -> None
    | FreshTuply _ -> raise Unresolved_tuple

let hyp_is_named what h =
  match name_of_hyp h with
  | Some name -> name = what
  | None -> false
  | exception Unresolved_tuple -> assert false

module Names = Map.Make (String)

let rec remove_newer prefix cx names =
  if Deque.size cx = prefix then names
  else match Deque.rear cx with
    | None -> assert false
    | Some (cx, hyp) ->
        let names = match name_of_hyp hyp with
          | None -> names
          | Some name ->
              Names.update name (function
                | Some (_ :: (_ :: _ as older)) -> Some older
                | _ -> None) names
        in
        remove_newer prefix cx names

let add_newer prefix cx names =
  let add (depth, names) hyp =
    let names = match name_of_hyp hyp with
      | None -> names
      | Some name ->
          Names.update name (fun previous ->
              Some ((depth, hyp) :: Option.value ~default:[] previous)) names
    in
    (depth + 1, names)
  in
  if prefix = 0 then snd (Deque.fold_left add (0, names) cx)
  else
    let rec collect cx newer =
      if Deque.size cx = prefix then newer
      else match Deque.rear cx with
        | None -> assert false
        | Some (cx, hyp) -> collect cx (hyp :: newer)
    in
    snd (List.fold_left add (prefix, names) (collect cx []))


let anon_apply index op args =
    let ix = Ix index @@ op in
    match args with
    | [] -> ix
    | _ -> Apply (ix, args) @@ op


let standard_form
        ~cx ~index ~wd op args =
    match wd with
    | Builtin -> begin
        let ix = app_expr
            (shift index) op in
        match args with
        | [] -> ix.core @@ op
        | _ ->
            let e = normalize
                ~cx:cx ix args in
            e @@ op
        end
    | _ ->
        anon_apply index op args


class anon_sg = object (self: 'self)
  inherit [string list] Visit.map
        as super

  (* Proof scopes often reuse a long module prefix. Track only the bindings in
     the last context, rolling back shadowing when moving to a sibling scope. *)
  val mutable indexed_cx = Deque.empty
  val mutable names = Names.empty

  method private indexed_name cx name =
    if cx != indexed_cx then begin
      let prefix = Deque.shared_prefix_length indexed_cx cx in
      let shared_names =
        if prefix = 0 then Names.empty else remove_newer prefix indexed_cx names
      in
      names <- add_newer prefix cx shared_names;
      indexed_cx <- cx
    end;
    match Names.find_opt name names with
    | Some ((depth, hyp) :: _) -> Some (Deque.size cx - depth - 1, hyp)
    | _ -> None

  method find_name cx name =
    try self#indexed_name cx name
    with Unresolved_tuple ->
      Deque.find ~backwards:true cx (hyp_is_named name)

  method has_name cx name =
    try Option.is_some (self#indexed_name cx name)
    with Unresolved_tuple ->
      Option.is_some (Deque.find cx (hyp_is_named name))

  method expr scx e =
    match e.core with
    | Bang (
            {core=Apply (
                {core = Opaque op},
                args)},
            sels) -> begin
        let sels = List.map
            (self#sel scx) sels in
        let args = List.map
            (self#expr scx) args in
        let scx = ([], snd scx) in
        (* check the operator without the
        "use <1>1 in proof of <1>1" warning *)
        let rec check
                (pfx, pargs)
                sels
                is_inst =
            begin
            let hyp = self#find_name (snd scx) pfx in
            match hyp with
            | None -> begin
                match sels with
                | Sel_lab (sfx, sargs) :: sels ->
                    let sargs = List.map
                        (self#expr scx) sargs in
                    check
                        (pfx ^ "!" ^ sfx,
                         pargs @ sargs)
                        sels true
                (* a enlever *)
                | (Sel_num n) :: sels ->
                    Util.eprintf ~at:e
                        "Operator \"%s\" not found" pfx;
                    Errors.set
                        e (Printf.sprintf
                            "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1NUM"
                | (Sel_down) :: sels ->
                    Util.eprintf ~at:e
                        "Operator \"%s\" not found" pfx;
                    Errors.set
                        e (Printf.sprintf
                            "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1DOWN"
                | (Sel_at) :: sels ->
                    Util.eprintf ~at:e
                        "Operator \"%s\" not found" pfx;
                    Errors.set
                        e (Printf.sprintf
                            "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1AT"
                | (Sel_inst _) :: sels ->
                    Util.eprintf ~at:e
                        "Operator \"%s\" not found" pfx;
                    Errors.set
                        e (Printf.sprintf
                            "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1INST"
                | [] ->
                    Errors.set
                        e (Printf.sprintf
                            "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1EMPTY"
                | _ ->
                    Util.eprintf ~at:e
                        "Operator \"%s\" not found" pfx;
                    Errors.set
                        e (Printf.sprintf
                            "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1"
              end
            | Some (dep,
                    {core=Defn ({core=(
                        Operator (_, op)
                        | Bpragma (_, op, _)
                    )}, wd, _, _)}) ->
                begin match sels with
                  | [] when is_inst -> begin
                      let ix = Ix (dep + 1) @@ e in
                      match pargs with
                        | [] -> ix
                        | pargs ->
                            standard_form ~cx:(snd scx) ~index:(dep + 1) ~wd:wd
                              (op.core @@ e) pargs
                    end
                  | _ -> begin
                      let op = app_expr (shift (dep + 1)) op in
                      let op = Util.set_locus op (Util.get_locus e) in
                      let se = Deref.resolve_bang (snd scx) op pargs sels in
                      if Deref.is_badexp se then begin
                        Util.eprintf ~at:e "Could not resolve subexpression reference" ;
                        Errors.set e (Printf.sprintf "Could not resolve subexpression reference");
                        failwith "Expr.Anon: 2"
                      end ;
                      Util.set_locus se (Util.get_locus e)
                    end
                end
            | Some _ ->
                let cx = snd scx in
                let expr_str = E_fmt.string_of_expr cx e in
                Util.eprintf ~at:e "%s"
                    ("invalid subexpression reference in:  " ^ expr_str) ;
                 Errors.set e (Printf.sprintf "invalid subexpression reference");
                 failwith "Expr.Anon: 3"
        end in
        check (op, args) sels false
      end
    | Bang (b, sels) ->
        self#expr scx (Bang (Apply (b, []) @@ b, sels) @@ e)
    | Apply ({core = Opaque name}, args) ->
      begin
        if List.mem name (fst scx) then
            begin
                Errors.err ~at:e
                    "Warning: %s does not introduce any assumptions. \
                     It does not make sense to use it here.\n" name;
                Internal (Builtin.TRUE) @@ e
            end
        else
            begin
                let args = List.map (self#expr scx) args in
                let cx = snd scx in
                let pair = self#find_name cx name in
                match pair with  (* Replace operator application with the
                    de Bruijn index of the operator.
                    Defined operators are not expanded. *)

                    (* defined or builtin operator *)
                    | Some (depth, {core=Defn (defn, wd, _, _)}) ->
                        begin
                        match defn.core with
                        | Operator (_, op) ->
                            let cx = snd scx in
                            (* An increment by 1 is needed
                            to convert the 0-based depth to
                            a 1-based De Bruijn index.
                            *)
                            let index = depth + 1 in
                            let op = op.core @@ e $$ defn in
                            (* does not expand defined operators *)
                            standard_form
                                ~cx:cx ~index:index ~wd:wd op args
                        | Instance _
                        | Bpragma _ ->
                            let index = depth + 1 in
                            let op = e $$ defn in
                            anon_apply index op args
                        | Recursive _ ->
                            Errors.set defn "Recursive operators not supported by TLAPS";
                            failwith "Expr.Anon: Recursive"
                        end
                    (* declared operator *)
                    | Some (depth, ({core=Fresh _} as decl)) ->
                        let index = depth + 1 in
                        let op = e $$ decl in
                        anon_apply index op args
                    | Some (depth, ({core=Flex _} as decl)) ->
                        assert ((List.length args) = 0);
                        let index = depth + 1 in
                        let op = e $$ decl in
                        Ix index @@ op
                    (* unexpected cases *)
                    | Some (_, {core=Fact _ | FreshTuply _}) ->
                        assert false
                    | None ->
                         (* TODO? allow builtin operators here ?
                         possibly passing a context with builtin operators
                         present as the starting context. *)
                         Util.eprintf ~at:e "Operator \"%s\" not found" name ;
                         Errors.set e (Printf.sprintf "Operator \"%s\" not found" name);
                         failwith "Expr.Anon: 4"
            end
      end
    | Opaque _ -> self#expr scx (Apply (e, []) @@ e)
        (* remove parentheses that appear in the source text *)
    | Parens (e, {core = Syntax}) -> self#expr scx e
    | _ -> super#expr scx e

  method hyp scx h = match h.core with
    | Fact (e, vis, NotSet) ->
      let adj (s, cx) h =
        (s, Deque.snoc cx h) in
        let e = self#expr scx e in
        let h = Fact (e, vis, E_temporal_props.compute_time (snd scx) e) @@ h in
        (adj scx h, h)
    | Fact (e, vis, ts) ->
      let adj (s, cx) h =
        (s, Deque.snoc cx h) in
        let e = self#expr scx e in
        let h = Fact (e, vis, ts) @@ h in
        (adj scx h, h)
    | _ -> super#hyp scx h

  method pform scx pf = match pf.core with
    | Nlabel (l, ns) ->
        let xs = List.map begin
          fun n -> match self#find_name (snd scx) n.core with
            | None ->
                Util.eprintf ~at:pf "Identifier \"%s\" in label parameters not found" n.core ;
                Errors.set pf (Printf.sprintf "Identifier \"%s\" in label parameters not found" n.core);
              failwith "Expr.Anon"
            | Some (dep, _) ->
                (n, dep + 1)
        end ns in
        Xlabel (l, xs) @@ pf
    | _ -> super#pform scx pf

  method defn scx df = match df.core with
    | Operator (nm, op) ->
        let op = match op.core with
          | Fcn _ ->
              let nscx = Visit.adj scx (Fresh (nm, Shape_expr, Constant, Unbounded) @@ nm) in
              let op = self#expr nscx op in
              let mk x = { op with core = x } in
              let occurs op =
                let op' = (app_expr (scons (Opaque "%%%" |> mk) (shift 1)) op) in
                not (Eq.expr op' op)
              in
                if occurs op then begin
                    let e = Apply (Internal Builtin.Eq |> mk, [
                             Ix 1 |> mk ;
                             op
                           ]) |> mk in
                    let choose = E_t.From_hint.make_choose nm e in
                    choose.core |> mk
                    end
                else
                  app_expr (shift (-1)) op

          | _ ->
              self#expr scx op
        in
        Operator (nm, op) @@ df
    | _ ->
        super#defn scx df
end


class anon = object (self : 'self)
  inherit anon_sg as super
  method expr scx e =
    E_levels.newcache (Elab.desugar self#expr super#expr scx e)
end


let anon = object
  inherit anon
  method! find_name cx name =
    Deque.find ~backwards:true cx (hyp_is_named name)
end

let%test_unit "indexed names restore shadowed bindings across proof scopes" =
  let fresh name = noprops (Fresh (noprops name, Shape_expr, Constant, Unbounded)) in
  let base_x = fresh "x" in
  let base = Deque.snoc (Deque.of_list [fresh "outer"]) base_x in
  let local_x = fresh "x" in
  let left = Deque.snoc (Deque.snoc base local_x)
      (noprops (Fact (noprops (Internal Builtin.TRUE), Visible, NotSet))) in
  let right = Deque.snoc (Deque.snoc base (fresh "y")) (fresh "z") in
  let visitor = new anon in
  assert (visitor#find_name left "x" = Some (1, local_x));
  assert (visitor#find_name right "x" = Some (2, base_x));
  assert (visitor#find_name base "y" = None);
  assert (visitor#find_name left "outer" = Some (3, Option.get (Deque.nth left 0)));
  assert (visitor#find_name (Deque.of_list (Deque.to_list left)) "x" = Some (1, local_x))
