(* -------------------------------------------------------------------- *)
(* Hash-table over formulas whose key equality is alpha-equivalence in a
   fixed hypotheses context.

   The hash is invariant under the renaming of bound variables: a bound
   occurrence is hashed by the de-Bruijn *level* of its binder (an
   integer, intrinsically stable) rather than by its name, so
   alpha-equivalent formulas hash equal. Free variables, operators and
   types are stable under alpha-renaming and are hashed as-is.

   Like [Hashtbl.hash] (= [Hashtbl.hash_param 10 100]) the traversal is
   *bounded*: it folds at most [nmeaningful] leaves and visits at most
   [nnodes] nodes, so hashing is O(1) on arbitrarily large formulas. A
   bounded hash only ever *coarsens* (it never distinguishes alpha-equal
   forms); collisions are resolved by [is_alpha_eq].

   The context [hyps] is needed only by the equality ([is_alpha_eq]
   compares program variables / xpaths / statements relative to its
   environment), so it is supplied at table creation rather than via a
   functor. *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcIdent

(* -------------------------------------------------------------------- *)
(* Same budget as [Hashtbl.hash]. *)
let nmeaningful = 10
let nnodes      = 100

(* -------------------------------------------------------------------- *)
(* [bound] maps each in-scope bound variable to the de-Bruijn level of
   its binder; [depth] is the number of binders entered so far (the level
   to assign to the next one). *)
type env = {
  depth : int;
  bound : int Mid.t;
}

let empty_env : env = { depth = 0; bound = Mid.empty }

let bind_id (e : env) (id : ident) : env =
  { depth = e.depth + 1; bound = Mid.add id e.depth e.bound }

(* -------------------------------------------------------------------- *)
let hash (f0 : form) : int =
  (* Mutable budget, mirroring [Hashtbl.hash_param]. *)
  let nmeaningful = ref nmeaningful in
  let nnodes      = ref nnodes      in

  let acc = ref 0 in
  let combine (h : int) = acc := Why3.Hashcons.combine !acc h in

  (* Fold a "meaningful" leaf, respecting the [nmeaningful] budget. *)
  let leaf (h : int) =
    if !nmeaningful > 0 then begin
      decr nmeaningful; combine h
    end
  in

  let rec hash (e : env) (f : form) : unit =
    if !nnodes <= 0 || !nmeaningful <= 0 then () else begin
      decr nnodes;
      (* The result type is always (cheaply) folded in: it distinguishes
         e.g. [fun (x:bool)=>x] from [fun (x:int)=>x]. *)
      leaf (ty_hash f.f_ty);
      match f.f_node with
      | Fint i ->
        leaf (EcBigInt.hash i)

      | Flocal id ->
        (* Bound -> hash the binder's level (alpha-invariant);
           free -> hash the identifier. *)
        leaf (match Mid.find_opt id e.bound with
              | Some lvl -> Why3.Hashcons.combine 1 lvl
              | None     -> Why3.Hashcons.combine 2 (id_hash id))

      | Fpvar (pv, _m) ->
        (* The memory is alpha-bindable; ignore it, keep the variable. *)
        leaf (pv_hash pv)

      | Fglob (mp, _m) ->
        leaf (id_hash mp)

      | Fop (p, tys) ->
        leaf (EcPath.p_hash p);
        List.iter (fun ty -> leaf (ty_hash ty)) tys

      | Fif (c, t, f) ->
        hash e c; hash e t; hash e f

      | Fmatch (c, bs, ty) ->
        leaf (ty_hash ty);
        hash e c; List.iter (hash e) bs

      | Fquant (qt, bd, f) ->
        leaf (qt_hash qt);
        let e =
          List.fold_left (fun e (id, gty) ->
            leaf (gty_hash gty); bind_id e id) e bd
        in hash e f

      | Flet (lp, v, body) ->
        hash e v;
        let e =
          match lp with
          | LSymbol (id, ty)   -> leaf (ty_hash ty); bind_id e id
          | LTuple  ids        ->
            List.fold_left
              (fun e (id, ty) -> leaf (ty_hash ty); bind_id e id) e ids
          | LRecord (p, ids)   ->
            leaf (EcPath.p_hash p);
            List.fold_left (fun e (id, ty) ->
              leaf (ty_hash ty);
              match id with Some id -> bind_id e id | None -> e) e ids
        in hash e body

      | Fapp (f, args) ->
        hash e f; List.iter (hash e) args

      | Ftuple comps ->
        List.iter (hash e) comps

      | Fproj (f, i) ->
        leaf i; hash e f

      (* Forms binding memories / containing statements. These never
         reach the circuit cache (circuit translation rejects them), so a
         coarse, memory-invariant hash on the kind + result type is
         enough: it is trivially consistent with [is_alpha_eq] (it can
         only coarsen) and avoids canonicalizing memories and hashing
         statements. *)
      | FhoareF   _ -> leaf 101
      | FhoareS   _ -> leaf 102
      | FbdHoareF _ -> leaf 103
      | FbdHoareS _ -> leaf 104
      | FeHoareF  _ -> leaf 105
      | FeHoareS  _ -> leaf 106
      | FequivF   _ -> leaf 107
      | FequivS   _ -> leaf 108
      | FeagerF   _ -> leaf 109
      | Fpr       _ -> leaf 110
    end
  in

  hash empty_env f0;
  !acc

(* -------------------------------------------------------------------- *)
(* A formula-keyed table. Entries are bucketed by [hash]; within a bucket
   the alpha-equivalence [is_alpha_eq Ctxt.hyps] selects the matching
   key. *)
type 'a t = {
  hyps : EcEnv.LDecl.hyps;
  tbl  : (int, (form * 'a) list) Hashtbl.t;
}

let create (hyps : EcEnv.LDecl.hyps) (size : int) : 'a t =
  { hyps; tbl = Hashtbl.create size }

let clear (t : 'a t) : unit =
  Hashtbl.clear t.tbl

let find_opt (t : 'a t) (f : form) : 'a option =
  match Hashtbl.find_opt t.tbl (hash f) with
  | None        -> None
  | Some bucket ->
    match List.find_opt (fun (g, _) -> EcReduction.is_alpha_eq t.hyps f g) bucket with
    | None        -> None
    | Some (_, v) -> Some v

let add (t : 'a t) (f : form) (v : 'a) : unit =
  let h = hash f in
  let bucket = odfl [] (Hashtbl.find_opt t.tbl h) in
  Hashtbl.replace t.tbl h ((f, v) :: bucket)
