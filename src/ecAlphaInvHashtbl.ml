(* -------------------------------------------------------------------- *)
(* Hash-table over formulas whose key equality is alpha-equivalence in a
   fixed hypotheses context.

   The hash is invariant under the renaming of bound variables: a bound
   occurrence is hashed by the de-Bruijn *level* of its binder (an
   integer, intrinsically stable) rather than by its name, so
   alpha-equivalent formulas hash equal. Free variables, operators and
   types are stable under alpha-renaming and are hashed as-is.

   The hash traverses the whole formula, but is memoized on the hash-cons
   tag ([f_tag]) of every subformula reached with no binder in scope: each
   distinct (shared) subformula is hashed once, so table lookups are O(1)
   amortized. Memoization is gated on an empty binder environment so a
   subformula's hash never depends on enclosing binders (under a binder it
   is recomputed). Collisions are resolved by [is_alpha_eq], with a
   physical-equality ([==]) fast path for the common case of re-looking-up
   the very same (shared) formula.

   The context [hyps] is needed only by the equality ([is_alpha_eq]
   compares program variables / xpaths / statements relative to its
   environment), so it is supplied at table creation rather than via a
   functor. *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcIdent

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
let combine = Why3.Hashcons.combine
let combine_list = Why3.Hashcons.combine_list (fun (h : int) -> h)

(* Full alpha-invariant hash, memoized on the hash-cons tag of every
   subformula reached with an empty binder environment ([e.depth = 0]):
   such a subformula's hash is context-independent, so memoizing on
   [f_tag] is sound and gives each shared subformula a single traversal.
   Under a binder the hash is recomputed (it then depends on de-Bruijn
   levels). *)
let hash_memo (memo : (int, int) Hashtbl.t) (f0 : form) : int =
  let rec hash (e : env) (f : form) : int =
    if e.depth = 0 then
      match Hashtbl.find_opt memo f.f_tag with
      | Some h -> h
      | None ->
        let h = node e f in
        Hashtbl.add memo f.f_tag h;
        h
    else node e f
  (* The result type is always folded in: it distinguishes e.g.
     [fun (x:bool)=>x] from [fun (x:int)=>x]. *)
  and node (e : env) (f : form) : int =
    combine (ty_hash f.f_ty)
    @@
    match f.f_node with
    | Fint i -> combine 0 (EcBigInt.hash i)
    | Flocal id ->
      (* Bound -> the binder's level (alpha-invariant); free -> the id. *)
      (match Mid.find_opt id e.bound with
       | Some lvl -> combine 1 lvl
       | None -> combine 2 (id_hash id))
    | Fpvar (pv, _m) ->
      (* The memory is alpha-bindable; ignore it, keep the variable. *)
      combine 3 (pv_hash pv)
    | Fglob (mp, _m) -> combine 4 (id_hash mp)
    | Fop (p, tys) ->
      combine 5 (combine_list (EcPath.p_hash p) (List.map ty_hash tys))
    | Fif (c, t, f) -> combine 6 (combine_list 0 [hash e c; hash e t; hash e f])
    | Fmatch (c, bs, ty) ->
      combine 7 (combine_list (ty_hash ty) (hash e c :: List.map (hash e) bs))
    | Fquant (qt, bd, f) ->
      let gtys = List.map (fun (_, gty) -> gty_hash gty) bd in
      let e = List.fold_left (fun e (id, _) -> bind_id e id) e bd in
      combine 8 (combine (qt_hash qt) (combine_list (hash e f) gtys))
    | Flet (lp, v, body) ->
      let hv = hash e v in
      let e, hlp =
        match lp with
        | LSymbol (id, ty) -> bind_id e id, ty_hash ty
        | LTuple ids ->
          ( List.fold_left (fun e (id, _) -> bind_id e id) e ids,
            combine_list 0 (List.map (fun (_, ty) -> ty_hash ty) ids) )
        | LRecord (p, ids) ->
          ( List.fold_left
              (fun e (id, _) ->
                match id with Some id -> bind_id e id | None -> e)
              e ids,
            combine_list (EcPath.p_hash p)
              (List.map (fun (_, ty) -> ty_hash ty) ids) )
      in
      combine 12 (combine hv (combine hlp (hash e body)))
    | Fapp (f, args) ->
      combine 9 (combine_list (hash e f) (List.map (hash e) args))
    | Ftuple comps -> combine 10 (combine_list 0 (List.map (hash e) comps))
    | Fproj (f, i) -> combine 11 (combine i (hash e f))
    (* Forms binding memories / containing statements never reach the
       circuit cache; a coarse kind-tag hash is enough (only coarsens). *)
    | FhoareF _ -> 101
    | FhoareS _ -> 102
    | FbdHoareF _ -> 103
    | FbdHoareS _ -> 104
    | FeHoareF _ -> 105
    | FeHoareS _ -> 106
    | FequivF _ -> 107
    | FequivS _ -> 108
    | FeagerF _ -> 109
    | Fpr _ -> 110
  in
  hash empty_env f0

let hash (f : form) : int = hash_memo (Hashtbl.create 0) f

(* -------------------------------------------------------------------- *)
(* A formula-keyed table. Entries are bucketed by [hash]; within a bucket
   the alpha-equivalence [is_alpha_eq Ctxt.hyps] selects the matching
   key. *)
type 'a t = {
  hyps : EcEnv.LDecl.hyps;
  tbl  : (int, (form * 'a) list) Hashtbl.t;
  memo : (int, int) Hashtbl.t;       (* f_tag -> alpha-invariant hash *)
}

let create (hyps : EcEnv.LDecl.hyps) (size : int) : 'a t =
  { hyps; tbl = Hashtbl.create size; memo = Hashtbl.create size }

let clear (t : 'a t) : unit =
  Hashtbl.clear t.tbl;
  Hashtbl.clear t.memo

let find_opt (t : 'a t) (f : form) : 'a option =
  match Hashtbl.find_opt t.tbl (hash_memo t.memo f) with
  | None        -> None
  | Some bucket ->
    match
      List.find_opt
        (fun (g, _) -> f_equal f g || EcReduction.is_alpha_eq t.hyps f g)
        bucket
    with
    | None        -> None
    | Some (_, v) -> Some v

let add (t : 'a t) (f : form) (v : 'a) : unit =
  let h = hash_memo t.memo f in
  let bucket = odfl [] (Hashtbl.find_opt t.tbl h) in
  Hashtbl.replace t.tbl h ((f, v) :: bucket)
