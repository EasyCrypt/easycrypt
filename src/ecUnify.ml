(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcMaps
open EcUtils
open EcUid
open EcAst
open EcTypes
open EcCoreSubst
open EcDecl

module Sp = EcPath.Sp
module TC = EcTypeClass

(* -------------------------------------------------------------------- *)
type pb = [ `TyUni of ty * ty | `IxUni of tindex * tindex ]

exception UnificationFailure of pb
exception UninstantiateUni

(* -------------------------------------------------------------------- *)
module UFArgs = struct
  module I = struct
    type t = uid

    let equal   = uid_equal
    let compare = uid_compare
  end

  module D = struct
    type data    = ty option
    type effects = pb list

    let default : data =
      None

    let isvoid (x : data) =
      Option.is_none x

    let noeffects : effects =
      []

    let union (d1 : data) (d2 : data) =
      match d1, d2 with
      | None, None ->
        (None, [])

      | Some ty1, Some ty2 ->
        (Some ty1, [`TyUni (ty1, ty2)])

      | None   , Some ty
      | Some ty, None ->
        (Some ty, [])
  end
end

module UF = EcUFind.Make(UFArgs.I)(UFArgs.D)

(* -------------------------------------------------------------------- *)
module UnifyCore = struct
  let fresh ?ty uf =
    let uid = EcUid.unique () in
    let uf  =
      match ty with
      | Some { ty_node = Tunivar id } ->
          let uf = UF.set uid None uf in
          fst (UF.union uid id uf)
      | None | Some _ -> UF.set uid ty uf
    in
      (uf, tuni uid)
end

(* -------------------------------------------------------------------- *)
type unienv_r = {
  ue_uf       : UF.t;
  ue_named    : EcIdent.t Mstr.t;
  ue_decl     : EcIdent.t list;
  ue_closed   : bool;
  (* Indices live in their own namespace, separate from type variables.
     They are always closed (declared up front, no on-demand creation). *)
  ue_idxnamed : EcIdent.t Mstr.t;
  ue_idxdecl  : EcIdent.t list;
  (* Index-univar machinery (Phase 3.5). [ue_iuf] holds assignments for
     resolved univars; [ue_iuf_alloc] tracks the set of all index uids
     ever allocated, so [close] can detect leftover unresolved ones. *)
  ue_iuf       : tindex Muid.t;
  ue_iuf_alloc : Suid.t;
}

type unienv = unienv_r ref

(* -------------------------------------------------------------------- *)
(* Index-univar helpers — defined at top level so [unify_core] can use
   them. All operate on a [unienv ref]. *)

let resolve_tindex (ue : unienv) : tindex -> tindex =
  let rec doit ti =
    match ti with
    | TIUnivar u -> begin
        match Muid.find_opt u (!ue).ue_iuf with
        | None    -> ti
        | Some ti -> doit ti
      end
    | TIVar _ | TIConst _ -> ti
    | TIAdd (l, r) ->
        let l' = doit l in
        let r' = doit r in
        if l == l' && r == r' then ti else TIAdd (l', r')
    | TIMul (l, r) ->
        let l' = doit l in
        let r' = doit r in
        if l == l' && r == r' then ti else TIMul (l', r')
  in doit

(* -------------------------------------------------------------------- *)
(* Failure is TRANSACTIONAL by default: on [UnificationFailure] the
   unienv is restored to its entry state (in-place mutation would
   otherwise leak partial type/index assignments into non-restoring
   failure paths, e.g. the matcher's MatchFailure handlers).
   [~transactional:false] deliberately KEEPS the partial assignments:
   the failure-classification path runs on a throwaway unienv and
   reads them back for diagnostics ("inferred as 'a = int"). *)
let unify_core ?(transactional = true) (env : EcEnv.env) (ue : unienv) (pb : pb) =
  let saved = !ue in
  let failure () = raise (UnificationFailure pb) in

  let pb_q = let x = Queue.create () in Queue.push pb x; x in
  let push p = Queue.push p pb_q in

  let get_uf  ()  = (!ue).ue_uf in
  let set_uf  u   = ue := { !ue with ue_uf  = u } in
  let upd_uf  f   = set_uf (f (get_uf ())) in

  let ocheck i t =
    let i   = UF.find i (get_uf ()) in
    let map = Hint.create 0 in

    let rec doit t =
      match t.ty_node with
      | Tunivar i' -> begin
          let i' = UF.find i' (get_uf ()) in
            match i' with
            | _ when i = i' -> true
            | _ when Hint.mem map i' -> false
            | _ ->
                match UF.data i' (get_uf ()) with
                | None   -> Hint.add map i' (); false
                | Some t ->
                  match doit t with
                  | true  -> true
                  | false -> Hint.add map i' (); false
      end

      | _ -> EcTypes.ty_sub_exists doit t
    in
      doit t
  in

  let setvar i t =
    let (ti, effects) = UFArgs.D.union (UF.data i (get_uf ())) (Some t) in
      if odfl false (ti |> omap (ocheck i)) then failure ();
      List.iter push effects;
      upd_uf (UF.set i ti)
  in

  let getvar t =
    match t.ty_node with
    | Tunivar i -> odfl t (UF.data i (get_uf ()))
    | _ -> t
  in

  (* Try to unify two indices. Resolves both sides through the current
     univar assignments, canonicalises, and compares. If equal, done.
     Otherwise hands off to [tindex_solve_for_univar], which solves any
     equation reducible to "one TIUnivar with coefficient ±1, residual
     non-negative". This subsumes the old "naked univar = polynomial"
     special case and additionally handles e.g. [?u + 1 = n + 5]. *)
  let unify_ix t1 t2 =
    let r1 = resolve_tindex ue t1 in
    let r2 = resolve_tindex ue t2 in
    if tindex_equal r1 r2 then () else
    let assign u t =
      ue := { !ue with ue_iuf = Muid.add u t (!ue).ue_iuf } in
    (* Fast path: if either side is a naked univar [?u] not occurring
       in the other, assign directly. This subsumes the case [?u = ?v]
       which [tindex_solve_for_univar] would refuse (it sees two
       univars with non-zero net coefficient). *)
    match tindex_naked_univar r1 with
    | Some u when not (tindex_occurs_univar u r2) -> assign u r2
    | _ ->
        match tindex_naked_univar r2 with
        | Some u when not (tindex_occurs_univar u r1) -> assign u r1
        | _ ->
            match tindex_solve_for_univar r1 r2 with
            | Some (u, v) when not (tindex_occurs_univar u v) ->
                assign u v
            | _ -> failure ()
  in

  (* Problems that [unify_ix] couldn't solve in the current state —
     typically because a dependent TIUnivar is still unresolved. They
     get retried after every successful assignment; we fail only when
     a full pass makes no progress. *)
  let deferred = ref [] in

  let try_unify_ix t1 t2 =
    try unify_ix t1 t2
    with UnificationFailure _ -> deferred := (t1, t2) :: !deferred
  in

  let rec drain_deferred () =
    let todo = !deferred in
    deferred := [];
    let progressed = ref false in
    List.iter (fun (t1, t2) ->
      let before = !deferred in
      (try
         unify_ix t1 t2;
         progressed := true
       with UnificationFailure _ ->
         deferred := (t1, t2) :: before)
    ) todo;
    if !progressed && !deferred <> [] then drain_deferred ()
  in

  let doit () =
    while not (Queue.is_empty pb_q) do
      match Queue.pop pb_q with
      | `IxUni (t1, t2) ->
          try_unify_ix t1 t2

      | `TyUni (t1, t2) -> begin
        let (t1, t2) = (getvar t1, getvar t2) in

        match ty_equal t1 t2 with
        | true  -> ()
        | false -> begin
            match t1.ty_node, t2.ty_node with
            | Tunivar id1, Tunivar id2 -> begin
                if not (uid_equal id1 id2) then
                  let effects =
                    let uf' = get_uf () in
                    let (uf'', effs) = UF.union id1 id2 uf' in
                    set_uf uf''; effs in
                  List.iter push effects
            end

            | Tunivar id, _ -> setvar id t2
            | _, Tunivar id -> setvar id t1

            | Ttuple lt1, Ttuple lt2 ->
                if List.length lt1 <> List.length lt2 then failure ();
                List.iter2 (fun t1 t2 -> push (`TyUni (t1, t2))) lt1 lt2

            | Tfun (t1, t2), Tfun (t1', t2') ->
                push (`TyUni (t1, t1'));
                push (`TyUni (t2, t2'))

            | Tconstr (p1, ta1), Tconstr (p2, ta2) when EcPath.p_equal p1 p2 ->
                if List.compare_lengths ta1.indices ta2.indices <> 0 then failure ();
                if List.compare_lengths ta1.types ta2.types <> 0 then failure ();
                List.iter2
                  (fun i1 i2 -> push (`IxUni (i1, i2)))
                  ta1.indices ta2.indices;
                List.iter2
                  (fun t1 t2 -> push (`TyUni (t1, t2)))
                  ta1.types ta2.types

            | Tconstr (p, lt), _ when EcEnv.Ty.defined p env ->
                push (`TyUni (EcEnv.Ty.unfold p lt env, t2))

            | _, Tconstr (p, lt) when EcEnv.Ty.defined p env ->
                push (`TyUni (t1, EcEnv.Ty.unfold p lt env))

            | _, _ -> failure ()
        end
      end
    done;
    (* After the primary queue drains, retry any [IxUni] problems
       that were deferred (typically because a dependent univar was
       not yet assigned). Each round either resolves at least one or
       fails the remaining. *)
    drain_deferred ();
    if !deferred <> [] then
      let (i1, i2) = List.hd !deferred in
      raise (UnificationFailure (`IxUni (i1, i2)))
  in
    try doit ()
    with UnificationFailure _ as e ->
      if transactional then ue := saved;
      raise e

(* -------------------------------------------------------------------- *)
let close (uf : UF.t) =
  let map = Hint.create 0 in

  let rec doit t =
    match t.ty_node with
    | Tunivar i -> begin
       match Hint.find_opt map i with
       | Some t -> t
       | None   -> begin
         let t =
           match UF.data i uf with
           | None   -> tuni (UF.find i uf)
           | Some t -> doit t
         in
           Hint.add map i t; t
       end
    end

    | _ -> ty_map doit t
  in
    fun t -> doit t



(* -------------------------------------------------------------------- *)
let subst_of_uf (uf : UF.t) =
  let close = close uf in
  let uids = UF.domain uf in
  List.fold_left
    (fun m uid ->
      match close (tuni uid) with
      | { ty_node = Tunivar uid' } when uid_equal uid uid' -> m
      | t -> Muid.add uid t m
    )
    Muid.empty
    uids


(* -------------------------------------------------------------------- *)
type idx_inst =
| IXunamed of tindex list
| IXnamed  of (EcSymbols.symbol * tindex) list

type tvar_inst =
(* Explicit indices first, then explicit types. Either may be empty;
   when both are empty, the slot is "no instantiation provided". The
   index side is independent of the named/positional choice made for
   the type side. *)
| TVIunamed of idx_inst * ty list
| TVInamed  of idx_inst * (EcSymbols.symbol * ty) list

type tvi = tvar_inst option

(* Raised by [opentvi] / [openidx] on an explicitly named parameter
   that matches no formal of the instantiated declaration. User-facing
   paths validate names beforehand (op selection filters candidates,
   [pf_check_tvi] checks lemma instantiation), so reaching this from
   the surface is a bug in the caller. *)
exception UnknownTypeVariable  of EcSymbols.symbol
exception UnknownIndexVariable of EcSymbols.symbol

let tvi_indices (tvi : tvar_inst option) : idx_inst =
  match tvi with
  | None -> IXunamed []
  | Some (TVIunamed (ix, _)) | Some (TVInamed (ix, _)) -> ix
type uidmap = uid -> ty option

module UniEnv = struct
  let copy (ue : unienv) : unienv =
    ref !ue

  let restore ~(dst:unienv) ~(src:unienv) =
    dst := !src

  let getnamed (ue : unienv) (x : symbol) =
      match Mstr.find_opt x (!ue).ue_named with
      | Some a -> a
      | None   -> begin
          if (!ue).ue_closed then raise Not_found;
          let id = EcIdent.create x in
            ue := { !ue with
              ue_named = Mstr.add x id (!ue).ue_named;
              ue_decl  = id :: (!ue).ue_decl;
            }; id
    end

  let create (vd : ty_params option) =
    let ue = {
      ue_uf        = UF.initial;
      ue_named     = Mstr.empty;
      ue_decl      = [];
      ue_closed    = false;
      ue_idxnamed  = Mstr.empty;
      ue_idxdecl   = [];
      ue_iuf       = Muid.empty;
      ue_iuf_alloc = Suid.empty;
    } in

    let ue =
      match vd with
      | None    -> ue
      | Some vd ->
          let tyvars = vd.tyvars in
          let vdmap  = List.map (fun x -> (EcIdent.name x, x)) tyvars in
          let imap   = List.map (fun x -> (EcIdent.name x, x)) vd.idxvars in
          { ue with
              ue_named    = Mstr.of_list vdmap;
              ue_decl     = List.rev tyvars;
              ue_closed   = true;
              ue_idxnamed = Mstr.of_list imap;
              ue_idxdecl  = List.rev vd.idxvars; }
    in
      ref ue

  (* Look up an index variable by name. Returns None if no such
     binding exists. Indices are always declared up front, so we never
     create one on demand. *)
  let getnamed_idx (ue : unienv) (x : symbol) : EcIdent.t option =
    Mstr.find_opt x (!ue).ue_idxnamed

  let fresh ?(ty : ty option) (ue : unienv) =
    let (uf, uid) = UnifyCore.fresh ?ty (!ue).ue_uf in
      ue := { !ue with ue_uf = uf }; uid

  (* Allocate a fresh index univar. Tracked in [ue_iuf_alloc] so that
     [close] can complain if it stays unresolved. *)
  let idx_fresh (ue : unienv) : tindex =
    let u = EcUid.unique () in
    ue := { !ue with ue_iuf_alloc = Suid.add u (!ue).ue_iuf_alloc };
    TIUnivar u

  let opentvi (ue : unienv) (params : ty_params) (tvi : tvar_inst option) =
    let params = params.tyvars in
    match tvi with
    | None ->
        List.fold_left
          (fun s v -> Mid.add v (fresh ue) s)
          Mid.empty params

    | Some (TVIunamed (_ix, lt)) ->
        (* _ix is handled by [openidx] separately. Here we only map
           tyvars to their explicit-or-fresh univars. *)
        if lt = [] then
          List.fold_left
            (fun s v -> Mid.add v (fresh ue) s)
            Mid.empty params
        else
          List.fold_left2
            (fun s v ty -> Mid.add v (fresh ~ty ue) s)
            Mid.empty params lt

    | Some (TVInamed (_ix, lt)) ->
        List.iter (fun (name, _) ->
          if not (List.exists (fun v -> EcIdent.name v = name) params) then
            raise (UnknownTypeVariable name))
          lt;
        let for1 s v =
          let t =
            try  fresh ~ty:(List.assoc (EcIdent.name v) lt) ue
            with Not_found -> fresh ue
          in
            Mid.add v t s
        in
          List.fold_left for1 Mid.empty params

  (* Build the ident-to-tindex substitution that binds each idxvar
     of [params]. Explicit indices (positional or named) are used
     where provided; every other idxvar gets a fresh TIUnivar so
     type-directed unification can assign it later. Named
     instantiation may be partial. *)
  let openidx (ue : unienv) (params : ty_params) (tvi : tvar_inst option) : tindex Mid.t =
    let infer_all () =
      List.fold_left
        (fun s v -> Mid.add v (idx_fresh ue) s)
        Mid.empty params.idxvars
    in
    match tvi_indices tvi with
    | IXunamed [] -> infer_all ()

    | IXunamed ix ->
        if List.compare_lengths ix params.idxvars <> 0 then
          (* CONTRACT: the arity fallback exists ONLY for the select
             loop (a candidate op may be tried among others; arity
             incompatibility is reported there as OF_idx_arity).
             Every other caller validates arity beforehand
             (pf_check_tvi for lemmas, tvi_compat for selection), so
             a mismatch reaching a non-select caller is a caller
             bug -- it silently infers instead of failing. *)
          infer_all ()
        else
          List.fold_left2
            (fun s v ti -> Mid.add v ti s)
            Mid.empty params.idxvars ix

    | IXnamed ix ->
        List.iter (fun (name, _) ->
          if not (List.exists (fun v -> EcIdent.name v = name) params.idxvars) then
            raise (UnknownIndexVariable name))
          ix;
        List.fold_left
          (fun s v ->
            let ti =
              try  List.assoc (EcIdent.name v) ix
              with Not_found -> idx_fresh ue
            in Mid.add v ti s)
          Mid.empty params.idxvars

  let subst_tv (subst : ty -> ty) (params : ty_params) =
    List.map (fun tv -> subst (tvar tv)) params.tyvars

  (* Open the index params: build the [TIVar -> TIVar/TIUnivar] map,
     then resolve each idxvar through it (so explicit user-supplied
     indices come back as-is). Returned in [params.idxvars] order. *)
  let subst_ix (idxmap : tindex Mid.t) (params : ty_params) =
    List.map (fun id ->
      Option.value (Mid.find_opt id idxmap) ~default:(TIVar id))
      params.idxvars

  let openty_r (ue : unienv) (params : ty_params) (tvi : tvar_inst option) =
    let idxmap = openidx ue params tvi in
    let subst =
      f_subst_init
        ~tv:(opentvi ue params tvi)
        ~idx:idxmap
        () in
    let ixs = subst_ix idxmap params in
    let tys = subst_tv (ty_subst subst) params in
    (subst, ixs, tys)

  let opentys (ue : unienv) (params : ty_params) (tvi : tvar_inst option) (tys : ty list) =
    let (subst, _, tvs) = openty_r ue params tvi in
      (List.map (ty_subst subst) tys, tvs)

  let openty (ue : unienv) (params : ty_params) (tvi : tvar_inst option) (ty : ty)=
    let (subst, _, tvs) = openty_r ue params tvi in
      (ty_subst subst ty, tvs)

  let repr (ue : unienv) (t : ty) : ty =
    match t.ty_node with
    | Tunivar id -> odfl t (UF.data id (!ue).ue_uf)
    | _ -> t

  let closed_tv (ue : unienv) =
    UF.closed (!ue).ue_uf

  (* The index side: every allocated index univar got an assignment.
     Exposed separately so uninferred *indices* can be reported as
     such instead of as "free type variables". *)
  let closed_iu (ue : unienv) =
    Suid.subset (!ue).ue_iuf_alloc
      (Muid.fold (fun u _ s -> Suid.add u s)
         (!ue).ue_iuf Suid.empty)

  let closed (ue : unienv) =
    closed_tv ue && closed_iu ue

  let close (ue : unienv) =
    if not (closed ue) then raise UninstantiateUni;
    (subst_of_uf (!ue).ue_uf)

  let assubst (ue : unienv) =
    subst_of_uf (!ue).ue_uf

  (* Index-univar assignment map after typechecking. Use to build a
     [f_subst] that resolves residual TIUnivars in computed types. *)
  let iu_close (ue : unienv) : tindex Muid.t =
    if not (closed ue) then raise UninstantiateUni;
    (!ue).ue_iuf

  let iu_assubst (ue : unienv) : tindex Muid.t =
    (!ue).ue_iuf

  (* Build a full [f_subst] that resolves both type-univars and
     index-univars in one shot. Use this where the legacy
     [Tuni.subst (close ue)] is followed by an [f_subst] application
     to a type or formula that may carry indexed types — without the
     idx-univar substitution, [TIUnivar] nodes survive into the saved
     AST and break later matching. *)
  let close_subst (ue : unienv) : f_subst =
    if not (closed ue) then raise UninstantiateUni;
    f_subst_init
      ~tu:(subst_of_uf (!ue).ue_uf)
      ~iu:(!ue).ue_iuf
      ()

  (* Non-raising variant: substitute the resolved univars of both
     kinds, leave the unresolved ones in place. *)
  (* Chase [ue_iuf] chains: the assignment map may bind a univar to
     another univar. *)
  let repr_tindex (ue : unienv) (ti : tindex) : tindex =
    resolve_tindex ue ti

  let as_subst (ue : unienv) : f_subst =
    f_subst_init
      ~tu:(subst_of_uf (!ue).ue_uf)
      ~iu:(!ue).ue_iuf
      ()

  let tparams (ue : unienv) : ty_params =
    { idxvars = List.rev (!ue).ue_idxdecl;
      tyvars  = List.rev (!ue).ue_decl; }
end

(* -------------------------------------------------------------------- *)
let unify (env : EcEnv.env) (ue : unienv) (t1 : ty) (t2 : ty) =
  unify_core env ue (`TyUni (t1, t2))

(* Index unification — same engine, different problem kind. Used by
   the matching engine to match [Tconstr (p, {indices=...; types=...})]
   patterns where indices may carry univars. *)
let unify_idx (env : EcEnv.env) (ue : unienv) (i1 : tindex) (i2 : tindex) =
  unify_core env ue (`IxUni (i1, i2))

(* -------------------------------------------------------------------- *)
let tfun_expected ue ?retty psig =
  let retty = ofdfl (fun () -> UniEnv.fresh ue) retty in
  EcTypes.toarrow psig retty

(* -------------------------------------------------------------------- *)
type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

(* -------------------------------------------------------------------- *)
type select_result =
  (EcPath.path * tindex list * ty list) * ty * unienv * sbody option

(* -------------------------------------------------------------------- *)
type op_failure =
  | OF_argument of int * ty * ty   (* 1-based index, expected (param), provided (arg) *)
  | OF_result   of ty * ty         (* operator result type, expected result type *)
  | OF_arity    of int * int       (* expected arity (at most), provided *)
  | OF_idx_arity   of int * int    (* expected #index params, provided *)
  | OF_idx_unknown of EcSymbols.symbol (* named index binding no index param *)
  | OF_tv_arity    of int * int    (* expected #type params, provided *)
  | OF_tv_unknown  of EcSymbols.symbol (* named tyvar binding no type param *)

(* -------------------------------------------------------------------- *)
(* Parameters of an operator constrained while applying it. *)
type op_instance = {
  oi_tys : (EcIdent.t * ty) list;
  oi_ixs : (EcIdent.t * tindex) list;
}

type select_outcome =
  | OK of select_result
  | KO of (EcPath.path * op_instance * ty * op_failure) Lazy.t
    (* operator path, partial instantiation, declared operator type, reason *)

(* -------------------------------------------------------------------- *)
(* Resolve both type- and index-univars of [ty]: failure reports must
   show inferred indices, not raw index univars. (No index
   normalization: [ty] hashconsing compares indices canonically, so a
   rebuilt [vec<:8>] IS the interned [vec<:3+5>] node — the display
   spelling is whichever was interned first, deterministic per file.) *)
let resolve_ty_for_report (ue : unienv) (ty : ty) : ty =
  ty_subst
    (f_subst_init ~tu:(UniEnv.assubst ue) ~iu:(UniEnv.iu_assubst ue) ())
    ty

(* -------------------------------------------------------------------- *)
(* [None] if [top] applies to [psig] (and [retty]), updating [ue]; otherwise
   [Some] of the first argument/result/arity failure. *)
let classify_application
   (env  : EcEnv.env)
   (ue   : unienv)
   (top  : ty)
   (psig : ty list)
   (retty : ty option)
  : op_failure option
=
  let exception Failure_with of op_failure in

  (* Resolve both type- and index-univars: failure reports must show
     inferred indices, not raw index univars. *)
  let resolve ty = resolve_ty_for_report ue ty in
  let whnf ty = EcEnv.ty_hnorm (resolve ty) env in

  let unify env ue t1 t2 =
    unify_core ~transactional:false env ue (`TyUni (t1, t2)) in

  let rec peel i cur args =
    match args with
    | [] -> begin
        match retty with
        | None -> None
        | Some r ->
            try  unify env ue cur r; None
            with UnificationFailure _ ->
              Some (OF_result (resolve cur, resolve r))
      end

    | a :: args ->
        match (whnf cur).ty_node with
        | Tfun (d, c) ->
            (try  unify env ue d a
             with UnificationFailure _ ->
               raise_notrace (Failure_with (OF_argument (i, resolve d, resolve a))));
            peel (i+1) c args

        | Tunivar _ ->
            let d = UniEnv.fresh ue in
            let c = UniEnv.fresh ue in
            (try  unify env ue cur (tfun d c)
             with UnificationFailure _ ->
               raise_notrace (Failure_with (OF_arity (List.length psig, i-1))));
            (try  unify env ue d a
             with UnificationFailure _ ->
               raise_notrace (Failure_with (OF_argument (i, resolve d, resolve a))));
            peel (i+1) c args

        | _ ->
            Some (OF_arity (List.length psig, i-1))
  in
    try peel 1 top psig with Failure_with f -> Some f

(* -------------------------------------------------------------------- *)
let select_op_outcomes
  ?(hidden : bool = false)
  ?(filter : EcPath.path -> operator -> bool = fun _ _ -> true)
   (tvi    : tvar_inst option)
   (env    : EcEnv.env)
   (name   : qsymbol)
   (ue     : unienv)
   (sig_   : ty list * ty option)
  : select_outcome list
=
  ignore hidden;                (* FIXME *)

  let module D = EcDecl in

  let (psig, retty) = sig_ in

  (* An explicit instantiation incompatible with the candidate is not a
     silent pre-filter: it classifies the candidate as a [KO] with a
     precise reason, so a zero-[OK] selection can explain itself
     instead of degenerating to "unknown variable or constant". *)
  let tvi_compat (op : D.operator) : op_failure option =
    match tvi with
    | None -> None
    | Some tvi_ ->
        (* Index side: a positional non-empty list must match the
           candidate's index arity; a named list must only use the
           candidate's idxvar names (it may be partial). Empty means
           "infer this side". *)
        let idxvars = op.D.op_tparams.idxvars in
        let idx_fail =
          match tvi_indices (Some tvi_) with
          | IXunamed [] -> None
          | IXunamed ix ->
              let n = List.length ix in
              if n <> List.length idxvars then
                Some (OF_idx_arity (List.length idxvars, n))
              else None
          | IXnamed ix ->
              let iparams = Ssym.of_list (List.map EcIdent.name idxvars) in
              List.find_map_opt
                (fun (x, _) ->
                  if Ssym.mem x iparams then None
                  else Some (OF_idx_unknown x))
                ix
        in

        let tyvars = op.D.op_tparams.tyvars in
        let ty_fail =
          match tvi_ with
          | TVIunamed (_, []) -> None
          | TVIunamed (_, lt) ->
              let n = List.length lt in
              if n <> List.length tyvars then
                Some (OF_tv_arity (List.length tyvars, n))
              else None
          | TVInamed (_, ls) ->
              let tparams = Ssym.of_list (List.map EcIdent.name tyvars) in
              List.find_map_opt
                (fun (x, _) ->
                  if Ssym.mem x tparams then None
                  else Some (OF_tv_unknown x))
                ls
        in
        (match idx_fail with Some _ -> idx_fail | None -> ty_fail)
  in

  let mk_ok (path, op) tip ixs tvs top subue =
    let bd =
      match op.D.op_kind with
      | OB_nott nt ->
         let substnt () =
           let xs = List.map (snd_map (ty_subst tip)) nt.D.ont_args in
           let es = e_subst tip in
           let bd = es nt.D.ont_body in
           (xs, bd)
         in Some (Lazy.from_fun substnt)

      | _ -> None

    in OK ((path, ixs, tvs), top, subue, bd)
  in

  let classify (path, op) =
    let subue = UniEnv.copy ue in

    let (tip, ixs, tvs) = UniEnv.openty_r subue op.D.op_tparams tvi in
    let top = ty_subst tip op.D.op_ty in

    let resolve ty = resolve_ty_for_report subue ty in

    (* [select] builds a [KO] only after unification rejected the candidate. *)
    let f = oget (classify_application env subue top psig retty) in
    let instance = {
      oi_tys =
        List.combine op.D.op_tparams.tyvars tvs
        |> List.filter_map (fun (tp, tv) ->
             match (resolve tv).ty_node with
             | Tunivar _ -> None
             | _         -> Some (tp, resolve tv));
      oi_ixs =
        List.combine op.D.op_tparams.idxvars ixs
        |> List.filter_map (fun (ip, iv) ->
             match resolve_tindex subue iv with
             | TIUnivar _ -> None
             | iv         -> Some (ip, tindex_normalize iv));
    } in
    (path, instance, op.D.op_ty, f)
  in

  let select (path, op) =
    match tvi_compat op with
    | Some f ->
        (* Do not open/unify: [openidx] falls back to inference on a
           positional-arity mismatch, so a wrong-arity candidate could
           otherwise unify successfully. *)
        KO (lazy (path, { oi_tys = []; oi_ixs = [] }, op.D.op_ty, f))

    | None ->

    let subue = UniEnv.copy ue in

    let (tip, ixs, tvs) = UniEnv.openty_r subue op.D.op_tparams tvi in
    let top = ty_subst tip op.D.op_ty in

    let texpected = tfun_expected subue ?retty psig in

    match unify env subue top texpected with
    | () -> mk_ok (path, op) tip ixs tvs top subue
    | exception UnificationFailure _ -> KO (lazy (classify (path, op)))

  in
    List.map select (EcEnv.Op.all ~check:filter ~name env)

(* -------------------------------------------------------------------- *)
let select_op
  ?hidden ?filter (tvi : tvar_inst option)
  (env : EcEnv.env) (name : qsymbol) (ue : unienv)
  (sig_ : ty list * ty option)
  : select_result list
=
  List.filter_map
    (function OK r -> Some r | KO _ -> None)
    (select_op_outcomes ?hidden ?filter tvi env name ue sig_)

(* -------------------------------------------------------------------- *)
(* The candidates of that name that fail to apply, with the reason why. *)
let select_op_failures
  ?hidden ?filter (tvi : tvar_inst option)
  (env : EcEnv.env) (name : qsymbol) (ue : unienv)
  (sig_ : ty list * ty option)
  : (EcPath.path * op_instance * ty * op_failure) list
=
  List.filter_map
    (function KO lz -> Some (Lazy.force lz) | OK _ -> None)
    (select_op_outcomes ?hidden ?filter tvi env name ue sig_)
