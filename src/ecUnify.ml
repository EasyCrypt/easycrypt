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
type pb = [ `TyUni of ty * ty ]

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
let unify_core (env : EcEnv.env) (uf : UF.t) pb =
  let failure () = raise (UnificationFailure pb) in

  let uf = ref uf in
  let pb = let x = Queue.create () in Queue.push pb x; x in

  let ocheck i t =
    let i   = UF.find i !uf in
    let map = Hint.create 0 in

    let rec doit t =
      match t.ty_node with
      | Tunivar i' -> begin
          let i' = UF.find i' !uf in
            match i' with
            | _ when i = i' -> true
            | _ when Hint.mem map i' -> false
            | _ ->
                match UF.data i' !uf with
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
    let (ti, effects) = UFArgs.D.union (UF.data i !uf) (Some t) in
      if odfl false (ti |> omap (ocheck i)) then failure ();
      List.iter (Queue.push^~ pb) effects;
      uf := UF.set i ti !uf

  and getvar t =
    match t.ty_node with
    | Tunivar i -> odfl t (UF.data i !uf)
    | _ -> t

  in

  let doit () =
    while not (Queue.is_empty pb) do
      match Queue.pop pb with
      | `TyUni (t1, t2) -> begin
        let (t1, t2) = (getvar t1, getvar t2) in

        match ty_equal t1 t2 with
        | true  -> ()
        | false -> begin
            match t1.ty_node, t2.ty_node with
            | Tunivar id1, Tunivar id2 -> begin
                if not (uid_equal id1 id2) then
                  let effects = reffold (swap -| UF.union id1 id2) uf in
                    List.iter (Queue.push^~ pb) effects
            end

            | Tunivar id, _ -> setvar id t2
            | _, Tunivar id -> setvar id t1

            | Ttuple lt1, Ttuple lt2 ->
                if List.length lt1 <> List.length lt2 then failure ();
                List.iter2 (fun t1 t2 -> Queue.push (`TyUni (t1, t2)) pb) lt1 lt2

            | Tfun (t1, t2), Tfun (t1', t2') ->
                Queue.push (`TyUni (t1, t1')) pb;
                Queue.push (`TyUni (t2, t2')) pb

            | Tconstr (p1, lt1), Tconstr (p2, lt2) when EcPath.p_equal p1 p2 ->
                if List.length lt1 <> List.length lt2 then failure ();
                List.iter2 (fun t1 t2 -> Queue.push (`TyUni (t1, t2)) pb) lt1 lt2

            | Tconstr (p, lt), _ when EcEnv.Ty.defined p env ->
                Queue.push (`TyUni (EcEnv.Ty.unfold p lt env, t2)) pb

            | _, Tconstr (p, lt) when EcEnv.Ty.defined p env ->
                Queue.push (`TyUni (t1, EcEnv.Ty.unfold p lt env)) pb

            | _, _ -> failure ()
        end
      end
    done
  in
    doit (); !uf

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
type unienv_r = {
  ue_uf     : UF.t;
  ue_named  : EcIdent.t Mstr.t;
  ue_decl   : EcIdent.t list;
  ue_closed : bool;
}

type unienv = unienv_r ref

type tvar_inst =
| TVIunamed of ty list
| TVInamed  of (EcSymbols.symbol * ty) list

type tvi = tvar_inst option
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

  let create (vd : EcIdent.t list option) =
    let ue = {
      ue_uf     = UF.initial;
      ue_named  = Mstr.empty;
      ue_decl   = [];
      ue_closed = false;
    } in

    let ue =
      match vd with
      | None    -> ue
      | Some vd ->
          let vdmap = List.map (fun x -> (EcIdent.name x, x)) vd in
          { ue with
              ue_named  = Mstr.of_list vdmap;
              ue_decl   = List.rev vd;
              ue_closed = true; }
    in
      ref ue

  let fresh ?(ty : ty option) (ue : unienv) =
    let (uf, uid) = UnifyCore.fresh ?ty (!ue).ue_uf in
      ue := { !ue with ue_uf = uf }; uid

  let opentvi (ue : unienv) (params : ty_params) (tvi : tvar_inst option) =
    match tvi with
    | None ->
        List.fold_left
          (fun s v -> Mid.add v (fresh ue) s)
          Mid.empty params

    | Some (TVIunamed lt) ->
        List.fold_left2
          (fun s v ty -> Mid.add v (fresh ~ty ue) s)
          Mid.empty params lt

    | Some (TVInamed lt) ->
        let for1 s v =
          let t =
            try  fresh ~ty:(List.assoc (EcIdent.name v) lt) ue
            with Not_found -> fresh ue
          in
            Mid.add v t s
        in
          List.fold_left for1 Mid.empty params

  let subst_tv (subst : ty -> ty) (params : ty_params) =
    List.map (fun tv -> subst (tvar tv)) params

  let openty_r (ue : unienv) (params : ty_params) (tvi : tvar_inst option) =
    let subst = f_subst_init ~tv:(opentvi ue params tvi) () in
      (subst, subst_tv (ty_subst subst) params)

  let opentys (ue : unienv) (params : ty_params) (tvi : tvar_inst option) (tys : ty list) =
    let (subst, tvs) = openty_r ue params tvi in
      (List.map (ty_subst subst) tys, tvs)

  let openty (ue : unienv) (params : ty_params) (tvi : tvar_inst option) (ty : ty)=
    let (subst, tvs) = openty_r ue params tvi in
      (ty_subst subst ty, tvs)

  let repr (ue : unienv) (t : ty) : ty =
    match t.ty_node with
    | Tunivar id -> odfl t (UF.data id (!ue).ue_uf)
    | _ -> t

  let closed (ue : unienv) =
    UF.closed (!ue).ue_uf

  let close (ue : unienv) =
    if not (closed ue) then raise UninstantiateUni;
    (subst_of_uf (!ue).ue_uf)

  let assubst (ue : unienv) =
    subst_of_uf (!ue).ue_uf

  let tparams (ue : unienv) : ty_params =
    List.rev (!ue).ue_decl
end

(* -------------------------------------------------------------------- *)
let unify (env : EcEnv.env) (ue : unienv) (t1 : ty) (t2 : ty) =
  let uf = unify_core env (!ue).ue_uf (`TyUni (t1, t2)) in
  ue := { !ue with ue_uf = uf; }

(* -------------------------------------------------------------------- *)
let tfun_expected ue ?retty psig =
  let retty = ofdfl (fun () -> UniEnv.fresh ue) retty in
  EcTypes.toarrow psig retty

(* -------------------------------------------------------------------- *)
type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

(* -------------------------------------------------------------------- *)
type select_result = (EcPath.path * ty list) * ty * unienv * sbody option

(* -------------------------------------------------------------------- *)
type op_failure =
  | OF_argument of int * ty * ty   (* 1-based index, expected (param), provided (arg) *)
  | OF_result   of ty * ty         (* operator result type, expected result type *)
  | OF_arity    of int * int       (* expected arity (at most), provided *)

(* -------------------------------------------------------------------- *)
(* Constrained type parameters of an operator (those bound while applying it). *)
type op_instance = (EcIdent.t * ty) list

type select_outcome =
  | OK of select_result
  | KO of (EcPath.path * op_instance * ty * op_failure) Lazy.t
    (* operator path, partial instantiation, declared operator type, reason *)

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

  let resolve ty = ty_subst (Tuni.subst (UniEnv.assubst ue)) ty in
  let whnf ty = EcEnv.ty_hnorm (resolve ty) env in

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

  let filter oppath op =
    (* Filter operator based on given type variables instanciation *)
    let filter_on_tvi =
      match tvi with
      | None -> fun _ -> true

      | Some (TVIunamed lt) ->
          let len = List.length lt in
            fun op ->
              let tparams = op.D.op_tparams in
                 List.length tparams = len

      | Some (TVInamed ls) -> fun op ->
          let tparams = List.map EcIdent.name op.D.op_tparams in
          let tparams = Ssym.of_list tparams in
          List.for_all (fun (x, _) -> Msym.mem x tparams) ls

    in
      filter oppath op && filter_on_tvi op
  in

  let mk_ok (path, op) tip tvs top subue =
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

    in OK ((path, tvs), top, subue, bd)
  in

  let classify (path, op) =
    let subue = UniEnv.copy ue in

    let (tip, tvs) = UniEnv.openty_r subue op.D.op_tparams tvi in
    let top = ty_subst tip op.D.op_ty in

    let resolve ty = ty_subst (Tuni.subst (UniEnv.assubst subue)) ty in

    (* [select] builds a [KO] only after unification rejected the candidate. *)
    let f = oget (classify_application env subue top psig retty) in
    let instance =
      List.combine op.D.op_tparams tvs
      |> List.filter_map (fun (tp, tv) ->
           match (resolve tv).ty_node with
           | Tunivar _ -> None
           | _         -> Some (tp, resolve tv))
    in
    (path, instance, op.D.op_ty, f)
  in

  let select (path, op) =
    let subue = UniEnv.copy ue in

    let (tip, tvs) = UniEnv.openty_r subue op.D.op_tparams tvi in
    let top = ty_subst tip op.D.op_ty in

    let texpected = tfun_expected subue ?retty psig in

    match unify env subue top texpected with
    | () -> mk_ok (path, op) tip tvs top subue
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
