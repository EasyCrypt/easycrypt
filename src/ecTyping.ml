(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcMaps
open EcSymbols
open EcLocation
open EcParsetree
open EcAst
open EcTypes
open EcDecl
open EcMemory
open EcModules
open EcFol
open EcMatching.Position

module MMsym = EcSymbols.MMsym
module Sid   = EcIdent.Sid
module Mid   = EcIdent.Mid

module EqTest = EcReduction.EqTest
module NormMp = EcEnv.NormMp

(* -------------------------------------------------------------------- *)
type opmatch = [
  | `Op   of EcPath.path * EcTypes.ty list
  | `Lc   of EcIdent.t
  | `Var  of EcTypes.prog_var
  | `Proj of EcTypes.prog_var * EcMemory.proj_arg
]

type 'a mismatch_sets = [`Eq of 'a * 'a | `Sub of 'a ]

type 'a suboreq       = [`Eq of 'a | `Sub of 'a ]

type mismatch_funsig =
| MF_targs     of ty * ty                               (* expected, got *)
| MF_tres      of ty * ty                               (* expected, got *)
| MF_restr     of EcEnv.env * Sx.t mismatch_sets

type restr_failure = Sx.t * Sm.t

type restr_eq_failure = Sx.t * Sm.t * Sx.t * Sm.t

type mismatch_restr = [
  | `Sub    of restr_failure          (* Should not be allowed *)
  | `RevSub of restr_failure option   (* Should be allowed. None is everybody *)
  | `Eq     of restr_eq_failure       (* Should be equal *)
  | `FunCanCallUnboundedOracle of symbol * EcPath.xpath
]

(* -------------------------------------------------------------------- *)
type restriction_who =
| RW_mod of EcPath.mpath
| RW_fun of EcPath.xpath

type restriction_error = restriction_who * [
  | `Sub of restr_failure             (* Should not be allowed *)
  | `RevSub of restr_failure option   (* Should be allowed. None is everybody *)
  ]

exception RestrictionError of EcEnv.env * restriction_error

type tymod_cnv_failure =
| E_TyModCnv_ParamCountMismatch
| E_TyModCnv_ParamTypeMismatch of EcIdent.t
| E_TyModCnv_MissingComp       of symbol

| E_TyModCnv_MismatchRestr of symbol * mismatch_restr

| E_TyModCnv_MismatchFunSig    of symbol * mismatch_funsig
| E_TyModCnv_SubTypeArg        of
    EcIdent.t * module_type * module_type * tymod_cnv_failure

type modapp_error =
| MAE_WrongArgCount       of int * int  (* expected, got *)
| MAE_InvalidArgType      of EcPath.mpath * tymod_cnv_failure
| MAE_AccesSubModFunctor

type modtyp_error =
| MTE_IncludeFunctor
| MTE_InnerFunctor
| MTE_DupProcName of symbol

type modsig_error =
| MTS_DupProcName of symbol
| MTS_DupArgName  of symbol * symbol

type modupd_error =
| MUE_Functor
| MUE_AbstractFun
| MUE_AbstractModule
| MUE_InvalidFun
| MUE_InvalidCodePos
| MUE_InvalidTargetCond

type funapp_error =
| FAE_WrongArgCount

type mem_error =
| MAE_IsConcrete

type fxerror =
| FXE_EmptyMatch
| FXE_MatchParamsMixed
| FXE_MatchParamsDup
| FXE_MatchParamsUnk
| FXE_MatchNonLinear
| FXE_MatchDupBranches
| FXE_MatchPartial
| FXE_CtorUnk
| FXE_CtorAmbiguous
| FXE_CtorInvalidArity of (symbol * int * int)
| FXE_SynCheckFailure

type filter_error =
| FE_InvalidIndex of int
| FE_NoMatch

type tyerror =
| UniVarNotAllowed
| FreeTypeVariables
| TypeVarNotAllowed
| OnlyMonoTypeAllowed    of symbol option
| NoConcreteAnonParams
| UnboundTypeParameter   of symbol
| UnknownTypeName        of qsymbol
| UnknownTypeClass       of qsymbol
| UnknownRecFieldName    of qsymbol
| UnknownInstrMetaVar    of symbol
| UnknownMetaVar         of symbol
| UnknownProgVar         of qsymbol * EcMemory.memory
| DuplicatedRecFieldName of symbol
| MissingRecField        of symbol
| MixingRecFields        of EcPath.path tuple2
| UnknownProj            of qsymbol
| AmbiguousProj          of qsymbol
| AmbiguousProji         of int * ty
| InvalidTypeAppl        of qsymbol * int * int
| DuplicatedTyVar
| DuplicatedLocal        of symbol
| DuplicatedField        of symbol
| NonLinearPattern
| LvNonLinear
| NonUnitFunWithoutReturn
| TypeMismatch           of (ty * ty) * (ty * ty)
| TypeClassMismatch
| TypeModMismatch        of mpath * module_type * tymod_cnv_failure
| NotAFunction
| NotAnInductive
| AbbrevLowArgs
| UnknownVarOrOp         of qsymbol * ty list
| MultipleOpMatch        of qsymbol * ty list * (opmatch * EcUnify.unienv) list
| UnknownModName         of qsymbol
| UnknownTyModName       of qsymbol
| UnknownFunName         of qsymbol
| UnknownModVar          of qsymbol
| UnknownMemName         of symbol
| InvalidFunAppl         of funapp_error
| InvalidModAppl         of modapp_error
| InvalidModType         of modtyp_error
| InvalidModSig          of modsig_error
| InvalidModUpdate       of modupd_error
| InvalidMem             of symbol * mem_error
| InvalidMatch           of fxerror
| InvalidFilter          of filter_error
| FunNotInModParam       of qsymbol
| FunNotInSignature      of symbol
| InvalidVar
| NoActiveMemory
| PatternNotAllowed
| MemNotAllowed
| UnknownScope           of qsymbol
| NoWP
| FilterMatchFailure
| MissingMemType
| ModuleNotAbstract      of symbol
| ProcedureUnbounded     of symbol * symbol
| LvMapOnNonAssign
| NoDefaultMemRestr
| ProcAssign             of qsymbol
| PositiveShouldBeBeforeNegative
| NotAnExpression        of [`Unknown | `LL | `Pr | `Logic | `Glob | `MemSel]

(* -------------------------------------------------------------------- *)
exception TyError of EcLocation.t * EcEnv.env * tyerror

let tyerror loc env e = raise (TyError (loc, env, e))

(* -------------------------------------------------------------------- *)
type ptnmap = ty EcIdent.Mid.t ref
type metavs = EcFol.form Msym.t

(* -------------------------------------------------------------------- *)
let ident_of_osymbol (x : osymbol_r): EcIdent.ident =
  omap unloc x |> odfl "_" |> EcIdent.create

(* -------------------------------------------------------------------- *)
module UE = EcUnify.UniEnv

let unify_or_fail (env : EcEnv.env) ue loc ~expct:ty1 ty2 =
  try  EcUnify.unify env ue ty1 ty2
  with EcUnify.UnificationFailure pb ->
    match pb with
    | `TyUni (t1, t2)->
       let uidmap = UE.assubst ue in
       let tyinst = ty_subst (Tuni.subst uidmap) in
       tyerror loc env (TypeMismatch ((tyinst ty1, tyinst ty2),
                                      (tyinst  t1, tyinst  t2)))

(* -------------------------------------------------------------------- *)
let add_glob (m:Sx.t) (x:prog_var) : Sx.t =
  if is_glob x then Sx.add (get_glob x) m else m

let e_inuse =
  let rec inuse (map : Sx.t) (e : expr) =
    match e.e_node with
    | Evar x -> add_glob map x
    | _ -> e_fold inuse map e
  in
    fun e -> inuse Sx.empty e

(* -------------------------------------------------------------------- *)
let empty_uses : uses = mk_uses [] Sx.empty Sx.empty

let add_call (u : uses) p : uses =
  mk_uses (p::u.us_calls) u.us_reads u.us_writes

let add_read (u : uses) p : uses =
  if is_glob p then
    mk_uses u.us_calls (Sx.add (get_glob p) u.us_reads) u.us_writes
  else u

let add_write (u : uses) p : uses =
  if is_glob p then
    mk_uses u.us_calls u.us_reads (Sx.add (get_glob p) u.us_writes)
  else u

let (_i_inuse, s_inuse, se_inuse) =
  let rec lv_inuse (map : uses) (lv : lvalue) =
    match lv with
    | LvVar (p,_) ->
        add_write map p

    | LvTuple ps ->
        List.fold_left
          (fun map (p, _) -> add_write map p)
          map ps

  and i_inuse (map : uses) (i : instr) =
    match i.i_node with
    | Sasgn (lv, e) ->
      let map = lv_inuse map lv in
      let map = se_inuse map e in
        map

    | Srnd (lv, e) ->
      let map = lv_inuse map lv in
      let map = se_inuse map e in
        map

    | Scall (lv, p, es) -> begin
      let map = List.fold_left se_inuse map es in
      let map = add_call map p in
      let map = lv |> ofold ((^~) lv_inuse) map in
        map
    end

    | Sif (e, s1, s2) ->
      let map = se_inuse map e in
      let map = s_inuse map s1 in
      let map = s_inuse map s2 in
        map

    | Swhile (e, s) ->
      let map = se_inuse map e in
      let map = s_inuse map s in
        map

    | Smatch (e, bs) ->
      let map = se_inuse map e in
      let map = List.fold_left (fun map -> s_inuse map -| snd) map bs in
        map

    | Sassert e ->
      se_inuse map e

    | Sabstract _ ->
      assert false (* FIXME *)

  and s_inuse (map : uses) (s : stmt) =
    List.fold_left i_inuse map s.s_node

  and se_inuse (u : uses) (e : expr) =
    mk_uses u.us_calls (Sx.union u.us_reads (e_inuse e)) u.us_writes

  in
    (i_inuse empty_uses, s_inuse empty_uses, se_inuse)

(* -------------------------------------------------------------------- *)
let select_local env (qs,s) =
  if   qs = []
  then EcEnv.Var.lookup_local_opt s env
  else None

(* -------------------------------------------------------------------- *)
let select_pv env side name ue tvi (psig, retty) =
  if   tvi <> None
  then []
  else
    try
      let pvs = EcEnv.Var.lookup_progvar ?side name env in
      let select (pv,ty) =
        let subue = UE.copy ue in
        let texpected = EcUnify.tfun_expected subue ?retty psig in
          try
            EcUnify.unify env subue ty texpected;
            [(pv, ty, subue)]
          with EcUnify.UnificationFailure _ -> []
      in
        select pvs
    with EcEnv.LookupFailure _ -> []

(* -------------------------------------------------------------------- *)
module OpSelect = struct
  type pvsel = [
    | `Proj of EcTypes.prog_var * EcMemory.proj_arg
    | `Var  of EcTypes.prog_var
  ]

  type opsel = [
    | `Pv of EcMemory.memory option * pvsel
    | `Op of (EcPath.path * ty list)
    | `Lc of EcIdent.ident
    | `Nt of EcUnify.sbody
  ]

  type mode = [`Form | `Expr of [`InProc | `InOp]]

  type gopsel =
    opsel * EcTypes.ty * EcUnify.unienv * opmatch
end

let gen_select_op
    ~(actonly : bool)
    ~(mode    : OpSelect.mode)
    ~(forcepv  : bool)
    (opsc     : path option)
    (tvi      : EcUnify.tvi)
    (env      : EcEnv.env)
    (name     : EcSymbols.qsymbol)
    (ue       : EcUnify.unienv)
    (psig     : EcTypes.dom * EcTypes.ty option)

    : OpSelect.gopsel list
=

  let fpv me (pv, ty, ue) : OpSelect.gopsel =
    (`Pv (me, pv), ty, ue, (pv :> opmatch))

  and fop (op, ty, ue, bd) : OpSelect.gopsel=
    match bd with
    | None -> (`Op op, ty, ue, (`Op op :> opmatch))
    | Some bd -> (`Nt bd, ty, ue, (`Op op :> opmatch))

  and flc (lc, ty, ue) : OpSelect.gopsel =
    (`Lc lc, ty, ue, (`Lc lc :> opmatch)) in

  let ue_filter =
    match mode with
    | `Expr _ -> fun _ op -> not (EcDecl.is_pred op)
    | `Form   -> fun _ _  -> true
  in

  let by_scope opsc ((p, _), _, _, _) =
    EcPath.p_equal opsc (oget (EcPath.prefix p))

  and by_current ((p, _), _, _, _) =
    EcPath.isprefix ~prefix:(oget (EcPath.prefix p)) ~path:(EcEnv.root env)

  and by_tc ((p, _), _, _, _) =
    match oget (EcEnv.Op.by_path_opt p env) with
    | { op_kind = OB_oper (Some OP_TC) } -> false
    | _ -> true

  in

  let locals () : OpSelect.gopsel list =
    if Option.is_none tvi then
      select_local env name
      |> Option.map
          (fun (id, ty) -> flc (id, ty, ue))
      |>  Option.to_list
    else [] in

  let ops () : OpSelect.gopsel list =
    let ops = EcUnify.select_op ~filter:ue_filter tvi env name ue psig in
    let ops = opsc |> ofold (fun opsc -> List.mbfilter (by_scope opsc)) ops in
    let ops = match List.mbfilter by_current ops with [] -> ops | ops -> ops in
    let ops = match List.mbfilter by_tc ops with [] -> ops | ops -> ops in
    (List.map fop ops)

  and pvs () : OpSelect.gopsel list =
    let me, pvs =
      match EcEnv.Memory.get_active_ss env, actonly with
      | None, true -> (None, [])
      | me  , _    -> (  me, select_pv env me name ue tvi psig)
    in List.map (fpv me) pvs
  in

  let select (filters : (unit -> OpSelect.gopsel list) list) : OpSelect.gopsel list =
    List.find_map_opt
      (fun f -> match f () with [] -> None | x -> Some x)
      filters
    |> odfl [] in

  match mode with
  | `Expr `InOp   -> select [locals; ops]
  | `Form
  | `Expr `InProc ->
      if forcepv then
        select [pvs; locals; ops]
      else
        select [locals; pvs; ops]

(* -------------------------------------------------------------------- *)
let select_exp_op env mode opsc name ue tvi psig =
  gen_select_op ~actonly:false ~forcepv:false ~mode:(`Expr mode)
    opsc tvi env name ue psig

(* -------------------------------------------------------------------- *)
let select_form_op env mode ~forcepv opsc name ue tvi psig =
  gen_select_op ~actonly:true ~mode ~forcepv
    opsc tvi env name ue psig

(* -------------------------------------------------------------------- *)
let select_proj env opsc name ue tvi recty =
  let filter = (fun _ op -> EcDecl.is_proj op) in
  let ops = EcUnify.select_op ~filter tvi env name ue ([recty], None) in
  let ops = List.map (fun (p, ty, ue, _) -> (p, ty, ue)) ops in

  match ops, opsc with
  | _ :: _ :: _, Some opsc ->
      List.filter
        (fun ((p, _), _, _) ->
          EcPath.p_equal opsc (oget (EcPath.prefix p)))
        ops

  | _, _ -> ops

(* -------------------------------------------------------------------- *)
let lookup_scope env popsc =
  match unloc popsc with
  | ([], x) when x = EcCoreLib.i_top -> EcCoreLib.p_top
  | _ -> begin
    match EcEnv.Theory.lookup_opt (unloc popsc) env with
    | None -> tyerror popsc.pl_loc env (UnknownScope (unloc popsc))
    | Some opsc -> fst opsc
  end

(* -------------------------------------------------------------------- *)
type typolicy = {
  tp_uni  : bool;   (* "_" (Tunivar) allowed  *)
  tp_tvar : bool;   (* type variable allowed *)
}

let tp_tydecl  = { tp_uni = false; tp_tvar = true ; } (* type decl. *)
let tp_relax   = { tp_uni = true ; tp_tvar = true ; } (* ops/forms/preds *)
let tp_nothing = { tp_uni = false; tp_tvar = false; } (* module type annot. *)
let tp_uni     = { tp_uni = true ; tp_tvar = false; } (* params/local vars. *)

(* -------------------------------------------------------------------- *)
type ismap = (instr list) Mstr.t

(* -------------------------------------------------------------------- *)
let transtcs (env : EcEnv.env) tcs =
  let for1 tc =
    match EcEnv.TypeClass.lookup_opt (unloc tc) env with
    | None -> tyerror tc.pl_loc env (UnknownTypeClass (unloc tc))
    | Some (p, _) -> p                  (* FIXME: TC HOOK *)
  in
    Sp.of_list (List.map for1 tcs)

(* -------------------------------------------------------------------- *)
let transtyvars (env : EcEnv.env) (loc, tparams) =
  let tparams = tparams |> omap
    (fun tparams ->
        let for1 ({ pl_desc = x }) = (EcIdent.create x) in
          if not (List.is_unique (List.map unloc tparams)) then
            tyerror loc env DuplicatedTyVar;
          List.map for1 tparams)
  in
    EcUnify.UniEnv.create tparams

(* -------------------------------------------------------------------- *)
exception TymodCnvFailure of tymod_cnv_failure

type cnvmode = [`Eq | `Sub]

let tymod_cnv_failure e =
  raise (TymodCnvFailure e)

let tysig_item_name = function
  | Tys_function f -> f.fs_name

(* Check that the oracle information of two procedures are compatible. *)
let check_item_compatible env mode (fin,oin) (fout,oout) =
  assert (fin.fs_name = fout.fs_name);

  let check_item_err err =
    tymod_cnv_failure (E_TyModCnv_MismatchFunSig(fin.fs_name,err)) in

  let (iargs, oargs) = (fin.fs_arg, fout.fs_arg) in
  let (ires , ores ) = (fin.fs_ret, fout.fs_ret) in

  (* We check signatures compatibility. *)
  if not (EqTest.for_type env iargs oargs) then
    check_item_err (MF_targs(oargs,iargs));

  if not (EqTest.for_type env ires ores) then
    check_item_err (MF_tres(ores,ires));

  (* We check allowed oracle compatibility. *)
  let norm_allowed oi =
    List.fold_left (fun s f ->
        EcPath.Sx.add (EcEnv.NormMp.norm_xfun env f) s)
      EcPath.Sx.empty (OI.allowed oi) in

  let icalls = norm_allowed oin in
  let ocalls = norm_allowed oout in

  match mode with
  | `Sub ->
    if not (Sx.subset icalls ocalls) then
      let sx = Sx.diff icalls ocalls in
      check_item_err (MF_restr(env, `Sub sx))

  | `Eq  ->
    if not (Sx.equal icalls ocalls) then
      check_item_err (MF_restr(env, `Eq(ocalls, icalls)))

(* -------------------------------------------------------------------- *)
exception RestrErr of mismatch_restr

let re_perror x = raise @@ RestrErr (`Sub x)

let re_eq_perror x = raise @@ RestrErr (`Eq x)

(* Unify the two restriction errors, if any. *)
let to_eq_error e e' =
  match e, e' with
  | None, None -> ()
  | Some (sx,sm), None ->
    re_eq_perror (sx,sm, Sx.empty, Sm.empty)
  | None, Some (sx,sm) ->
    re_eq_perror (Sx.empty, Sm.empty, sx, sm)
  | Some (sx,sm), Some (sx',sm') ->
    re_eq_perror (sx, sm, sx', sm')

let to_unit_map sx = Mx.map (fun _ -> ()) sx

let to_sm sid =
  EcIdent.Sid.fold (fun m sm -> Sm.add (EcPath.mident m) sm) sid Sm.empty

let support env (pr : EcEnv.use option) (r : EcEnv.use use_restr) =
  let memo : Sx.t EcIdent.Hid.t = EcIdent.Hid.create 16 in

  let rec ur_support (supp : Sx.t) ur =
    let supp = EcUtils.omap_dfl (use_support supp) supp ur.ur_pos in
    use_support supp ur.ur_neg

  and use_support (supp : Sx.t) (use : EcEnv.use) =
    let supp = Mx.fold (fun x _ supp -> Sx.add x supp) use.EcEnv.us_pv supp in
    EcIdent.Sid.fold (fun m supp ->
        mident_support supp m
      ) use.EcEnv.us_gl supp

  and mident_support (supp : Sx.t) m =
    try EcIdent.Hid.find memo m with
    | Not_found ->
      let mp = EcPath.mident m in
      let ur  = NormMp.get_restr_use env mp in
      let supp = ur_support supp ur in
      EcIdent.Hid.add memo m supp;
      supp in

  let supp = EcUtils.omap_dfl (use_support Sx.empty) Sx.empty pr in
  ur_support supp r

(* Is [x] allowed in a positive restriction [pr]. *)
let rec p_allowed env (x : EcPath.xpath) (pr : EcEnv.use option) =
  match pr with
  | None -> true
  | Some pr ->
    Mx.mem x pr.EcEnv.us_pv
    || EcIdent.Sid.exists (allowed_m env x) pr.EcEnv.us_gl

(* Is [x] allowed in an abstract module [m] *)
and allowed_m env (x : EcPath.xpath) (m : EcIdent.t) =
  let mp = EcPath.mident m in
  let r  = NormMp.get_restr_use env mp in
  allowed env x r

(* Is [x] allowed in a positive and negative restriction [r]. *)
and allowed env (x : EcPath.xpath) (r : EcEnv.use use_restr) =
  (* [x] is allowed in [r] iff:
     - [x] is directly allowed
     - [x] is allowed in a module allowed in [r] *)
  (p_allowed env x r.ur_pos && not (p_allowed env x (Some r.ur_neg)))

(* Are all elements of [sx] allowed in the positive and negative
   restriciton [r]. *)
let all_allowed env (sx : 'a EcPath.Mx.t) (r : EcEnv.use use_restr) =
  let allow x = allowed env x r in
  let not_allowed = Mx.filter (fun x _ -> not @@ allow x) sx
                    |> to_unit_map in
  if not @@ Mx.is_empty not_allowed then
    re_perror (not_allowed, Sm.empty)

(* Are all elements of [sx] allowed in the union of the positive restriction [pr]
   and the positive and negative restriction [r]. *)
let all_allowed_gen env (sx : 'a EcPath.Mx.t)
    (pr : EcEnv.use option) (r : EcEnv.use use_restr) =
  let allow x = p_allowed env x pr || allowed env x r in
  let not_allowed = Mx.filter (fun x _ -> not @@ allow x) sx
                    |> to_unit_map in
  if not @@ Mx.is_empty not_allowed then
    re_perror (not_allowed, Sm.empty)

(* Are all elements of [sx] allowed in the positive restriciton [pr]. *)
let all_allowed_p env (sx : 'a EcPath.Mx.t) (pr : EcEnv.use option) =
  all_allowed env sx { ur_pos = pr; ur_neg = EcEnv.use_empty }


(* Are all variables allowed in the union of the positive restriction [pr]
   and the positive and negative restriction [r].
   I.e. is [pr] union [r] forbidding nothing.
   Remark: we cannot compute directly the union of [pr] and [r], because
   A union (B \ C) <> (A union B) \ C *)
let rec everything_allowed env
    (pr : EcEnv.use option) (r : EcEnv.use use_restr) : unit =
  match pr, r.ur_pos with
  | None, _ -> ()
  | Some pr, Some rup when EcIdent.Sid.is_empty pr.EcEnv.us_gl
                        && EcIdent.Sid.is_empty rup.EcEnv.us_gl ->
    raise @@ RestrErr (`RevSub None)

  | Some _, Some _ ->
    (* We check whether everybody in the support of [pr] and [r] is allowed,
       and whether a dummy variable (which stands for everybody else) is
       allowed. *)
    let supp = support env pr r in
    let dum =
      let mdum = EcPath.mpath_abs (EcIdent.create "__dummy_ecTyping__") [] in
      EcPath.xpath mdum "__dummy_ecTyping_s__" in
    (* Sanity check: [dum] must be fresh. *)
    assert (not @@ Sx.mem dum supp);
    let supp = Sx.add dum supp in

    all_allowed_gen env supp pr r;

  | Some pr, None ->
    (* In that case, we need [r.ur_neg] to forbid only variables that are
       allowed in [pr], i.e. we require that:
       [r.ur_neg] subset [pr] *)
    try
      all_allowed_p env r.ur_neg.EcEnv.us_pv (Some pr);
      all_mod_allowed env
        r.ur_neg.EcEnv.us_gl (Some pr) (EcModules.ur_full EcEnv.use_empty)
    with RestrErr (`Sub e) -> raise @@ RestrErr (`RevSub (Some e))

(* Are all elements of [sm] allowed the union of the positive restriction
   [pr] and the positive and negative restriction [r]. *)
and all_mod_allowed env (sm : EcIdent.Sid.t)
    (pr : EcEnv.use option) (r : EcEnv.use use_restr) : unit =

  let allow m = mod_allowed env m pr r in
  let not_allowed = EcIdent.Sid.filter (fun m -> not @@ allow m) sm
                    |> to_sm in
  if not @@ Sm.is_empty not_allowed then
    re_perror (Sx.empty, not_allowed)

(* Is [m] directly allowed. This is sound but not complete (hence a negative
   answer does not mean that [m] is forbidden). *)
and direct_mod_allowed
    (m : EcIdent.t) (pr : EcEnv.use option) (r : EcEnv.use use_restr) =
  match pr with
  | None -> true
  | Some pr ->
    if EcIdent.Sid.mem m pr.EcEnv.us_gl
    then true
    else if EcIdent.Sid.is_empty r.ur_neg.EcEnv.us_gl
         && Mx.is_empty r.ur_neg.EcEnv.us_pv
    then match r.ur_pos with
      | None -> true
      | Some rur -> EcIdent.Sid.mem m rur.EcEnv.us_gl
    else false

(* Is [m] allowed in the union of the positive restriction [pr] and the
   positive and negative restriction [r]. *)
and mod_allowed env
    (m : EcIdent.t) (pr : EcEnv.use option) (r : EcEnv.use use_restr) =

  if direct_mod_allowed m pr r
  then true
  else
    let mp = EcPath.mident m in
    let rm  = NormMp.get_restr_use env mp in

    try ur_allowed env rm pr r; true with
      RestrErr _ -> false

(* Is [ur] allowed in the union of the positive restriction [pr] and the
   positive and negative restriction [r]. *)
and ur_allowed env
    (ur : EcEnv.use use_restr)
    (pr : EcEnv.use option) (r : EcEnv.use use_restr) : unit =
  let pr' = match pr with
    | None -> None
    | Some pr -> some @@ EcEnv.use_union pr ur.ur_neg in

  use_allowed env ur.ur_pos pr' r

(* Is [use] allowed in the union of the positive restriction [pr] and the
   positive and negative restriction [r]. *)
and use_allowed env
    (use : EcEnv.use option)
    (pr : EcEnv.use option) (r : EcEnv.use use_restr) : unit =
  (* We have two cases, depending on whether [use] is everybody or not. *)
  match use with
  | None -> everything_allowed env pr r

  | Some urm ->
    all_allowed_gen env urm.EcEnv.us_pv pr r;
    all_mod_allowed env urm.EcEnv.us_gl pr r

(* This only checks the memory restrictions. *)
let _check_mem_restr env (use : EcEnv.use) (restr : mod_restr) =
  let r : EcEnv.use use_restr = NormMp.restr_use env restr in
  use_allowed env (Some use) (Some EcEnv.use_empty) r

(* Check if [mr1] is a a subset of [mr2]. *)
let _check_mem_restr_sub env (mr1 : mod_restr) (mr2 : mod_restr) =
  let r1 = NormMp.restr_use env mr1 in
  let r2 = NormMp.restr_use env mr2 in
  ur_allowed env r1 (Some EcEnv.use_empty) r2

(* Check if [mr1] is equal to [mr2]. *)
let _check_mem_restr_eq env (mr1 : mod_restr) (mr2 : mod_restr) =
  let r1 = NormMp.restr_use env mr1 in
  let r2 = NormMp.restr_use env mr2 in

  let e1 = match ur_allowed env r1 (Some EcEnv.use_empty) r2 with
    | exception (RestrErr (`Sub e1)) -> Some e1
    | () -> None
  and e2 = match ur_allowed env r2 (Some EcEnv.use_empty) r1 with
    | exception (RestrErr (`Sub e2)) -> Some e2
    | () -> None in

    to_eq_error e1 e2

let check_mem_restr_mode mode env sym mr1 mr2 =
  try match mode with
    | `Sub -> _check_mem_restr_sub env mr1 mr2
    | `Eq  -> _check_mem_restr_eq  env mr1 mr2
  with RestrErr err -> tymod_cnv_failure (E_TyModCnv_MismatchRestr (sym,err))

let recast env who f =
  let re x = raise (RestrictionError (env, (who, x))) in
  try f () with
  | RestrErr (`Eq _) -> assert false
  | RestrErr (`Sub e) -> re (`Sub e)
  | RestrErr (`RevSub e) -> re (`RevSub e)

(* This only checks the memory restrictions. *)
let check_mem_restr env mp (use : EcEnv.use) (restr : mod_restr) =
  recast env (RW_mod mp) (fun () -> _check_mem_restr env use restr)

(* This only checks the memory restrictions. *)
let check_mem_restr_fun env xp restr =
  let use = NormMp.fun_use env xp in
  recast env (RW_fun xp) (fun () ->_check_mem_restr env use restr)

(* -------------------------------------------------------------------- *)
let rec check_sig_cnv
    (mode : cnvmode) (env : EcEnv.env) (sin : module_sig) (sout : module_sig) =
  (* Check parameters for compatibility. Parameters names may be
   * different, hence, substitute in [tin.tym_params] types the names
   * of [tout.tym_params] *)

  if List.length sin.mis_params <> List.length sout.mis_params then
    tymod_cnv_failure E_TyModCnv_ParamCountMismatch;

  let bsubst =
    List.fold_left2
      (fun subst (xin, tyin) (xout, tyout) ->
         let tyout = EcSubst.subst_modtype subst tyout in
         begin
           try check_modtype_cnv ~mode env tyout tyin
           with TymodCnvFailure err ->
             tymod_cnv_failure
               (E_TyModCnv_SubTypeArg(xin, tyout, tyin, err))
         end;
         EcSubst.add_module subst xout (EcPath.mident xin))
      EcSubst.empty sin.mis_params sout.mis_params
  in

  let bout = EcSubst.subst_modsig_body bsubst sout.mis_body
  and rout = EcSubst.subst_oracle_infos bsubst sout.mis_oinfos in

  (* Check for body inclusion:
   * - functions inclusion with equal signatures + included oracles. *)
  let env = EcEnv.Mod.bind_params sin.mis_params env in

  let check_for_item (Tys_function fout : module_sig_body_item) =
    let o_name = fout.fs_name in

    let i_item =
      List.ofind
        (fun i_item ->
           (tysig_item_name i_item) = o_name)
        sin.mis_body
    in
    match i_item with
    | None -> tymod_cnv_failure (E_TyModCnv_MissingComp o_name)
    | Some (Tys_function fin) ->
      let oin = EcSymbols.Msym.find fin.fs_name sin.mis_oinfos in
      let oout = EcSymbols.Msym.find fout.fs_name rout in
      check_item_compatible env mode (fin,oin) (fout,oout)
  in
  List.iter check_for_item bout;

  if mode = `Eq then begin
    List.iter
      (fun i_item ->
         let i_name = tysig_item_name i_item in
         let b =
           List.exists
             (fun o_item ->
                (tysig_item_name o_item) = i_name)
             bout
         in
         if not b then
           tymod_cnv_failure (E_TyModCnv_MissingComp i_name))
      sin.mis_body
  end

and check_modtype_cnv
  ?(mode : cnvmode = `Eq) (env : EcEnv.env) (tyin : module_type) (tyout : module_type)
=
  let sin = EcEnv.ModTy.sig_of_mt env tyin in
  let sout = EcEnv.ModTy.sig_of_mt env tyout in
  check_sig_cnv mode env sin sout

let check_sig_mt_cnv (env : EcEnv.env) (sin : module_sig) (tyout : module_type) =
  let sout = EcEnv.ModTy.sig_of_mt env tyout in
  check_sig_cnv `Sub env sin sout

(* -------------------------------------------------------------------- *)
let check_modtype (env : EcEnv.env) (mp : mpath) (ms : module_sig) ((mty, mr) : mty_mr) =
  let use = NormMp.mod_use env mp in
  check_mem_restr env mp use mr;
  check_sig_mt_cnv env ms mty

(* -------------------------------------------------------------------- *)
let split_msymb (env : EcEnv.env) (msymb : pmsymbol located) =
  let (top, args, sm) =
    try
      let (r, (x, args), sm) =
        List.find_pivot (fun (_,args) -> args <> None) msymb.pl_desc
      in
        (List.rev_append r [x, None], args, sm)
    with Not_found ->
      (msymb.pl_desc, None, [])
  in

  let (top, sm) =
    let ca (x, args) =
      if args <> None then
        tyerror msymb.pl_loc env
          (InvalidModAppl (MAE_WrongArgCount(0, List.length (oget args))));
      x
    in
      (List.map ca top, List.map ca sm)
  in
    (top, args, sm)

(* -------------------------------------------------------------------- *)
let rec trans_msymbol (env : EcEnv.env) (msymb : pmsymbol located) =
  let loc = msymb.pl_loc in
  let (top, args, sm) = split_msymb env msymb in

  let to_qsymbol l =
    match List.rev l with
    | [] -> assert false
    | x::qn ->
        { pl_desc = (List.rev_map unloc qn, unloc x);
          pl_loc  = x.pl_loc; }
  in

  let top_qname = to_qsymbol (top@sm) in

  let (top_path, {EcEnv.sp_target = mod_expr; EcEnv.sp_params = (spi, params)}) =
    match EcEnv.Mod.sp_lookup_opt top_qname.pl_desc env with
    | None ->
        tyerror top_qname.pl_loc env (UnknownModName top_qname.pl_desc)
    | Some (mp, me, _) -> (mp, me)
  in

  let (params, istop) =
    match top_path.EcPath.m_top with
    | `Concrete (_, Some sub) ->
        if mod_expr.me_params <> [] then
          assert false;
        if args <> None then
          if not (EcPath.p_size sub = List.length sm) then
            tyerror loc env
              (InvalidModAppl (MAE_WrongArgCount(EcPath.p_size sub,
                                                List.length sm)));
        (params, false)

    | `Concrete (p, None) ->
        if (params <> []) || ((spi+1) <> EcPath.p_size p) then
          assert false;
        (mod_expr.me_params, true)

    | `Local _m ->
        if (params <> []) || spi <> 0 then
          assert false;
        (mod_expr.me_params, true)
  in

  let args = args |> omap (List.map (trans_msymbol env)) in

  match args with
  | None ->
    if not istop && params <> [] then
      tyerror loc env (InvalidModAppl MAE_AccesSubModFunctor);

    ((top_path,loc), { miss_params = mod_expr.me_params;
                       miss_body   = mod_expr.me_sig_body; } )

  | Some args ->
      let lena = List.length args in
      let lenp = List.length params in
      if lena > lenp then
        tyerror loc env (InvalidModAppl (MAE_WrongArgCount(lenp, lena)));

      let params, remn = List.takedrop lena params in

      let args = List.map2
        (fun (x,tp) ((a,loc),ta_smpl) ->
          try
            let ta = NormMp.sig_of_mp env a in

            (* Sanity check *)
            if List.length ta_smpl.miss_params <> List.length ta.mis_params then
              assert false;

            let env = EcEnv.Mod.bind_param x tp env in
            check_sig_mt_cnv env ta tp; a
          with TymodCnvFailure error ->
            tyerror loc env (InvalidModAppl (MAE_InvalidArgType(a, error))))
        params args in

      let subst =
          List.fold_left2
            (fun s (x,_) a -> EcSubst.add_module s x a)
            EcSubst.empty params args
      in

      let body = EcSubst.subst_modsig_body subst mod_expr.me_sig_body in

      ((EcPath.mpath top_path.EcPath.m_top args, loc),
       { miss_params = remn;
         miss_body   = body; })

let trans_msymbol env msymb =
  let ((m,_),mt) = trans_msymbol env msymb in
  (m,mt)

(* -------------------------------------------------------------------- *)
let rec transty (tp : typolicy) (env : EcEnv.env) ue ty =
  match ty.pl_desc with
  | PTunivar ->
      if   tp.tp_uni
      then UE.fresh ue
      else tyerror ty.pl_loc env UniVarNotAllowed

  | PTvar s ->
      if tp.tp_tvar then
        try tvar (UE.getnamed ue s.pl_desc)
        with _ -> tyerror s.pl_loc env (UnboundTypeParameter s.pl_desc)
      else
        tyerror s.pl_loc env TypeVarNotAllowed;

  | PTtuple tys   ->
      ttuple (transtys tp env ue tys)

  | PTnamed { pl_desc = name } -> begin
      match EcEnv.Ty.lookup_opt name env with
      | None ->
          tyerror ty.pl_loc env (UnknownTypeName name)

      | Some (p, tydecl) ->
          if tydecl.tyd_params <> [] then begin
            let nargs = List.length tydecl.tyd_params in
              tyerror ty.pl_loc env (InvalidTypeAppl (name, nargs, 0))
          end;
          tconstr p []
      end

  | PTfun(ty1,ty2) ->
      tfun (transty tp env ue ty1) (transty tp env ue ty2)

  | PTapp ({ pl_desc = name }, tyargs) ->
    begin match EcEnv.Ty.lookup_opt name env with
    | None ->
      tyerror ty.pl_loc env (UnknownTypeName name)

    | Some (p, tydecl) ->
      let nargs    = List.length tyargs in
      let expected = List.length tydecl.tyd_params in

      if nargs <> expected then
        tyerror ty.pl_loc env (InvalidTypeAppl (name, expected, nargs));

      let tyargs = transtys tp env ue tyargs in
      tconstr p tyargs
    end
  | PTglob gp ->
    let mo,_ = trans_msymbol env gp in
    EcEnv.NormMp.norm_tglob env mo

and transtys tp (env : EcEnv.env) ue tys =
  List.map (transty tp env ue) tys

let transty_for_decl env ty =
  let ue = UE.create (Some []) in
    transty tp_nothing env ue ty

(* -------------------------------------------------------------------- *)
let transpattern1 env ue (p : EcParsetree.plpattern) =
  match p.pl_desc with
  | LPSymbol { pl_desc = x } ->
      let ty = UE.fresh ue in
      let x  = EcIdent.create x in
      (LSymbol (x,ty), ty)

  | LPTuple xs ->
      let xs = unlocs xs in
      if not (List.is_unique xs) then
        tyerror p.pl_loc env NonLinearPattern
      else
        let xs     = List.map ident_of_osymbol xs in
        let subtys = List.map (fun _ -> UE.fresh ue) xs in
        (LTuple (List.combine xs subtys), ttuple subtys)

  | LPRecord fields ->
      let xs = List.map (unloc -| snd) fields in
      if not (List.is_unique xs) then
        tyerror p.pl_loc env NonLinearPattern;

      let fields =
        let for1 (name, v) =
          let filter = fun _ op -> EcDecl.is_proj op in
          let fds    = EcUnify.select_op ~filter None env (unloc name) ue ([], None) in
            match List.ohead fds with
            | None ->
              let exn = UnknownRecFieldName (unloc name) in
                tyerror name.pl_loc env exn

            | Some ((fp, _tvi), opty, subue, _) ->
              let field = oget (EcEnv.Op.by_path_opt fp env) in
              let (recp, fieldidx, _) = EcDecl.operator_as_proj field in
                EcUnify.UniEnv.restore ~src:subue ~dst:ue;
                ((recp, fieldidx), opty, (name, v))
        in
          List.map for1 fields in

      let recp = Sp.of_list (List.map (fst -| proj3_1) fields) in
      let recp =
        match Sp.elements recp with
        | []        -> assert false
        | [recp]    -> recp
        | p1::p2::_ -> tyerror p.pl_loc env (MixingRecFields (p1, p2))
      in

      let recty  = oget (EcEnv.Ty.by_path_opt recp env) in
      let rec_   = snd (oget (EcDecl.tydecl_as_record recty)) in
      let reccty = tconstr recp (List.map tvar recty.tyd_params) in
      let reccty, rectvi = EcUnify.UniEnv.openty ue recty.tyd_params None reccty in
      let fields =
        List.fold_left
          (fun map (((_, idx), _, _) as field) ->
             if Mint.mem idx map then
               let name = fst (List.nth rec_ idx) in
               let exn  = DuplicatedRecFieldName name in
                 tyerror p.pl_loc env exn
             else
               Mint.add idx field map)
          Mint.empty fields in

      let fields =
        List.init (List.length rec_)
          (fun i ->
            match Mint.find_opt i fields with
            | None ->
                let pty = EcUnify.UniEnv.fresh ue in
                let fty = snd (List.nth rec_ i) in
                let fty, _ =
                  EcUnify.UniEnv.openty ue recty.tyd_params
                    (Some (EcUnify.TVIunamed rectvi)) fty
                in
                  (try  EcUnify.unify env ue pty fty
                   with EcUnify.UnificationFailure _ -> assert false);
                  (None, pty)

            | Some (_, opty, (_, v)) ->
                let pty = EcUnify.UniEnv.fresh ue in
                (try  EcUnify.unify env ue (tfun reccty pty) opty
                 with EcUnify.UnificationFailure _ -> assert false);
                (Some (EcIdent.create (unloc v)), pty))
      in
        (LRecord (recp, fields), reccty)

let transpattern env ue (p : EcParsetree.plpattern) =
  match transpattern1 env ue p with
  | (LSymbol (x, ty)) as p, _ ->
      (EcEnv.Var.bind_local x ty env, p, ty)

  | LTuple xs as p, ty ->
      (EcEnv.Var.bind_locals xs env, p, ty)

  | LRecord (_, xs) as p, ty ->
      let xs = List.pmap (function
        | (None, _)    -> None
        | (Some x, ty) -> Some (x, ty)) xs
      in
        (EcEnv.Var.bind_locals xs env, p, ty)

(* -------------------------------------------------------------------- *)
let transtvi env ue tvi =
  match tvi.pl_desc with
  | TVIunamed lt ->
      EcUnify.TVIunamed (List.map (transty tp_relax env ue) lt)

  | TVInamed lst ->
      let add locals (s, t) =
        if List.exists (fun (s', _) -> unloc s = unloc s') locals then
          tyerror tvi.pl_loc env DuplicatedTyVar;
        (s, transty tp_relax env ue t) :: locals
      in

      let lst = List.fold_left add [] lst in
        EcUnify.TVInamed (List.rev_map (fun (s,t) -> unloc s, t) lst)

let rec destr_tfun env ue tf =
  match tf.ty_node with
  | Tunivar id -> begin
      let tf' = UE.repr ue tf in
        match tf == tf' with
        | false -> destr_tfun env ue tf'
        | true  ->
            let ty1 = UE.fresh ue in
            let ty2 = UE.fresh ue in
              EcUnify.unify env ue (tuni id) (tfun ty1 ty2);
              Some (ty1, ty2)
  end

  | Tfun (ty1, ty2) -> Some (ty1, ty2)

  | Tconstr (p, tys) when EcEnv.Ty.defined p env ->
      destr_tfun env ue (EcEnv.Ty.unfold p tys env)

  | _ -> None

let rec ty_fun_app loc env ue tf targs =
  match targs with
  | [] -> tf
  | t1 :: targs -> begin
      match destr_tfun env ue tf with
      | None -> tyerror loc env NotAFunction
      | Some (dom, codom) ->
        unify_or_fail env ue t1.pl_loc ~expct:dom t1.pl_desc;
        let loc = EcLocation.merge loc t1.pl_loc in
        ty_fun_app loc env ue codom targs
  end

(* -------------------------------------------------------------------- *)
let trans_binding env ue bd =
  let trans_bd1 env (xs, pty) =
    let ty  = transty tp_relax env ue pty in
    let xs  = List.map (fun x -> ident_of_osymbol (unloc x), ty) xs in
    let env = EcEnv.Var.bind_locals xs env in
    env, xs in
  let env, bd = List.map_fold trans_bd1 env bd in
  let bd = List.flatten bd in
  env, bd

(* -------------------------------------------------------------------- *)
let trans_record env ue (subtt, proj) (loc, b, fields) =
  let fields =
    let for1 rf =
      let filter = fun _ op -> EcDecl.is_proj op in
      let tvi    = rf.rf_tvi |> omap (transtvi env ue) in
      let fds    = EcUnify.select_op ~filter tvi env (unloc rf.rf_name) ue ([], None) in
        match List.ohead fds with
        | None ->
            let exn = UnknownRecFieldName (unloc rf.rf_name) in
              tyerror rf.rf_name.pl_loc env exn

        | Some ((fp, _tvi), opty, subue, _) ->
            let field = oget (EcEnv.Op.by_path_opt fp env) in
            let (recp, fieldidx, _) = EcDecl.operator_as_proj field in
              EcUnify.UniEnv.restore ~src:subue ~dst:ue;
              ((recp, fieldidx), opty, rf)
    in
      List.map for1 fields in

  let recp = Sp.of_list (List.map (fst -| proj3_1) fields) in
  let recp =
    match Sp.elements recp with
    | []        -> assert false
    | [recp]    -> recp
    | p1::p2::_ -> tyerror loc env (MixingRecFields (p1, p2))
  in

  let recty  = oget (EcEnv.Ty.by_path_opt recp env) in
  let rec_   = snd (oget (EcDecl.tydecl_as_record recty)) in
  let reccty = tconstr recp (List.map tvar recty.tyd_params) in
  let reccty, rtvi = EcUnify.UniEnv.openty ue recty.tyd_params None reccty in
  let tysopn = Tvar.init recty.tyd_params rtvi in

  let fields =
    List.fold_left
      (fun map (((_, idx), _, _) as field) ->
         if Mint.mem idx map then
           let name = fst (List.nth rec_ idx) in
           let exn  = DuplicatedRecFieldName name in
           tyerror loc env exn
         else
           Mint.add idx field map)
      Mint.empty fields in

  let dflrec =
    let doit f =
      let (dfl, dflty) = subtt f in
      unify_or_fail env ue f.pl_loc ~expct:reccty dflty; dfl
    in b |> omap doit
  in

  let fields =
    let get_field i name rty =
      match Mint.find_opt i fields with
      | Some (_, opty, rf) ->
          `Set (opty, rf.rf_value)

      | None ->
          match dflrec with
          | None   -> tyerror loc env (MissingRecField name)
          | Some _ -> `Dfl (Tvar.subst tysopn rty, name)
    in List.mapi (fun i (name, rty) -> get_field i name rty) rec_
  in

  let fields =
    let for1 = function
      | `Set (opty, value) ->
          let pty = EcUnify.UniEnv.fresh ue in
          (try  EcUnify.unify env ue (tfun reccty pty) opty
           with EcUnify.UnificationFailure _ -> assert false);
          let e, ety = subtt value in
          unify_or_fail env ue value.pl_loc ~expct:pty ety;
          (e, pty)

      | `Dfl (rty, name) ->
          let nm = oget (EcPath.prefix recp) in
          (proj (nm, name, (rtvi, reccty), rty, oget dflrec), rty)

    in
      List.map for1 fields
  in

  let ctor =
    EcPath.pqoname
      (EcPath.prefix recp)
      (Printf.sprintf "mk_%s" (EcPath.basename recp))
  in
    (ctor, fields, (rtvi, reccty))

(* -------------------------------------------------------------------- *)
let trans_branch ~loc env ue gindty ((pb, body) : ppattern * _) =
  let filter = fun _ op -> EcDecl.is_ctor op in
  let PPApp ((cname, tvi), cargs) = pb in
  let tvi = tvi |> omap (transtvi env ue) in
  let cts = EcUnify.select_op ~filter tvi env (unloc cname) ue ([], None) in

  match cts with
  | [] ->
      tyerror cname.pl_loc env (InvalidMatch FXE_CtorUnk)

  | _ :: _ :: _ ->
      tyerror cname.pl_loc env (InvalidMatch FXE_CtorAmbiguous)

  | [(cp, tvi), opty, subue, _] ->
      let ctor = oget (EcEnv.Op.by_path_opt cp env) in
      let (indp, ctoridx) = EcDecl.operator_as_ctor ctor in
      let indty = oget (EcEnv.Ty.by_path_opt indp env) in
      let ind = (oget (EcDecl.tydecl_as_datatype indty)).tydt_ctors in
      let ctorsym, ctorty = List.nth ind ctoridx in

      let args_exp = List.length ctorty in
      let args_got = List.length cargs in

      if args_exp <> args_got then begin
        tyerror cname.pl_loc env (InvalidMatch
          (FXE_CtorInvalidArity (snd (unloc cname), args_exp, args_got)))
      end;

      let cargs_lin = List.pmap (fun o -> omap unloc (unloc o)) cargs in

      if not (List.is_unique cargs_lin) then
        tyerror cname.pl_loc env (InvalidMatch FXE_MatchNonLinear);

      EcUnify.UniEnv.restore ~src:subue ~dst:ue;

      let ctorty =
        let tvi = Some (EcUnify.TVIunamed tvi) in
          fst (EcUnify.UniEnv.opentys ue indty.tyd_params tvi ctorty) in
      let pty = EcUnify.UniEnv.fresh ue in

      (try  EcUnify.unify env ue (toarrow ctorty pty) opty
       with EcUnify.UnificationFailure _ -> assert false);

      unify_or_fail env ue loc ~expct:pty gindty;

      let create o = EcIdent.create (omap_dfl unloc "_" o) in
      let pvars = List.map (create -| unloc) cargs in
      let pvars = List.combine pvars ctorty in

      (ctorsym, (pvars, body))

(* -------------------------------------------------------------------- *)
let trans_match ~loc env ue (gindty, gind) pbs =
  let pbs = List.map (trans_branch ~loc env ue gindty) pbs in
  (* the left-hand-sides of pbs are a subset of the left hand sides
     of gind.tydt_ctors (with the order perhaps different) *)

  if List.length pbs < List.length gind.tydt_ctors then
    tyerror loc env (InvalidMatch FXE_MatchPartial);

  if List.has_dup ~cmp:(fun x y -> compare (fst x) (fst y)) pbs then
    tyerror loc env (InvalidMatch FXE_MatchDupBranches);
  (* the left-hand-sides of pbs are exactly the left-hand sides
     of gind.tydt_ctors (with the order perhaps different) *)

  let pbs = Msym.of_list pbs in

  List.map
    (fun (x, _) -> oget (Msym.find_opt x pbs))
    gind.tydt_ctors

(* -------------------------------------------------------------------- *)
let trans_if_match ~loc env ue (gindty, gind) (c, b1, b2) =
  let (c, (cargs, b1)) = trans_branch ~loc env ue gindty (c, b1) in

  List.map
    (fun (x, xargs) ->
      if sym_equal c x then
        (cargs, Some b1)
      else
        (* Create a pattern C _ _ ... for each constructor *)
        let wilds = List.map (fun _ -> EcLocation.mk_loc loc None) xargs in
        let pat = PPApp ((EcLocation.mk_loc loc ([], x), None), wilds) in
        let b2 =
          (match b2 with
          | None -> []
          | Some b2 -> b2
        ) in
        let (_, (xargs, b2)) = trans_branch ~loc env ue gindty (pat, b2) in
        (xargs, Some b2)
    )
    gind.tydt_ctors

(*-------------------------------------------------------------------- *)

let var_or_proj fvar fproj pv ty =
  match pv with
  | `Var pv -> fvar pv ty
  | `Proj(pv, ap) -> fproj (fvar pv ap.arg_ty) ap.arg_pos ty

(* -------------------------------------------------------------------- *)
let lookup_module_type (env : EcEnv.env) (name : pqsymbol) =
  match EcEnv.ModTy.lookup_opt (unloc name) env with
  | None   -> tyerror name.pl_loc env (UnknownTyModName (unloc name))
  | Some x -> x

let lookup_fun env name =
  try
    EcEnv.Fun.lookup name.pl_desc env
  with EcEnv.LookupFailure _ ->
    tyerror name.pl_loc env (UnknownFunName name.pl_desc)

(* -------------------------------------------------------------------- *)
let transmodtype (env : EcEnv.env) (modty : pmodule_type) =
  let (p, { tms_sig = sig_ }) = lookup_module_type env modty in
  let modty = {                         (* eta-normal form *)
    mt_params = sig_.mis_params;
    mt_name   = p;
    mt_args   = List.map (EcPath.mident -| fst) sig_.mis_params;
  } in
    (modty, sig_)

let transcall transexp env ue loc fsig args =
  let targ = fsig.fs_arg in

  let process_args tys =
    if List.length args <> List.length tys then
      tyerror loc env (InvalidFunAppl FAE_WrongArgCount);
    List.map2
      (fun a ty ->
        let loc = a.pl_loc in
        let a, aty = transexp a in
        unify_or_fail env ue loc ~expct:ty aty; a) args tys
  in

  let args =
    match List.length args with
    | 0 ->
        if not (EcReduction.EqTest.for_type env targ tunit) then
          tyerror loc env (InvalidFunAppl FAE_WrongArgCount);
        []

    | _ when EcReduction.EqTest.for_type env targ tunit ->
        tyerror loc env (InvalidFunAppl FAE_WrongArgCount);

    | 1 -> process_args [targ]

    | _ ->
      let lty =
        match (EcEnv.Ty.hnorm targ env).ty_node with
        | Ttuple lty -> lty
        | _ -> [targ] in
      process_args lty

  in
    (args, fsig.fs_ret)

(* -------------------------------------------------------------------- *)
let trans_gamepath (env : EcEnv.env) gp =
  let loc = gp.pl_loc in

  let modsymb = List.map (unloc -| fst) (fst (unloc gp))
  and funsymb = unloc (snd (unloc gp)) in
  let xp =
    match EcEnv.Fun.sp_lookup_opt (modsymb, funsymb) env with
    | None -> tyerror gp.pl_loc env (UnknownFunName (modsymb, funsymb))
    | Some (xp,_) -> xp
  in
    match modsymb with
    | [] -> xp
    | _ ->
      let (mpath, _sig) = trans_msymbol env (mk_loc loc (fst (unloc gp))) in
        if _sig.miss_params <> [] then
          tyerror gp.pl_loc env (UnknownFunName (modsymb, funsymb));
        EcPath.xpath mpath funsymb

(* -------------------------------------------------------------------- *)
let trans_oracle (env : EcEnv.env) (m,f) =
  let msymbol = mk_loc (loc m) [m,None] in
  let (mpath, sig_) = trans_msymbol env msymbol in

  let () = match mpath.m_top with
    | `Local _ -> ()
    | `Concrete _ ->
      tyerror (loc m) env (ModuleNotAbstract (unloc m)) in

  let fmem = List.exists (fun (Tys_function fs) ->
      fs.fs_name = unloc f) sig_.miss_body in
  if not fmem then
    tyerror (loc f) env (UnknownFunName ([unloc m],unloc f));

  EcPath.xpath mpath (unloc f)

(* -------------------------------------------------------------------- *)
let trans_topmsymbol env gp =
  (* FIXME *)
  let (mp,_) = trans_msymbol env gp in
  let top = EcPath.m_functor mp in
  let mp = EcPath.m_apply top mp.EcPath.m_args in
  mp

(* -------------------------------------------------------------------- *)
(* Check that a gamepath can be seen as a qsymbol, by verifying that there
   is no applied functor in the path. *)
let pgamepath_to_pqsymbol (v : pgamepath) : pqsymbol option =
  let exception NotAQSymbol in
  let rec pmsymbol_to_qsymbol (m : pmsymbol) =
    match m with
    | [] -> []
    | (a, None) :: m -> (unloc a) :: pmsymbol_to_qsymbol m
    | (_, Some _) :: _ -> raise NotAQSymbol in

  let m,s = unloc v in
  try mk_loc (loc v) (pmsymbol_to_qsymbol m, unloc s)
        |> some
  with NotAQSymbol -> None

(* -------------------------------------------------------------------- *)
let transmem env m =
  match EcEnv.Memory.lookup (unloc m) env with
  | None ->
      tyerror m.pl_loc env (UnknownMemName (unloc m))

  | Some me ->
(*      if (EcMemory.memtype me) <> None then
        tyerror m.pl_loc env (InvalidMem (unloc m, MAE_IsConcrete)); *)
      (fst me)

(* -------------------------------------------------------------------- *)
let transpvar env side p =
  match EcEnv.Var.lookup_progvar_opt ~side (unloc p) env with
  | Some (`Var p, _) -> p
  | _ -> tyerror p.pl_loc env (UnknownProgVar (unloc p, side))

(* -------------------------------------------------------------------- *)
module PFS : sig
  type pfstate

  val create : unit -> pfstate

  val set_memused : pfstate -> unit
  val get_memused : pfstate -> bool
  val isforced    : pfstate -> bool
  val new_memused : ('a -> 'b) -> force:bool -> pfstate -> 'a -> bool * 'b
end = struct
  type pfstate1 = {
    pfa_memused : bool;
    pfa_forced  : bool;
  }

  type pfstate = pfstate1 ref

  let create1 ~(force : bool) : pfstate1 =
    { pfa_memused = false; pfa_forced = force; }

  let create () : pfstate =
    ref (create1 ~force:false)

  let set_memused (state : pfstate) =
    state := { !state with pfa_memused = true }

  let get_memused (state : pfstate) =
    (!state).pfa_memused

  let isforced (state : pfstate) =
    (!state).pfa_forced

  let new_memused (f : 'a -> 'b) ~(force : bool) (state : pfstate) (x : 'a) =
    let old  = !state in
    let aout = (state := create1 ~force; f x) in
    let new_ = get_memused state in
    state := old; (new_, aout)
end

(* -------------------------------------------------------------------- *)
let form_of_opselect
  (env, ue) loc ((sel, ty, subue, _) : OpSelect.gopsel) args
=
  EcUnify.UniEnv.restore ~src:subue ~dst:ue;

  let esig  = List.map (lmap f_ty) args in
  let args  = List.map unloc args in
  let codom = ty_fun_app loc env ue ty esig in

  let op, args =
    match sel with
    | `Nt (lazy (bds, body)) ->
         let nbds  = List.length bds in
         let nargs = List.length args in

         let ((tosub, args), flam) =
           if nbds <= nargs then
             (List.split_at nbds args, [])
           else
             let xs = snd (List.split_at nargs bds) in
             let xs = List.map (fst_map EcIdent.fresh) xs in
             ((args @ List.map (curry f_local) xs, []), xs) in

         let flam  = List.map (snd_map gtty) flam in
         let body = match (EcEnv.Memory.get_active_ss env) with
        | None -> form_of_expr body
        | Some me -> (ss_inv_of_expr me body).inv in
         let lcmap = List.map2 (fun (x, _) y -> (x, y)) bds tosub in
         let subst = Fsubst.f_subst_init ~freshen:true () in
         let subst =
           List.fold_left (fun s -> curry (Fsubst.f_bind_local s)) subst lcmap
         in (f_lambda flam (Fsubst.f_subst subst body), args)

    | (`Op _ | `Lc _ | `Pv _) as sel -> let op = match sel with
      | `Op (p, tys) -> f_op p tys ty
      | `Lc id       -> f_local id ty
      | `Pv (me, pv) ->
        var_or_proj (fun x ty -> (f_pvar x ty (oget me)).inv) f_proj pv ty

    in (op, args)

  in 
  f_app op args codom

(* -------------------------------------------------------------------- *)

(* LvMap (op, x, e, ty)
 * - op is the map-set operator
 * - x  is the map to be updated
 * - e  is the index to update
 * - ty is the type of the value [x] *)

type lvmap = (path * ty list) *  prog_var * expr * ty

type lVAl =
  | Lval  of lvalue
  | LvMap of lvmap

let i_asgn_lv (_loc : EcLocation.t) (_env : EcEnv.env) lv e =
  match lv with
  | Lval lv -> i_asgn (lv, e)
  | LvMap ((op,tys), x, ei, ty) ->
    let op = e_op op tys (toarrow [ty; ei.e_ty; e.e_ty] ty) in
    i_asgn (LvVar (x,ty), e_app op [e_var x ty; ei; e] ty)

let i_rnd_lv loc env lv e =
  match lv with
  | Lval lv -> i_rnd (lv, e)
  | LvMap _ -> tyerror loc env LvMapOnNonAssign

let i_call_lv loc env lv f args =
  match lv with
  | Lval lv -> i_call (Some lv, f, args)
  | LvMap _ -> tyerror loc env LvMapOnNonAssign

(* -------------------------------------------------------------------- *)
let top_is_mem_binding pf = match pf with
  | PFforall (bds,_)  | PFexists (bds,_) ->
    List.exists (fun (_,bd) ->
        match bd with PGTY_Mem _ -> true | _ -> false
      ) bds

  | PFhoareF   _
  | PFequivF   _
  | PFeagerF   _
  | PFprob     _
  | PFBDhoareF _
  | PFehoareF  _ -> true

  | PFhole -> true

  | PFmatch   _
  | PFcast    _
  | PFint     _
  | PFdecimal _
  | PFtuple   _
  | PFident   _
  | PFref     _
  | PFmem     _
  | PFside    _
  | PFapp     _
  | PFif      _
  | PFlet     _
  | PFlambda  _
  | PFrecord  _
  | PFproj    _
  | PFproji   _
  | PFglob    _
  | PFeqveq   _
  | PFeqf     _
  | PFlsless  _
  | PFscope   _ -> false


let f_or_mod_ident_loc : f_or_mod_ident -> EcLocation.t = function
  | FM_FunOrVar x -> loc x
  | FM_Mod      x -> loc x

(* -------------------------------------------------------------------- *)
let trans_restr_mem env (r_mem : pmod_restr_mem) =

  let neg_started = ref false in

  (* If there is one positive restriction, then we do not have +all mem *)
  let m_add_pos loc mr x =
    if !neg_started then tyerror loc env PositiveShouldBeBeforeNegative;
    let ur_pos =
      match mr.ur_pos with
      | None    -> Some(Sx.empty, Sm.singleton x)
      | Some (sx, sm) -> Some(sx, Sm.add x sm) in
    { mr with ur_pos } in

  let x_add_pos loc mr x =
    if !neg_started then tyerror loc env PositiveShouldBeBeforeNegative;
    let ur_pos =
      match mr.ur_pos with
      | None    -> Some (Sx.singleton x, Sm.empty)
      | Some (sx, sm) -> Some(Sx.add x sx, sm) in
    { mr with ur_pos } in

  let m_add_neg mr x =
    neg_started := true;
    let ur_neg =
      let (sx, sm) = mr.ur_neg in
      sx, Sm.add x sm in
    { mr with ur_neg } in

  let x_add_neg mr x =
    neg_started := true;
    let ur_neg =
      let (sx, sm) = mr.ur_neg in
      Sx.add x sx, sm in
    { mr with ur_neg } in

  List.fold_left (fun mr el ->
      let x = match el with PMPlus x | PMMinus x | PMDefault x -> x in
      let xloc = f_or_mod_ident_loc x in
      let sign = match el with
        | PMPlus _    -> `Plus
        | PMMinus _   -> `Minus
        | PMDefault _ ->
          if EcGState.get_old_mem_restr (EcEnv.gstate env) then
            `Minus
          else
            tyerror xloc env NoDefaultMemRestr
      in

      match x with
      | FM_Mod m ->
        let m = trans_topmsymbol env m in
        if sign = `Plus
        then m_add_pos xloc mr m
        else m_add_neg mr m

      | FM_FunOrVar vf ->
        match pgamepath_to_pqsymbol vf with
        | None -> tyerror (loc vf) env InvalidVar
        | Some v ->
          let xp = match EcEnv.Var.lookup_progvar_opt (unloc v) env with
            | None -> tyerror (loc vf) env (UnknownModVar (unloc v))
            | Some (`Var pv,_) when is_glob pv -> get_glob pv
            | Some _ -> assert false in
          if sign = `Plus
          then x_add_pos xloc mr xp
          else x_add_neg mr xp )
    mr_empty
    r_mem

(* -------------------------------------------------------------------- *)
(* See [trans_restr_fun] for the requirements on [env], [env_in], [params]. *)
let trans_restr_oracle_calls env env_in (params : Sm.t) = function
    | None ->
      let do_one mp calls =
        let me, _ = EcEnv.Mod.by_mpath mp env_in in
        if me.me_params <> [] then calls
        else
          let fs = List.map (fun (Tys_function fsig) ->
              EcPath.xpath mp fsig.fs_name) me.me_sig_body
          in
          fs@calls
      in
      Sm.fold do_one params []
    | Some pfd_uses ->
      List.map (fun name ->
          let s_env = if name.inp_in_params then env_in else env in
          let qname = name.inp_qident in

          let f = fst (lookup_fun s_env qname) in
          let p = f.EcPath.x_top in
          if not (Sm.mem p params) then
            tyerror qname.pl_loc env (FunNotInModParam qname.pl_desc);
          f)
        pfd_uses

(* -------------------------------------------------------------------- *)
(* Oracles restrictions for a function.
 * - [params] must be the set of parameters on the module being typed.
 * - [env] is the environment the restriction is being typed on.
 * - [env_in] is [env] where the module parameters [params] are binded.
 * Remark: [env] and [env_in] can be the same, e.g. in:
 * 'module type A (B : T) {some restriction} = { ... }'
 * And they can be different, e.g. in:
 * 'forall (A <: T) (B <: S {some restriction)), ...'
 * Here, the parameter of the functor [S] are not binded in [env], but must be
 * binded in [env_in]. *)
let rec trans_restr_fun env env_in (params : Sm.t) (r_el : pmod_restr_el) =
  let name = unloc r_el.pmre_name in
  let r_orcls = trans_restr_oracle_calls env env_in params r_el.pmre_orcls in
  (name, r_orcls)

(* See [trans_restr_fun] for the requirements on [env], [env_in], [params]. *)
and transmod_restr env (mr : pmod_restr) =
  trans_restr_mem env mr.pmr_mem

(* -------------------------------------------------------------------- *)
(* Return the module type updated with some restriction.
 * Remark: the module type has not been entered. *)
and trans_restr_for_modty env (modty : module_type) (pmr : pmod_restr option) =
  let mr =
    match pmr with
    | None -> mr_empty
    | Some pmr -> transmod_restr env pmr in
  (modty, mr)

(* -------------------------------------------------------------------- *)
and transmodsig (env : EcEnv.env) (inft : pinterface) =
  let Pmty_struct modty = inft.pi_sig in

  let margs =
    List.map (fun (x, i) ->
      (EcIdent.create (unloc x), fst (transmodtype env i)))
      modty.pmsig_params
  in
  let params =
    List.fold_left (fun sa (x,_) -> Sm.add (EcPath.mident x) sa) Sm.empty margs
  in
  let env = EcEnv.Mod.enter (unloc inft.pi_name) margs env in

  (* We compute the body of the signature, and the restrictions given at
     function declarations. *)
  let body, ois = transmodsig_body env params modty.pmsig_body in

  assert (Msym.cardinal ois = List.length body);

  let mis =
    { mis_params = margs;
      mis_body   = body;
      mis_oinfos = ois; } in

  { tms_sig = mis; tms_loca = inft.pi_locality }

(* -------------------------------------------------------------------- *)
and transmodsig_body
  (env : EcEnv.env) (sa : Sm.t) (is : pmodule_sig_struct_body)
=

  let names = ref [] in

  let transsig1 ois = function
    | `FunctionDecl f ->
      let name = f.pfd_name in
      names := name::!names;
      let tyargs =
        let tyargs =
          List.map
            (fun (x, ty) -> {
                 ov_name = omap unloc x.pl_desc;
                 ov_type = transty_for_decl env ty }) f.pfd_tyargs
        in

        let args = List.fold_left (fun names (x, _) ->
          match unloc x with
          | None   -> names
          | Some x -> x :: names) [] f.pfd_tyargs
        in

        Msym.odup unloc args |> oiter (fun (_, a) ->
          tyerror name.pl_loc env
          (InvalidModSig (MTS_DupArgName (unloc name, unloc a))));

        tyargs
      in

      let resty = transty_for_decl env f.pfd_tyresult in

      let rname, calls = trans_restr_fun env env sa f.pfd_uses in

      assert (rname = name.pl_desc);

      let sig_ = { fs_name   = name.pl_desc;
                   fs_arg    = ttuple (List.map ov_type tyargs);
                   fs_anames = tyargs;
                   fs_ret    = resty; }
      and ois = EcModules.change_oicalls ois name.pl_desc calls in
      [Tys_function sig_], ois

    | `Include (i,proc,restr) ->
      let (_modty,sig_) = transmodtype env i in
      if sig_.mis_params <> [] then
        tyerror i.pl_loc env (InvalidModType MTE_IncludeFunctor);

      let check_xs xs =
        List.iter (fun x ->
          let s = unloc x in
          if not (List.exists (fun (Tys_function fs) ->
                      sym_equal fs.fs_name s) sig_.mis_body) then
            let modsymb = fst (unloc i) @ [snd (unloc i)] in
            let funsymb = unloc x in
            tyerror (loc x) env (UnknownFunName (modsymb,funsymb))) xs in

      let in_xs (Tys_function fs) xs =
        List.exists (fun x -> sym_equal fs.fs_name (unloc x)) xs in

      let calls = trans_restr_oracle_calls env env sa restr in

      let update_ois ois (Tys_function fs) =
        names := mk_loc (loc i) fs.fs_name :: !names;
        EcModules.change_oicalls ois fs.fs_name calls
      in

      let ois, body = match proc with
        | None -> List.fold_left update_ois ois sig_.mis_body, List.rev sig_.mis_body
        | Some (`MInclude xs) ->
          check_xs xs;
          List.fold_left
            (fun (ois, body) fs ->
               if in_xs fs xs then (update_ois ois fs,fs :: body)
               else (ois, body))
            (ois,[]) sig_.mis_body
        | Some (`MExclude xs) ->
          check_xs xs;
          List.fold_left
            (fun (ois, body) fs ->
               if not (in_xs fs xs) then (update_ois ois fs, fs :: body)
               else (ois, body))
            (ois,[]) sig_.mis_body in

      body, ois in

  let items, ois = List.fold_left (fun (its, ois) i ->
      let l, mr = transsig1 ois i in
      l @ its, mr
    ) ([], Msym.empty) is in
  let items = List.rev items in
  let names = List.rev !names in

  Msym.odup unloc names |> oiter (fun (_, x) ->
    tyerror (loc x) env (InvalidModSig (MTS_DupProcName (unloc x))));
  (items, ois)

(* -------------------------------------------------------------------- *)
and transmod ~attop (env : EcEnv.env) (me : pmodule_def) =
  snd (transmod_header ~attop env me.ptm_header [] me.ptm_body)

(* -------------------------------------------------------------------- *)
and transmod_header
    ~attop (env : EcEnv.env) (mh:pmodule_header) params (me:pmodule_expr) =
  match mh with
  | Pmh_ident x ->
    0, transmod_body ~attop env x params me
  | Pmh_params {pl_desc = (mh,params')} ->
    let n, me = transmod_header ~attop env mh (params' @ params) me in
    n + List.length params', me
  | Pmh_cast(mh, mts) ->
    let n, me = transmod_header ~attop env mh params me in
    (* Compute the signature at the given position,
       i.e: remove the n first argument *)
    let rm,_ = List.takedrop n me.me_params in

    let env = EcEnv.Mod.bind me.me_name
                { tme_expr = me; tme_loca = `Global } env in

    let env = EcEnv.Mod.bind_params rm env in
    let args = List.map (fun (id,_) -> EcPath.mident id) rm in
    let mp =
      match EcEnv.scope env with
      | `Theory ->
        EcPath.mpath_crt (EcPath.pqname (EcEnv.root env) me.me_name) args None
      | `Module m ->
        assert (List.is_empty args);
        EcPath.mqname m me.me_name
      | `Fun _ ->
        assert false
    in

    let tymod = EcEnv.NormMp.sig_of_mp env mp in

    (* Check that the signature is a subtype *)
    let check s =
      let (aty, _asig) = transmodtype env s in

      try  check_sig_mt_cnv env tymod aty
      with TymodCnvFailure err ->
        let args = List.map (fun (id,_) -> EcPath.mident id) rm in
        let mp = mpath_crt (psymbol me.me_name) args None in
        tyerror s.pl_loc env (TypeModMismatch(mp, aty, err)) in
    List.iter check mts;

    n,me

(* -------------------------------------------------------------------- *)
and transmod_body ~attop (env : EcEnv.env) x params (me:pmodule_expr) =
  (* Check parameters types *) (* FIXME: dup names *)
  let stparams =
    List.map                          (* FIXME: exn *)
      (fun (a, aty) ->
         (EcIdent.create a.pl_desc, fst (transmodtype env aty)))
      params
  in
  let env = EcEnv.Mod.enter x.pl_desc stparams env in

  match me.pl_desc with
  | Pm_ident m ->
    let (mp, sig_) = trans_msymbol env {pl_desc = m; pl_loc = me.pl_loc} in

    let nb_params = List.length stparams + List.length sig_.miss_params in
    if nb_params > 0 && not attop then
      tyerror me.pl_loc env
        (InvalidModAppl (MAE_WrongArgCount(0,nb_params)));
    let me, _ = EcEnv.Mod.by_mpath mp env in
    let arity = List.length stparams in

    assert (List.length sig_.miss_params = List.length me.me_params);

    let extraparams = me.me_params in
    let allparams = stparams @ extraparams in

    let me = {
        me_name     = x.pl_desc;
        me_body     = ME_Alias (arity,mp);
        me_params   = allparams;
        me_sig_body = me.me_sig_body;
        me_comps    = me.me_comps;
        me_oinfos   = me.me_oinfos;
      } in
    me
  | Pm_struct ps ->
    transstruct ~attop env x.pl_desc stparams (mk_loc me.pl_loc ps)
  | Pm_update (m, delete_vars, vars, funs) ->
    let loc = me.pl_loc in
    let (mp, sig_) = trans_msymbol env {pl_desc = m; pl_loc = loc} in

    (* Prohibit functor updates *)
    if not (List.is_empty sig_.miss_params) then
      tyerror loc env (InvalidModUpdate MUE_Functor);

    (* Construct the set of new module variables *)
    let items =
      List.concat_map
        (fun (xs, ty) ->
          let ty = transty_for_decl env ty in
          let items = List.map
            (fun { pl_desc = x } -> MI_Variable { v_name = x; v_type = ty; })
            xs
          in
          items)
        vars
    in

    let delete_vars = List.map (fun v -> v.pl_desc) delete_vars in

    let me, _ = EcEnv.Mod.by_mpath mp env in
    let p = match mp.m_top with | `Concrete (p, _) -> p | _ -> assert false in
    let subst = EcSubst.add_moddef EcSubst.empty ~src:p ~dst:(EcEnv.mroot env) in
    let me = EcSubst.subst_module subst me in

    let update_fun env fn plocals pupdates pupdate_res =
      (* Extract the function body and load the memory *)
      let fun_ = EcEnv.Fun.by_xpath (xpath mp fn) env in

      (* Follow a function alias until we get to the concrete definition *)
      let rec resolve_alias f =
        match f.f_def with
        | FBabs _ ->
          tyerror loc env (InvalidModUpdate MUE_AbstractModule);
        | FBalias xp -> resolve_alias (EcEnv.Fun.by_xpath xp env)
        | FBdef _ -> f
      in

      let target_fun = EcSubst.subst_function subst (resolve_alias fun_) in
      let (_fs, fd), memenv = EcEnv.Fun.actmem_body (EcIdent.create "&hr") target_fun in

      let fun_ = EcSubst.subst_function subst fun_ in

      (* Introduce the new local variables *)
      let locals = List.concat_map (fun (vs, pty) ->
          let ty = transty_for_decl env pty in
          List.map (fun x -> { v_name = x.pl_desc; v_type = ty; }, x.pl_loc) vs
        )
        plocals
      in

      let memenv = fundef_add_symbol env memenv locals in
      let env = EcEnv.Memory.push_active_ss memenv env in

      let locals = ref locals in
      let memenv = ref memenv in

      (* Semantics for stmt updating, `i` is the target of the update. *)
      let eval_supdate env sup si =
        match sup with
        | Pups_add (s, after) ->
          let ue  = UE.create (Some []) in
          let s = transstmt env ue s in
          let ts = Tuni.subst (UE.close ue) in
          if after then
            si @ (s_subst ts s).s_node
          else
            (s_subst ts s).s_node @ si
        | Pups_del -> []
      in

      (* Semantics for condition updating *)
      let eval_cupdate cp_loc env cup si =
        (* NOTE: There will always be a head element *)
        (* `i` is the target of the update, and `tl` is the instr suffix. *)
        let i, tl = List.takedrop 1 si in
        let i = List.hd i in

        match cup with
        (* Insert an if with condition `e` with body `tl` *)
        | Pupc_add (e, after) ->
          let loc = e.pl_loc in
          let ue  = UE.create (Some []) in
          let e, ty = transexp env `InProc ue e in
          let ts = Tuni.subst (UE.close ue) in
          let ty = ty_subst ts ty in
          unify_or_fail env ue loc ~expct:tbool ty;
          if after then
            i :: [i_if (e_subst ts e, stmt tl, s_empty)]
          else
            [i_if (e_subst ts e, stmt (i :: tl), s_empty)]

        (* Change the condition expression to `e` for a conditional instr `i` *)
        | Pupc_mod e -> begin
          let loc = e.pl_loc in
          let ue  = UE.create (Some []) in
          let e, ty = transexp env `InProc ue e in
          let ts = Tuni.subst (UE.close ue) in
          let ty = ty_subst ts ty in
          match i.i_node with
          | Sif (_, t, f) ->
            unify_or_fail env ue loc ~expct:tbool ty;
            [i_if (e_subst ts e, t, f)] @ tl
          | Smatch (p, bs) ->
            unify_or_fail env ue loc ~expct:p.e_ty ty;
            [i_match (e_subst ts e, bs)] @ tl
          | Swhile (_, t) ->
            unify_or_fail env ue loc ~expct:tbool ty;
            [i_while (e_subst ts e, t)] @ tl
          | _ ->
            tyerror cp_loc env (InvalidModUpdate MUE_InvalidTargetCond);
          end

        (* Collapse a conditional `i` to a specific branch `bs` *)
        | Pupc_del bs -> begin
          let bs = trans_codepos_brsel bs in
          match i.i_node, bs with
          | Sif (_, t, _), `Cond true -> t.s_node
          | Sif (_, _, f), `Cond false -> f.s_node
          | Swhile (_, t), `Cond true -> t.s_node
          | Smatch (e, bs), `Match cn -> begin
            (* match e with | C a b c => b | ...  ---> (a, b, c) <- oget (get_as_C e); b *)

            let typ, tydc, tyinst = oget (EcEnv.Ty.get_top_decl e.e_ty env) in
            let tyinst = List.combine tydc.tyd_params tyinst in
            let indt = oget (EcDecl.tydecl_as_datatype tydc) in
            let cnames = List.fst indt.tydt_ctors in
            let r = List.assoc_opt cn (List.combine cnames bs) in
            match r with
            | None ->
              tyerror cp_loc env (InvalidModUpdate MUE_InvalidTargetCond)
            | Some (p, b) -> begin
              (* TODO: Factorize. This is mostly just a copy/paste from EcPhlRCond.gen_rcond_full. *)
              let cvars = List.map (fun (x, xty) -> { ov_name = Some (EcIdent.name x); ov_type = xty; }) p in
              let me, cvars = EcMemory.bindall_fresh cvars !memenv in

              let subst, pvs =
                let s = Fsubst.f_subst_id in
                let s, pvs = List.fold_left_map (fun s ((x, xty), name) ->
                    let pv = pv_loc (oget name.ov_name) in
                    let s  = bind_elocal s x (e_var pv xty) in
                    (s, (pv, xty)))
                  s (List.combine p cvars)
                in
                (s, pvs)
              in

              let asgn = EcModules.lv_of_list pvs |> omap (fun lv ->
                  let rty  = ttuple (List.snd p) in
                  let proj = EcInductive.datatype_proj_path typ cn in
                  let proj = e_op proj (List.snd tyinst) (tfun e.e_ty (toption rty)) in
                  let proj = e_app proj [e] (toption rty) in
                  let proj = e_oget proj rty in
                  i_asgn (lv, proj))
              in

              memenv := me;
              locals := !locals @ (List.map (fun ov -> {v_name = oget ov.ov_name; v_type = ov.ov_type; }, cp_loc) cvars);

              match asgn with
              | None -> b.s_node @ tl
              | Some a -> a :: (s_subst subst b).s_node @ tl
            end
          end
          | _ ->
            tyerror cp_loc env (InvalidModUpdate MUE_InvalidTargetCond);
          end
      in

      (* Apply each of updates in reverse *)
      (* NOTE: This is with the expectation that the user entered them in chronological order. *)
      let body =
        List.fold_right (fun (cpr, up) bd ->
          let {pl_desc = cpr; pl_loc = loc} = cpr in
          let cp = trans_codepos_range env cpr in
          let change env si =
            match up with
            | Pup_stmt sup ->
              eval_supdate env sup si
            | Pup_cond cup ->
              eval_cupdate loc env cup si
          in
          let env = EcEnv.Memory.push_active_ss !memenv env in
          try
            EcMatching.Zipper.map_range env cp change bd
          with
            | EcMatching.Zipper.InvalidCPos ->
              tyerror loc env (InvalidModUpdate MUE_InvalidCodePos);
        )
        pupdates
        fd.f_body
      in

      (* Apply the result update if given *)
      let ret = match fd.f_ret, pupdate_res with
        | Some e, Some e' ->
          let loc = e'.pl_loc in
          let ue  = UE.create (Some []) in
          let e', ty = transexp env `InProc ue e' in
          unify_or_fail env ue loc ~expct:e.e_ty ty;
          let ts = Tuni.subst (UE.close ue) in
          Some (e_subst ts e')
        | _ -> fd.f_ret
      in

      (* Reconstruct the function def *)
      let uses = ret |> ofold ((^~) se_inuse) (s_inuse body) in
      let fd = {f_locals = fd.f_locals @ (List.fst !locals); f_body = body; f_ret = ret; f_uses = uses; } in
      let fun_ = {fun_ with f_def = FBdef fd} in
      fun_
    in

    let allowed_funs = List.map (fun (Tys_function f) -> f.fs_name) me.me_sig_body in
    let funs = List.map (fun ({pl_loc = loc; pl_desc = fn}, lvs, v) ->
      if List.mem fn allowed_funs then
        fn, (lvs, v)
      else
        tyerror loc env (InvalidModUpdate MUE_InvalidFun)
    ) funs
    in

    (* Update all module items *)
    let env, items =
      match me.me_body with
      | ME_Structure mb ->
        let doit (env, items) mi =
          match mi with
          | MI_Variable v when not (List.mem (v_name v) delete_vars) ->
            let env = EcEnv.Var.bind_pvglob v.v_name v.v_type env in
            env, items @ [mi]
          | MI_Function f  -> begin
            match List.assoc_opt f.f_name funs with
            | None ->
              let env = EcEnv.bind1 (f.f_name, `Function f) env in
              env, items @ [mi]
            | Some (lvs, (upsc, rup)) ->
              let f = update_fun env f.f_name lvs upsc rup in
              let env = EcEnv.bind1 (f.f_name, `Function f) env in
              env, items @ [MI_Function f]
            end
          | MI_Module me ->
            let env = EcEnv.bind1 (me.me_name, `Module me) env in
            env, items @ [mi]
          | _ -> env, items
        in
        List.fold_left doit (env, []) (items @ mb.ms_body)

      | _ ->
        tyerror loc env (InvalidModUpdate MUE_AbstractModule);
    in

    let ois = get_oi_calls env (stparams, items) in

    (* Construct structure representation *)
    let me =
      { me_name       = x.pl_desc;
        me_body       = ME_Structure { ms_body = items; };
        me_comps      = items;
        me_params     = stparams;
        me_sig_body   = me.me_sig_body;
        me_oinfos     = ois; }
    in
    me

(* -------------------------------------------------------------------- *)
(* Module parameters must have been added to the environment            *)
and get_oi_calls env (params, items) =
  let mparams =
    let mparams = List.map (mident -| fst) params in
    Sm.of_list mparams in

  let comp_oi oi it = match it with
    | MI_Module  _ | MI_Variable _ -> oi
    | MI_Function f ->
      let rec f_call c f =
        let f = NormMp.norm_xfun env f in
        if EcPath.Sx.mem f c then c
        else
          let c = EcPath.Sx.add f c in
          let fun_ = EcEnv.Fun.by_xpath f env in
          match fun_.f_def with
          | FBalias _ -> assert false
          | FBdef def -> List.fold_left f_call c def.f_uses.us_calls
          | FBabs oi  ->
            List.fold_left f_call c (OI.allowed oi) in

      let all_calls =
        match f.f_def with
        | FBalias f -> f_call EcPath.Sx.empty f
        | FBdef def ->
          List.fold_left f_call EcPath.Sx.empty def.f_uses.us_calls
        | FBabs oi ->
          List.fold_left f_call EcPath.Sx.empty (OI.allowed oi) in
      let filter f =
        let ftop = EcPath.m_functor f.EcPath.x_top in
        Sm.mem ftop mparams in
      let calls = List.filter filter (EcPath.Sx.elements all_calls) in

      Msym.add f.f_name (OI.mk calls) oi in

  List.fold_left comp_oi Msym.empty items

(* -------------------------------------------------------------------- *)
and transstruct
    ~attop (env : EcEnv.env) (x : symbol)
    stparams (st:pstructure located) =
  let { pl_loc = loc; pl_desc = st; } = st in

  if not attop && stparams <> [] then
    tyerror loc env (InvalidModType MTE_InnerFunctor);

  let (env_funs, items) =
    let tydecl1 (x, obj) =
      match obj with
      | MI_Module   m -> (x, `Module   m)
      | MI_Variable v -> (x, `Variable v.v_type)
      | MI_Function f -> (x, `Function f)
    in
    List.fold_left
      (fun (env, acc) item ->
        let imports, newitems = transstruct1 env item in
        let env = EcEnv.bindall (List.map tydecl1 newitems) env in
        let env = List.fold_left EcEnv.Mod.import_vars env imports in
        (env, acc @ newitems))
      (env, []) st
  in
  let items = List.snd items in

  let sigitems = List.filter_map (function
      | MI_Module   _ | MI_Variable _ -> None
      | MI_Function f -> Some (Tys_function f.f_sig)
    ) items in

  let sigitems = List.rev sigitems in

  let ois = get_oi_calls env_funs (stparams, items) in

  (* Construct structure representation *)
  let me =
    { me_name       = x;
      me_body       = ME_Structure { ms_body = items; };
      me_comps      = items;
      me_params     = stparams;
      me_sig_body   = sigitems;
      me_oinfos     = ois; }
  in
  me

(* -------------------------------------------------------------------- *)
and transstruct1 (env : EcEnv.env) (st : pstructure_item located) =
  match unloc st with
  | Pst_mod  (x,cast, me) ->
    let pe = {
      ptm_header   = if List.is_empty cast then Pmh_ident x else Pmh_cast(Pmh_ident x, cast);
      ptm_body     = me; } in

    let me = transmod ~attop:false env pe in
    [], [me.me_name, MI_Module me]

  | Pst_var (xs, ty) ->
      let ty    = transty_for_decl env ty in
      let items =
        List.map
          (fun { pl_desc = x } ->
            (x, MI_Variable { v_name = x; v_type = ty; }))
          xs in

      [], items

  | Pst_fun (decl, body) -> begin
      let ue  = UE.create (Some []) in
      let env = EcEnv.Fun.enter decl.pfd_name.pl_desc env in

      (* Type-check function parameters / check for dups *)
      let params =
        let checked_name os =
          match unloc os with
          | None    -> tyerror os.pl_loc env NoConcreteAnonParams
          | Some os -> unloc os
        in
        List.map (fun (s,pty) -> {
              v_name = checked_name s;
              v_type = transty tp_uni env ue pty}, s.pl_loc) decl.pfd_tyargs
      in
      let memenv = EcMemory.empty_local ~witharg:false (EcIdent.create "&hr") in
      let memenv = fundef_add_symbol env memenv params in

      (* Type-check body *)
      let retty = transty tp_uni env ue decl.pfd_tyresult in
      let (env, stmt, result, prelude, locals) =
        transbody ue memenv env retty (mk_loc st.pl_loc body)
      in
      (* Close all types *)
      let ts      = Tuni.subst (UE.assubst ue) in
      let retty   = fundef_check_type (ty_subst ts) env None (retty, decl.pfd_tyresult.pl_loc) in
      let params  = List.map (fundef_check_decl (ty_subst ts) env) params in
      let locals  = List.map (fundef_check_decl (ty_subst ts) env) locals in
      let prelude = List.map (fundef_check_iasgn ts env) prelude in

      if not (UE.closed ue) then
        tyerror st.pl_loc env (OnlyMonoTypeAllowed None);

      let clsubst = ts in
      let stmt    = s_subst clsubst stmt
      and result  = result |> omap (e_subst clsubst) in
      let stmt    = EcModules.stmt (List.flatten prelude @ stmt.s_node) in

      (* Computes reads/writes/calls *)
      let uses = result |> ofold ((^~) se_inuse) (s_inuse stmt) in

      (* Compose all results *)
      let fun_ =
        { f_name   = decl.pfd_name.pl_desc;
          f_sig    = {
            fs_name   = decl.pfd_name.pl_desc;
            fs_arg    = ttuple (List.map (fun vd -> vd.v_type) params);
            fs_anames = List.map ovar_of_var params;
            fs_ret    = retty;
          };
          f_def = FBdef {
            f_locals = locals;
            f_body   = stmt;
            f_ret    = result;
            f_uses   = uses;
          };
        }
      in
        [], [(decl.pfd_name.pl_desc, MI_Function fun_)]
    end

  | Pst_alias ({pl_desc = name},f) ->
    [], [transstruct1_alias env name f]

  | Pst_import ms ->
    (List.map (fst -| trans_msymbol env) ms), []

  | Pst_include (m, imp, procs) -> begin
    let (mo, ms) = trans_msymbol env m in

    if ms.miss_params <> [] then
      tyerror (loc m) env (InvalidModType MTE_InnerFunctor);

    let check_procs =
      let check_proc { pl_loc = ploc; pl_desc = name; } =
        let check (Tys_function fs) = sym_equal fs.fs_name name in
        if not (List.exists check ms.miss_body) then
          let modsymb = List.map (unloc -| fst) (unloc m) in
          tyerror ploc env (UnknownFunName (modsymb,name))
      in
      List.iter check_proc in

    let in_procs (Tys_function fs) procs =
      List.exists (fun x -> sym_equal fs.fs_name (unloc x)) procs in

    let mk_fun (Tys_function fs) =
      (fs.fs_name,
       MI_Function { f_name = fs.fs_name;
                     f_sig  = fs;
                     f_def  = FBalias (EcPath.xpath mo fs.fs_name) }) in

    let items =
      match procs with
      | None ->
        List.map mk_fun ms.miss_body

      | Some (`MInclude procs) ->
        check_procs procs;
        List.pmap (fun fs ->
            if in_procs fs procs then Some (mk_fun fs) else None) ms.miss_body

      | Some (`MExclude procs) ->
        check_procs procs;
        List.pmap (fun fs ->
            if not (in_procs fs procs) then Some (mk_fun fs) else None) ms.miss_body

    in (if imp then [mo] else []), items
  end

and transstruct1_alias env name f =
  let f = trans_gamepath env f in
  let sig_ = (EcEnv.Fun.by_xpath f env).f_sig in
  let fun_ = {
      f_name = name;
      f_sig = { sig_ with fs_name = name };
      f_def = FBalias f;
    } in
  (name, MI_Function fun_)

(* -------------------------------------------------------------------- *)
and transbody ue memenv (env : EcEnv.env) retty pbody =
  let { pl_loc = loc; pl_desc = pbody; } = pbody in

  let prelude = ref []
  and locals  = ref [] in

  (* Type-check local variables / check for dups *)
  let add_local memenv local =
    let env   = EcEnv.Memory.push_active_ss memenv env in
    let ty     = local.pfl_type |> omap (transty tp_uni env ue) in
    let init   = local.pfl_init |> omap (fst -| transexp env `InProc ue) in
    let ty =
      match ty, init with
      | None   , None   -> None
      | Some ty, None   -> Some ty
      | None   , Some e -> Some e.e_ty
      | Some ty, Some e -> begin
          let loc =  (oget local.pfl_init).pl_loc in
            unify_or_fail env ue loc ~expct:ty e.e_ty; Some ty
      end
    in

    let xs     = snd (unloc local.pfl_names) in
    let mode   = fst (unloc local.pfl_names) in

    let xsvars = List.map (fun _ -> UE.fresh ue) xs in
    begin
      ty |> oiter (fun ty ->
        match mode with
        | `Single -> List.iter (fun a -> EcUnify.unify env ue a ty) xsvars
        | `Tuple  -> unify_or_fail env ue local.pfl_names.pl_loc ~expct:ty (ttuple xsvars))
    end;

    (* building the list of locals *)
    let xs = List.map2 (fun x ty -> {v_name = x.pl_desc; v_type = ty}, x.pl_loc) xs xsvars in
    let memenv = fundef_add_symbol env memenv xs in
    locals := xs :: !locals;
    init |> oiter
     (fun init ->
       let doit (v,_) = pv_loc v.v_name, v.v_type in
       let iasgn = List.map doit xs in
       prelude := ((mode, iasgn), init, _dummy) :: !prelude);
    memenv in

  let memenv = List.fold_left add_local memenv pbody.pfb_locals in
  let env = EcEnv.Memory.push_active_ss memenv env in

  let body   = transstmt env ue pbody.pfb_body in
  let result =
    match pbody.pfb_return with
    | None ->
        begin
          try  EcUnify.unify env ue tunit retty
          with EcUnify.UnificationFailure _ ->
            tyerror loc env NonUnitFunWithoutReturn
        end;
        None

    | Some pe ->
        let (e, ety) = transexp env `InProc ue pe in
        unify_or_fail env ue pe.pl_loc ~expct:retty ety;
        Some e
  in
    (env, body, result, List.rev !prelude, List.flatten (List.rev !locals))

(* -------------------------------------------------------------------- *)

(* for locals dup check *)
and fundef_add_symbol_mt env (memtype : memtype) xtys : memtype =
  try
    let f (x, _) = ovar_of_var x in
    EcMemory.bindall_mt (List.map f xtys) memtype
  with EcMemory.DuplicatedMemoryBinding s ->
    let (_, loc) = List.find (fun (v,_l) -> s = v.v_name) xtys in
    tyerror loc env (DuplicatedLocal s)

and fundef_add_symbol env (memenv : memenv) xtys : memenv =
  (fst memenv, fundef_add_symbol_mt env (snd memenv) xtys)

and fundef_check_type subst_uni env os (ty, loc) =
  let ty = subst_uni ty in
    if not (EcUid.Suid.is_empty (Tuni.fv ty)) then
      tyerror loc env (OnlyMonoTypeAllowed os);
    ty

and fundef_check_decl subst_uni env (decl, loc) =
  { decl with
      v_type =
      fundef_check_type subst_uni env (Some decl.v_name) (decl.v_type, loc) }

and fundef_check_iasgn subst_uni env ((mode, pl), init, loc) =
  let pl =
    List.map
      (fun (p, ty) ->
        (p, fundef_check_type (ty_subst subst_uni) env None (ty, loc)))
      pl
  in
  let pl =
    match mode with
    | `Single -> List.map (fun xty -> LvVar xty) pl
    | `Tuple  -> [LvTuple pl]
  in

  let clsubst = subst_uni in
  let init    = e_subst clsubst init in

    List.map (fun lv -> i_asgn (lv, init)) pl

(* -------------------------------------------------------------------- *)
and transstmt
  ?(map : ismap = Mstr.empty) (env : EcEnv.env) ue (stmt : pstmt) : stmt
=
  let l_start =
    Mstr.find_def [] EcTransMatching.default_start_name map in
  let l_end =
    Mstr.find_def [] EcTransMatching.default_end_name   map in
  let instr_list_list = List.map (transinstr ~map env ue) stmt in
  let instr_list_list = instr_list_list @ [l_end] in
  let instr_list_list = l_start :: instr_list_list in
  EcModules.stmt (List.flatten instr_list_list)

(* -------------------------------------------------------------------- *)
and transinstr
  ?(map : ismap = Mstr.empty) (env : EcEnv.env) ue (i : pinstr)
=
  let transcall name args =
    let fpath = trans_gamepath env name in
    let fsig  = (EcEnv.Fun.by_xpath fpath env).f_sig in
    let (args, ty) =
      transcall (transexp env `InProc ue) env ue name.pl_loc fsig args
    in
      (fpath, args, ty)
  in

  match i.pl_desc with
  | PSident x -> begin
      match Mstr.find_opt (unloc x) map with
      | Some x -> x
      | None ->
          tyerror (loc x) env (UnknownInstrMetaVar (unloc x))
    end

  | PSasgn (plvalue, prvalue) -> begin
      let handle_unknown_op = function
        | Expr { pl_desc = PFapp ({ pl_desc = PFident (f, None) }, _) }
            when EcEnv.Fun.lookup_opt (unloc f) env <> None
          -> tyerror prvalue.pl_loc env (ProcAssign (unloc f))
        | _ -> ()
      in

      let lvalue, lty = translvalue ue env plvalue in
      let rvalue, rty =
        try transexp env `InProc ue prvalue with
        | TyError (l, e, exn) ->
            handle_unknown_op (unloc prvalue);
            tyerror l e exn
      in
      unify_or_fail env ue prvalue.pl_loc ~expct:lty rty;
      [ i_asgn_lv i.pl_loc env lvalue rvalue ]
    end

  | PSrnd (plvalue, prvalue) ->
      let lvalue, lty = translvalue ue env plvalue in
      let rvalue, rty = transexp env `InProc ue prvalue in
      unify_or_fail env ue prvalue.pl_loc ~expct:(tdistr lty) rty;
      [ i_rnd_lv i.pl_loc env lvalue rvalue ]

  | PScall (None, name, args) ->
      let (fpath, args, _rty) = transcall name (unloc args) in
      [ i_call (None, fpath, args) ]

  | PScall (Some lvalue, name, args) ->
      let lvalue, lty = translvalue ue env lvalue in
      let (fpath, args, rty) = transcall name (unloc args) in
      unify_or_fail env ue name.pl_loc ~expct:lty rty;
      [ i_call_lv i.pl_loc env lvalue fpath args ]

  | PSif ((pe, s), cs, sel) -> begin
      let rec for1_i (pe, s) sel =
        let e, ety = transexp env `InProc ue pe in
        let s = transstmt env ue s in
        unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
        i_if (e, s, sel)

      and for1_s (pe, s) sel = stmt [for1_i (pe, s) sel] in

      [ for1_i (pe, s)
        (List.fold_right for1_s cs (transstmt env ue sel)) ]
  end

  | PSwhile (pe, pbody) ->
      let e, ety = transexp env `InProc ue pe in
      let body = transstmt env ue pbody in
      unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
      [ i_while (e, body) ]

  | PSmatch (pe, pbranches) -> begin
      let e, ety = transexp env `InProc ue pe in
      let uidmap = EcUnify.UniEnv.assubst ue in
      let ety = ty_subst (Tuni.subst uidmap) ety in

      let inddecl =
        match (EcEnv.ty_hnorm ety env).ty_node with
        | Tconstr (indp, _) -> begin
            match EcEnv.Ty.by_path indp env with
            | { tyd_type = Datatype dt } ->
                Some (indp, dt)
            | _ -> None
          end
        | _ -> None in

      let (_indp, inddecl) =
        match inddecl with
        | None   -> tyerror pe.pl_loc env NotAnInductive
        | Some x -> x in

      let branches =
        match pbranches with
        | `Full pbranches ->
            let aout = trans_match ~loc:i.pl_loc env ue (ety, inddecl) pbranches in
            List.map (snd_map some) aout

        | `If ((c, b1), b2) ->
            trans_if_match ~loc:i.pl_loc env ue (ety, inddecl) (c, b1, b2)

      in

      let branches = List.map (fun (lcs, s) ->
        let env = EcEnv.Var.bind_locals lcs env in
        (lcs, omap (transstmt env ue) s |> odfl (stmt []))) branches in

      [ i_match (e, branches) ]
    end

  | PSassert pe ->
      let e, ety = transexp env `InProc ue pe in
      unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
      [ i_assert e ]

(* -------------------------------------------------------------------- *)
and trans_pv env { pl_desc = x; pl_loc = loc } =
  let side = EcEnv.Memory.get_active_ss env in
  match EcEnv.Var.lookup_progvar_opt ?side x env with
  | None -> tyerror loc env (UnknownModVar x)
  | Some(pv,xty) ->
    match pv with
    | `Var pv -> pv, xty
    | `Proj _ -> assert false

and translvalue ue (env : EcEnv.env) lvalue =
  match lvalue.pl_desc with
  | PLvSymbol x ->
      let pty = trans_pv env x in
      Lval (LvVar pty), snd pty

  | PLvTuple xs ->
      let xs = List.map (trans_pv env) xs in
      if not (List.is_unique ~eq:(EqTest.for_pv env) (List.map fst xs)) then
        tyerror lvalue.pl_loc env LvNonLinear;
      let ty = ttuple (List.map snd xs) in
      Lval (LvTuple xs), ty

  | PLvMap (x, tvi, codom, es) ->
      let tvi = tvi |> omap (transtvi env ue) in
      let codom = Option.map (transty tp_relax env ue) codom in
      let codom = ofdfl (fun () -> UE.fresh ue) codom in
      let pv, xty = trans_pv env x in
      let e, ety = List.split (List.map (transexp env `InProc ue) es) in

      let e, ety = e_tuple e, ttuple ety in

      let name = ([], EcCoreLib.s_set) in
      let esig = [xty; ety; codom] in
      let ops = select_exp_op env `InProc None name ue tvi (esig, None) in

      match ops with
      | [] ->
         let uidmap = UE.assubst ue in
         let esig = Tuni.subst_dom uidmap esig in
          tyerror x.pl_loc env (UnknownVarOrOp (name, esig))

      | [`Op (p, tys), opty, subue, _] ->
          EcUnify.UniEnv.restore ~src:subue ~dst:ue;
          let uidmap = UE.assubst ue in
          let esig = Tuni.subst_dom uidmap esig in
          let esig = toarrow esig xty in
          unify_or_fail env ue lvalue.pl_loc ~expct:esig opty;
          LvMap ((p, tys), pv, e, xty), codom

      | [_] ->
          let uidmap = UE.assubst ue in
          let esig = Tuni.subst_dom uidmap esig in
          tyerror x.pl_loc env (UnknownVarOrOp (name, esig))

      | _ ->
          let uidmap = UE.assubst ue in
          let esig = Tuni.subst_dom uidmap esig in
          let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
          tyerror x.pl_loc env (MultipleOpMatch (name, esig, matches))

(* -------------------------------------------------------------------- *)
and trans_gbinding env ue decl =
  let trans1 env (xs, pgty) =
      match pgty with
      | PGTY_Type ty ->
        let ty  = transty tp_relax env ue ty in
        let xs  = List.map (fun x -> ident_of_osymbol (unloc x), ty) xs in
        let env = EcEnv.Var.bind_locals xs env in
        let xs  = List.map (fun (x,ty) -> x,GTty ty) xs in
        (env, xs)

      | PGTY_ModTy { pmty_pq = mi; pmty_mem = restr } ->
        let mi = fst (transmodtype env mi) in
        let mi = trans_restr_for_modty env mi restr in

        let ty = GTmodty mi in

        let add1 env x =
          let x   = ident_of_osymbol (unloc x) in
          let env = EcEnv.Mod.bind_local x mi env in
          (env, (x, ty))

        in List.map_fold add1 env xs

      | PGTY_Mem pmt ->
        let mt = match pmt with
          | None     -> EcMemory.abstract_mt
          | Some pmt -> trans_memtype env ue pmt
        in
        let add1 env x =
          let x   = ident_of_osymbol (unloc x) in
          let env = EcEnv.Memory.push (x, mt) env in
          (env, (x, GTmem mt))

        in List.map_fold add1 env xs

  in snd_map List.flatten (List.map_fold trans1 env decl)

(* -------------------------------------------------------------------- *)
and trans_form_or_pattern env mode ?mv ?ps ue pf tt =
  let state = PFS.create () in

  let rec transf_r_tyinfo opsc env ?tt f =
    let transf env ?tt f =
      transf_r opsc env ?tt f in

    match f.pl_desc with
    | PFhole -> begin
      match ps with
      | None    -> tyerror f.pl_loc env PatternNotAllowed
      | Some ps ->
        let x  = EcIdent.create (Printf.sprintf "?%d" (EcUid.unique ())) in
        let ty = UE.fresh ue in
        ps := Mid.add x ty !ps; f_local x ty
    end

    | PFref ({ pl_desc = name; pl_loc = loc }, filters) -> begin
        match Msym.find_opt name (odfl Msym.empty mv) with
        | None   -> tyerror loc env (UnknownMetaVar name)
        | Some f ->             (* FIXME: refresh *)
            let rec flatten deep f =
              try
                let (f1, f2) = EcFol.destr_and f in
                (if deep then flatten deep f1 else [f1]) @ (flatten deep f2)
              with DestrError _ -> [f] in

            let trans_idx (f : form list) (idx : pfindex) =
              match idx with
              | `Index i ->
                  i

              | `Match (ppt, off) ->
                  let ps   = ref Mid.empty in
                  let ue   = EcUnify.UniEnv.create None in
                  let pt   = trans_pattern env ps ue ppt in
                  let ev   = EcMatching.MEV.of_idents (Mid.keys !ps) `Form in
                  let mode = EcMatching.fmrigid in
                  let hyps = EcEnv.LDecl.init env [] in

                  let test (_ : int) f =
                    try
                      ignore (EcMatching.f_match mode hyps (ue, ev) pt f);
                      true
                    with EcMatching.MatchFailure -> false in

                  match List.Exceptionless.findi test f with
                  | Some (i, _) ->
                      (i+1) + (odfl 0 off)
                  | None ->
                      tyerror loc env (InvalidFilter (FE_NoMatch))

            in

            let trans_rg (f : form list) (rg : pfrange) =
              match rg with
              | `Single idx ->
                  `Single (trans_idx f idx)

              | `Range (i1, i2) ->
                  let i1 = omap (trans_idx f) i1 in
                  let i2 = omap (trans_idx f) i2 in
                  `Range (i1, i2) in

            let filter1 (fs : form list) ij =
              let n = List.length fs in
              let norm (x as ox) =
                let x =
                  match x with
                  | x when 0 < x && x  <= n -> Some (x - 1)
                  | x when x < 0 && -n <= x -> Some (n + x)
                  | _ -> None in

                match x with
                | None   -> tyerror loc env (InvalidFilter (FE_InvalidIndex ox))
                | Some x -> x in

              match
                match ij with
                | `Single  i     -> `Single (norm i)
                | `Range  (i, j) ->
                    let i = odfl 0 (omap norm i) in
                    let j = odfl n (omap norm j) in
                    `Range (i, j)
              with
              | `Single k        -> [List.nth fs k]
              | `Range  (k1, k2) -> List.take (k2 + 1 - k1) (List.drop k1 fs) in

            let filter f pf =
              match pf with
              | PFRange (deep, rgs) ->
                  let f   = flatten deep f in
                  let rgs = List.map (trans_rg f) rgs in
                  let f   = List.map (filter1 f) rgs in
                  f_ands (List.flatten f)

              | PFMatch (deep, x, ppt) ->
                  let f    = f_ands (flatten deep f) in
                  let x    = EcIdent.create (unloc x) in
                  let lenv = EcEnv.Var.bind_local x tbool env in
                  let ps   = ref Mid.empty in
                  let ue   = EcUnify.UniEnv.create None in
                  let pt   = trans_pattern lenv ps ue ppt in
                  let ev   = EcMatching.MEV.of_idents (x :: Mid.keys !ps) `Form in
                  let mode = EcMatching.fmrigid in
                  let hyps = EcEnv.LDecl.init lenv [] in

                  let (ue, _, ev) =
                    try  EcMatching.f_match mode hyps (ue, ev) pt f
                    with EcMatching.MatchFailure ->
                      tyerror ppt.pl_loc env FilterMatchFailure in

                  let subst = EcMatching.MEV.assubst ue ev env in
                  Fsubst.f_subst subst (f_local x tbool)

              | PFMatchBuild (deep, xs, ptg, ppt) ->
                  let f    = f_ands (flatten deep f) in
                  let xs   = List.map (EcIdent.create -| unloc) xs in
                  let xst  = List.map (fun x -> (x, tbool)) xs in
                  let lenv = EcEnv.Var.bind_locals xst env in
                  let tg   = trans_prop lenv ue ptg in
                  let ps   = ref Mid.empty in
                  let ue   = EcUnify.UniEnv.create None in
                  let pt   = trans_pattern lenv ps ue ppt in
                  let ev   = EcMatching.MEV.of_idents (xs @ Mid.keys !ps) `Form in
                  let mode = EcMatching.fmrigid in
                  let hyps = EcEnv.LDecl.init lenv [] in

                  let (ue, _, ev) =
                    try  EcMatching.f_match mode hyps (ue, ev) pt f
                    with EcMatching.MatchFailure ->
                      tyerror ppt.pl_loc env FilterMatchFailure in

                  let subst = EcMatching.MEV.assubst ue ev env in
                  Fsubst.f_subst subst tg

              | PFKeep (deep, rooted, exclude, ppt) ->
                  let f    = flatten deep f in
                  let ps   = ref Mid.empty in

                  let module E = struct exception MatchFound end in

                  let test =
                    match ppt with
                    | `Pattern ppt ->
                         let ue   = EcUnify.UniEnv.create None in
                         let pt   = trans_pattern env ps ue ppt in
                         let ev   = EcMatching.MEV.of_idents (Mid.keys !ps) `Form in
                         let mode = EcMatching.fmrigid in
                         let hyps = EcEnv.LDecl.init env [] in

                         let test target =
                           try
                             ignore (EcMatching.f_match mode hyps (ue, ev) pt target);
                             raise E.MatchFound
                           with EcMatching.MatchFailure -> `Continue in

                         let test target =
                           if rooted then test target else

                           try
                             ignore (EcMatching.f_match mode hyps (ue, ev) pt target);
                             raise E.MatchFound
                           with EcMatching.MatchFailure ->
                             `Continue

                         in test

                    | `VarSet xs ->
                        let trans1 (x, s) =
                          let mem =
                            match s with
                            | None -> oget (EcEnv.Memory.get_active_ss env)
                            | Some s -> transmem env s

                          in (transpvar env mem x, mem) in

                        let xs = List.map trans1 xs in

                        let test target =
                          match target.f_node with
                          | Fpvar (p, m) ->
                              if (List.exists (fun (p', m') ->
                                    EcMemory.mem_equal m m' &&
                                    EcEnv.NormMp.pv_equal env p p')
                                  xs)
                              then raise E.MatchFound else `Continue

                          | _ -> `Continue

                        in test
                  in

                  let test target =
                    try
                      ignore (EcMatching.FPosition.select (fun _ -> test) target);
                      false
                    with E.MatchFound -> true in

                  let test target =
                    let b = test target in
                    if exclude then not b else b in

                  f_ands (List.filter test f)

            in List.fold_left filter f filters
    end

    | PFcast (pf, pty) ->
        let ty = transty tp_relax env ue pty in
        let aout = transf env ~tt:ty pf in
        unify_or_fail env ue pf.pl_loc ~expct:ty aout.f_ty; aout

    | PFmem _ -> tyerror f.pl_loc env MemNotAllowed

    | PFscope (popsc, f) ->
        let opsc = lookup_scope env popsc in
          transf_r (Some opsc) env f

    | PFglob gp ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `Glob);

        let mp = fst (trans_msymbol env gp) in
        let me =
          match EcEnv.Memory.current_ss env with
          | None -> tyerror f.pl_loc env NoActiveMemory
          | Some me -> EcMemory.memory me
        in PFS.set_memused state;
           (EcEnv.NormMp.norm_glob env me mp).inv

    | PFint n ->
        f_int n

    | PFdecimal (n, f) ->
        f_decimal (n, f)

    | PFtuple pes ->
        let esig = List.map (fun _ -> EcUnify.UniEnv.fresh ue) pes in
        tt |> oiter (fun tt -> unify_or_fail env ue f.pl_loc  ~expct:tt (ttuple esig));
        let es = List.map2 (fun tt pe -> transf env ~tt pe) esig pes in
        f_tuple es

    | PFident ({ pl_desc = name; pl_loc = loc }, tvi) ->
        let tvi = tvi |> omap (transtvi env ue) in
        let ops =
          select_form_op
            ~forcepv:(PFS.isforced state)
            env mode opsc name ue tvi ([], tt) in
        begin match ops with
        | [] ->
            tyerror loc env (UnknownVarOrOp (name, []))

        | [sel] -> begin
            let op = form_of_opselect (env, ue) loc sel [] in
            let inmem =
              match op.f_node with
              | Fpvar _ | Fproj ({ f_node = Fpvar _ }, _) -> true
              | _ -> false in
            if inmem then PFS.set_memused state; op
        end

        | _ ->
            let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
            tyerror loc env (MultipleOpMatch (name, [], matches))
        end

    | PFside (f, (force, side)) -> begin
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `MemSel);

        let (sloc, side) = (side.pl_loc, unloc side) in
        let me =
          match EcEnv.Memory.lookup side env with
          | None -> tyerror sloc env (UnknownMemName side)
          | Some me -> EcMemory.memory me
        in

        let used, aout =
          PFS.new_memused
            (transf (EcEnv.Memory.set_active_ss me env))
            ~force state f
        in
        if not used then begin
          let ppe = EcPrinting.PPEnv.ofenv env in
          EcEnv.notify ~immediate:false env `Warning
            "unused memory `%s', while typing %a"
            side (EcPrinting.pp_form ppe) aout
        end;
        aout
      end

    | PFeqveq (xs, om) ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `MemSel);

        let lookup me x =
          match EcEnv.Var.lookup_progvar_opt ~side:me (unloc x) env with
          | None -> tyerror x.pl_loc env (UnknownVarOrOp (unloc x, []))
          | Some (x, ty) ->
            var_or_proj (fun x ty -> (f_pvar x ty me).inv) f_proj x ty
        in

        let qual (mq : pmsymbol option) (x : pqsymbol) =
          match mq with
          | None    -> x
          | Some qs ->
              let (nm, name) = x.pl_desc in
              { x with pl_desc = ((List.map (unloc -| fst) qs)@nm, name) }
        in

         let do1 = function
          | GVvar x ->
              let ml, mr = oget (EcEnv.Memory.get_active_ts env) in
              let x1 = lookup ml (qual (om |> omap fst) x) in
              let x2 = lookup mr (qual (om |> omap snd) x) in
                unify_or_fail env ue x.pl_loc ~expct:x1.f_ty x2.f_ty;
                f_eq x1 x2

          | GVglob (gp, ex) ->
              let (m, _) = trans_msymbol env gp in
              let ex = List.map (trans_pv env) ex in

              let filter_pv (xp, _) =
                let xp = pv_glob xp in
                let for1 (ex1, _) = not (EcEnv.NormMp.pv_equal env xp ex1) in
                List.for_all for1 ex in

              let create mem =
                if List.is_empty ex then
                  EcEnv.NormMp.norm_glob env mem m
                else

                let use = EcEnv.NormMp.mod_use env m in
                let gl  = Sid.elements use.us_gl in
                let pv  = List.filter filter_pv (Mx.bindings use.us_pv) in
                let res =
                    List.map (fun mid -> f_glob mid mem) gl
                  @ List.map (fun (xp, ty) -> f_pvar (EcTypes.pv_glob xp) ty mem) pv in

                map_ss_inv f_tuple res in
                  
              let ml, mr = oget (EcEnv.Memory.get_active_ts env) in
              let x1 = ss_inv_generalize_right (create ml) mr in
              let x2 = ss_inv_generalize_left (create mr) ml in

              unify_or_fail env ue gp.pl_loc ~expct:x1.inv.f_ty x2.inv.f_ty;
              (map_ts_inv2 f_eq x1 x2).inv
        in
          EcFol.f_ands (List.map do1 xs)

    | PFeqf fs ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `MemSel);

        let check_mem loc me =
          match EcEnv.Memory.byid me env with
          | None -> tyerror loc env (UnknownMemName (EcIdent.name me))
          | Some _ -> ()

        and do1 (me1, me2) f =
          let _, f1 =
            PFS.new_memused
              (transf (EcEnv.Memory.set_active_ss me1 env))
              ~force:false state f in
          let _, f2 =
            PFS.new_memused
              (transf (EcEnv.Memory.set_active_ss me2 env))
              ~force:false state f in
          unify_or_fail env ue f.pl_loc ~expct:f1.f_ty f2.f_ty;
          f_eq f1 f2

        in
          let ml, mr = oget (EcEnv.Memory.get_active_ts env) in
          check_mem f.pl_loc ml;
          check_mem f.pl_loc mr;
          EcFol.f_ands (List.map (do1 (ml, mr)) fs)

    | PFapp ({pl_desc = PFident ({ pl_desc = name; pl_loc = loc }, tvi)}, pes) -> begin
      let try_trans ?tt pe =
        let ue' = EcUnify.UniEnv.copy ue in
        let ps' = Option.map (fun ps -> ref !ps) ps in
          match transf env ?tt pe with
          | e -> Some e
          | exception TyError (_, _, MultipleOpMatch _) ->
            Option.iter (fun ps -> ps := !(Option.get ps')) ps;
            EcUnify.UniEnv.restore ~dst:ue ~src:ue';
            None
      in

      match
        let ue'  = EcUnify.UniEnv.copy ue in
        let ps'  = Option.map (fun ps -> ref !ps) ps in
        let es   = List.map (fun pe -> try_trans pe) pes in
        let tvi  = tvi |> omap (transtvi env ue) in
        let esig = List.map (fun e ->
            match e with Some e -> e.f_ty | None -> EcUnify.UniEnv.fresh ue
          ) es in
        match
          select_form_op ~forcepv:(PFS.isforced state)
            env mode opsc name ue tvi (esig, tt)
        with
        | [sel] -> Some (sel, (es, esig, tvi))
        | _ ->
            Option.iter (fun ps -> ps := !(Option.get ps')) ps;
            EcUnify.UniEnv.restore ~dst:ue ~src:ue';
            None
      with
      | None -> begin
        let tvi  = tvi |> omap (transtvi env ue) in
        let es   = List.map (transf env) pes in
        let esig = List.map EcFol.f_ty es in
        let ops  =
          select_form_op ~forcepv:(PFS.isforced state)
            env mode opsc name ue tvi (esig, tt) in

          begin match ops with
          | [] ->
             let uidmap = UE.assubst ue in
             let esig = Tuni.subst_dom uidmap esig in
             tyerror loc env (UnknownVarOrOp (name, esig))

          | [sel] ->
              let es = List.map2 (fun e l -> mk_loc l.pl_loc e) es pes in
              form_of_opselect (env, ue) loc sel es

          | _ ->
             let uidmap = UE.assubst ue in
             let esig = Tuni.subst_dom uidmap esig in
             let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
             tyerror loc env (MultipleOpMatch (name, esig, matches))
          end
        end

      | Some ((_, _, subue, _) as sel, (es, esig, _tvi)) ->
        EcUnify.UniEnv.restore ~dst:ue ~src:subue;
        let es =
          List.map2 (
            fun (e, ty) pe ->
              match e with None -> try_trans ~tt:ty pe | Some e -> Some e
          ) (List.combine es esig) pes in
          let es =
            List.map2 (
              fun (e, ty) pe ->
                match e with None -> transf env ~tt:ty pe | Some e -> e
            ) (List.combine es esig) pes in
          let es = List.map2 (fun e l -> mk_loc l.pl_loc e) es pes in
        EcUnify.UniEnv.restore ~src:ue ~dst:subue;
        form_of_opselect (env, ue) loc sel es
      end

    | PFapp (e, pes) ->
        let es    = List.map (transf env) pes in
        let esig  = List.map2 (fun f l -> mk_loc l.pl_loc f.f_ty) es pes in
        let op    = transf env e in
        let codom = ty_fun_app e.pl_loc env ue op.f_ty esig in
        f_app op es codom

    | PFif (pf1, pf2, pf3) ->
        let f1 = transf env pf1 in
        let f2 = transf env pf2 in
        let f3 = transf env pf3 in
          unify_or_fail env ue pf1.pl_loc ~expct:tbool   f1.f_ty;
          unify_or_fail env ue pf3.pl_loc ~expct:f2.f_ty f3.f_ty;
          f_if f1 f2 f3

    | PFmatch (pcf, pb) ->
       let cf = transf env pcf in
       let ts = Tuni.subst (UE.assubst ue) in
       let cfty = ty_subst ts cf.f_ty in

        let inddecl =
          match (EcEnv.ty_hnorm cfty env).ty_node with
          | Tconstr (indp, _) -> begin
              match EcEnv.Ty.by_path indp env with
              | { tyd_type = Datatype dt } ->
                  Some (indp, dt)
              | _ -> None
            end
          | _ -> None in

        let (_indp, inddecl) =
          match inddecl with
          | None   -> tyerror pcf.pl_loc env NotAnInductive
          | Some x -> x in

        let branches =
          trans_match ~loc:f.pl_loc env ue (cf.f_ty, inddecl) pb in

        let branches, bty = List.split (List.map (fun (lcs, s) ->
          let env  = EcEnv.Var.bind_locals lcs env in
          let bdy  = transf env s in
          f_lambda (List.map (snd_map gtty) lcs) bdy, (bdy.f_ty, s.pl_loc)) branches) in

        let rty = EcUnify.UniEnv.fresh ue in

        List.iter (fun (ty, loc) -> unify_or_fail env ue loc ~expct:rty ty) bty;
        f_match cf branches rty

    | PFlet (lp, (pf1, paty), f2) ->
        let (penv, p, pty) = transpattern env ue lp in
        let aty = paty |> omap (transty tp_uni env ue) in
        let f1 = transf env pf1 in
        unify_or_fail env ue pf1.pl_loc ~expct:pty f1.f_ty;
        aty |> oiter (fun aty-> unify_or_fail env ue pf1.pl_loc ~expct:pty aty);
        let f2 = transf penv ?tt f2 in
        f_let p f1 f2

    | PFforall (xs, pf) ->
        let env, xs = trans_gbinding env ue xs in
        let f = transf env pf in
        unify_or_fail env ue pf.pl_loc ~expct:tbool f.f_ty;
        f_forall xs f

    | PFexists (xs, f1) ->
        let env, xs = trans_gbinding env ue xs in
        let f = transf env f1 in
        unify_or_fail env ue f1.pl_loc ~expct:tbool f.f_ty;
        f_exists xs f

    | PFlambda (xs, f1) ->
        let env, xs = trans_binding env ue xs in
        let subtt = tt |> Option.map (fun tt ->
          let codom = EcUnify.UniEnv.fresh ue in
          unify_or_fail env ue (loc f) ~expct:(toarrow (List.snd xs) codom) tt;
          codom
        ) in
        let f = transf env ?tt:subtt f1 in
        f_lambda (List.map (fun (x, ty) -> (x, GTty ty)) xs) f

    | PFrecord (b, fields) ->
        let (ctor, fields, (rtvi, reccty)) =
          let proj (recp, name, (rtvi, reccty), pty, arg) =
            let proj = EcPath.pqname recp name in
            let proj = f_op proj rtvi (tfun reccty pty) in
            f_app proj [arg] pty in
          trans_record env ue
            ((fun f -> let f = transf env f in (f, f.f_ty)), proj)
            (f.pl_loc, b, fields) in
        let ctor = f_op ctor rtvi (toarrow (List.map snd fields) reccty) in
        f_app ctor (List.map fst fields) reccty

    | PFproj (subf, x) -> begin
      let subf = transf env subf in

      match select_proj env opsc (unloc x) ue None subf.f_ty with
      | [] ->
         tyerror x.pl_loc env (UnknownProj (unloc x))

      | _ :: _ :: _ ->
          tyerror x.pl_loc env (AmbiguousProj (unloc x))

      | [(op, tvi), pty, subue] ->
        EcUnify.UniEnv.restore ~src:subue ~dst:ue;
        let rty = EcUnify.UniEnv.fresh ue in
        (try  EcUnify.unify env ue (tfun subf.f_ty rty) pty
         with EcUnify.UnificationFailure _ -> assert false);
        f_app (f_op op tvi pty) [subf] rty
    end

    | PFproji (psubf, i) -> begin
      let subf = transf env psubf in
      let ts   = Tuni.subst (UE.assubst ue) in
      let ty   = ty_subst ts subf.f_ty in
      match (EcEnv.ty_hnorm ty env).ty_node with
      | Ttuple l when i < List.length l ->
          f_proj subf i (List.nth l i)
      | _ ->
          tyerror psubf.pl_loc env (AmbiguousProji (i, ty))
    end

    | PFprob (m, gp, args, pr_m, event) ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `Pr);

        let fpath = trans_gamepath env gp in
        let fun_  = EcEnv.Fun.by_xpath fpath env in
        let args,_ =
          transcall (fun f -> let f = transf env f in f, f.f_ty)
            env ue f.pl_loc fun_.f_sig args in
        let memid = transmem env pr_m in
        let m = odfl "&hr" (omap unloc m) in
        let m = EcIdent.create m in
        let env = EcEnv.Fun.prF m fpath env in
        let event' = {m;inv=transf env event} in
        unify_or_fail env ue event.pl_loc ~expct:tbool event'.inv.f_ty;
        f_pr memid fpath (f_tuple args) event'

    | PFhoareF (m, pre, gp, post) ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `Logic);
        let fpath = trans_gamepath env gp in
        let m = odfl "&hr" (omap unloc m) in
        let m = EcIdent.create m in
        let penv, qenv = EcEnv.Fun.hoareF m fpath env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
          unify_or_fail penv ue pre.pl_loc  ~expct:tbool pre' .f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
          f_hoareF {m;inv=pre'} fpath {m;inv=post'}

    | PFehoareF (m, pre, gp, post) ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `Logic);
        let m = odfl "&hr" (omap unloc m) in
        let m = EcIdent.create m in
        let fpath = trans_gamepath env gp in
        let penv, qenv = EcEnv.Fun.hoareF m fpath env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
          unify_or_fail penv ue pre.pl_loc  ~expct:txreal pre'.f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:txreal post'.f_ty;
          f_eHoareF {m;inv=pre'} fpath {m;inv=post'}

    | PFBDhoareF (m, pre, gp, post, hcmp, bd) ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `Logic);
        let m = odfl "&hr" (omap unloc m) in
        let m = EcIdent.create m in
        let fpath = trans_gamepath env gp in
        let penv, qenv = EcEnv.Fun.hoareF m fpath env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
        let bd'   = transf penv bd in
          (* FIXME: check that there are not pvars in bd *)
          unify_or_fail penv ue pre .pl_loc ~expct:tbool pre' .f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
          unify_or_fail env  ue bd  .pl_loc ~expct:treal bd'  .f_ty;
          f_bdHoareF {m;inv=pre'} fpath {m;inv=post'} hcmp {m;inv=bd'}

    | PFlsless gp ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `LL);
        let fpath = trans_gamepath env gp in
          f_losslessF fpath

    | PFequivF (ml, mr, pre, (gp1, gp2), post) ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `Logic);
        let ml = odfl "&1" (omap unloc ml) in
        let ml = EcIdent.create ml in
        let mr = odfl "&2" (omap unloc mr) in
        let mr = EcIdent.create mr in
        let fpath1 = trans_gamepath env gp1 in
        let fpath2 = trans_gamepath env gp2 in
        let penv, qenv = EcEnv.Fun.equivF ml mr fpath1 fpath2 env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
          unify_or_fail penv ue pre .pl_loc ~expct:tbool pre' .f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
          f_equivF {ml;mr;inv=pre'} fpath1 fpath2 {ml;mr;inv=post'}

    | PFeagerF (ml, mr, pre, (s1,gp1,gp2,s2), post) ->
        if mode <> `Form then
          tyerror f.pl_loc env (NotAnExpression `Logic);
        let ml = odfl "&1" (omap unloc ml) in
        let ml = EcIdent.create ml in
        let mr = odfl "&2" (omap unloc mr) in
        let mr = EcIdent.create mr in
        let fpath1 = trans_gamepath env gp1 in
        let fpath2 = trans_gamepath env gp2 in
        let penv, qenv = EcEnv.Fun.equivF ml mr fpath1 fpath2 env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
        let s1    = transstmt env ue s1 in
        let s2    = transstmt env ue s2 in
        unify_or_fail penv ue pre .pl_loc ~expct:tbool pre' .f_ty;
        unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
        f_eagerF {ml;mr;inv=pre'} s1 fpath1 fpath2 s2 {ml;mr;inv=post'}

  and transf_r opsc env ?tt pf =
    let f  = transf_r_tyinfo opsc env ?tt pf in
    let () = oiter (fun tt -> unify_or_fail env ue pf.pl_loc ~expct:tt f.f_ty) tt in
    f

  in transf_r None env ?tt pf

(* Type-check a memtype. *)
and trans_memtype env ue (pmemtype : pmemtype) : memtype =
  let mt = EcMemory.empty_local_mt ~witharg:false in

  let add_decl (memtype : memtype) (vars, pty) : memtype =
    let ty = transty tp_tydecl env ue pty in

    let xs   = snd (unloc vars) in
    let mode = fst (unloc vars) in

    let xsvars = List.map (fun _ -> UE.fresh ue) xs in
    let () = match mode with
      | `Single ->
        List.iter (fun a -> EcUnify.unify env ue a ty) xsvars
      | `Tuple  ->
        unify_or_fail env ue (loc vars) ~expct:ty (ttuple xsvars) in

    (* building the list of locals *)
    let xs = List.map2 (fun x ty ->
        {v_name = x.pl_desc; v_type = ty}, x.pl_loc) xs xsvars in

    let mt = fundef_add_symbol_mt env memtype xs in
    (* REM *)
    Format.eprintf "dump: %s@." (EcMemory.dump_memtype mt);
    mt
  in

  List.fold_left add_decl mt pmemtype

(* -------------------------------------------------------------------- *)
and transexp env ?tt mode ue { pl_desc = Expr e; pl_loc = loc; } =
  let f = trans_form_or_pattern env (`Expr mode) ue e tt in
  let e =
    try
      match (EcEnv.Memory.get_active_ss env) with
      | None -> expr_of_form f
      | Some m -> expr_of_ss_inv {m;inv=f}
    with CannotTranslate ->
      (* This should not happen. *)
      tyerror loc env (NotAnExpression `Unknown) in
  (e, e.e_ty)

(* -------------------------------------------------------------------- *)
and transexpcast (env : EcEnv.env) mode ue t e =
  let (e', t') = transexp env mode ue e in
  unify_or_fail env ue e.pl_loc ~expct:t t'; e'

(* -------------------------------------------------------------------- *)
and transexpcast_opt (env : EcEnv.env) mode ue oty e =
  match oty with
  | None   -> fst (transexp env mode ue e)
  | Some t -> transexpcast env mode ue t e

(* -------------------------------------------------------------------- *)
and trans_form_opt env ?mv ue pf oty =
  trans_form_or_pattern env `Form ?mv ue pf oty

(* -------------------------------------------------------------------- *)
and trans_form env ?mv ue pf ty =
  trans_form_opt env ?mv ue pf (Some ty)

(* -------------------------------------------------------------------- *)
and trans_prop env ?mv ue pf =
  trans_form env ?mv ue pf tbool

(* -------------------------------------------------------------------- *)
and trans_pattern env ps ue pf =
  trans_form_or_pattern env `Form ~ps ue pf None

(* -------------------------------------------------------------------- *)
and trans_args env ue = transcall (transexp env `InProc ue) env ue

(* -------------------------------------------------------------------- *)
and trans_lv_match ?(memory : memory option) (env : EcEnv.env) (p : plvmatch) : lvmatch =
  match p with
  | `LvmNone as p -> (p :> lvmatch)
  | `LvmVar pv -> begin
    match memory with
    | None ->
      `LvmVar (fst (trans_pv env pv))
    | Some m ->
      `LvmVar (transpvar env m pv)
    end
(* -------------------------------------------------------------------- *)
and trans_cp_match ?(memory : memory option) (env : EcEnv.env) (p : pcp_match) : cp_match =
  match p with
  | (`While | `If | `Match) as p ->
    (p :> cp_match)
  | `Sample lv ->
    `Sample (trans_lv_match ?memory env lv)
  | `Call lv ->
    `Call (trans_lv_match ?memory env lv)
  | `Assign lv ->
    `Assign (trans_lv_match ?memory env lv)
  | `AssignTuple lv ->
    `AssignTuple (trans_lv_match ?memory env lv)
(* -------------------------------------------------------------------- *)
and trans_cp_base ?(memory : memory option) (env : EcEnv.env) (p : pcp_base) : cp_base =
  match p with
  | `ByPos _ as p -> (p :> cp_base)
  | `ByMatch (i, p) -> `ByMatch (i, trans_cp_match ?memory env p)

(* -------------------------------------------------------------------- *)
and trans_codepos1 ?(memory : memory option) (env : EcEnv.env) (p : pcodepos1) : codepos1 =
  snd_map (trans_cp_base ?memory env) p

(* -------------------------------------------------------------------- *)
and trans_codepos_brsel (bs : pbranch_select) : codepos_brsel =
  match bs with
  | `Cond b -> `Cond b
  | `Match { pl_desc = x } -> `Match x

(* -------------------------------------------------------------------- *)
and trans_codepos ?(memory : memory option) (env : EcEnv.env) ((nm, p) : pcodepos) : codepos =
  let nm = List.map (fun (cp1, bs) -> (trans_codepos1 ?memory env cp1, trans_codepos_brsel bs)) nm in
  let p = trans_codepos1 ?memory env p in
  (nm, p)

(* -------------------------------------------------------------------- *)
and trans_codepos_range ?(memory : memory option) (env : EcEnv.env) ((cps, cpe) : pcodepos_range) : codepos_range =
  let cps = trans_codepos ?memory env cps in
  let cpe =
    match cpe with
    | `Base cp ->
      `Base (trans_codepos ?memory env cp)
    | `Offset cp ->
      `Offset (trans_codepos1 ?memory env cp)
  in
  (cps, cpe)

(* -------------------------------------------------------------------- *)
and trans_dcodepos1 ?(memory : memory option) (env : EcEnv.env) (p : pcodepos1 doption) : codepos1 doption =
  DOption.map (trans_codepos1 ?memory env) p

and trans_codeoffset1 ?(memory: memory option) (env : EcEnv.env) (o : pcodeoffset1) : codeoffset1 =
  match o with
  | `ByOffset   i -> `ByOffset i
  | `ByPosition p -> `ByPosition (trans_codepos1 ?memory env p) 

(* -------------------------------------------------------------------- *)
let get_instances (tvi, bty) env =
  let inst = List.pmap
    (function
     | (_, (`Ring _ | `Field _)) as x -> Some x
     | _ -> None)
    (EcEnv.TypeClass.get_instances env) in

  List.pmap (fun ((typ, gty), cr) ->
    let ue = EcUnify.UniEnv.create (Some tvi) in
    let (gty, _typ) = EcUnify.UniEnv.openty ue typ None gty in
      try
        EcUnify.unify env ue bty gty;
        let ts = Tuni.subst (UE.close ue) in
        Some (inst, ty_subst ts gty, cr)
      with EcUnify.UnificationFailure _ -> None)
    inst

let get_ring (typ, ty) env =
  let module E = struct exception Found of ring end in
    try
      List.iter
        (fun (_, _, cr) ->
          match cr with
          | `Ring cr -> raise (E.Found cr)
          | _ -> ())
        (get_instances (typ, ty) env);
      None
    with E.Found cr -> Some cr

let get_field (typ, ty) env =
  let module E = struct exception Found of field end in
    try
      List.iter
        (fun (_, _, cr) ->
          match cr with
          | `Field cr -> raise (E.Found cr)
          | _ -> ())
        (get_instances (typ, ty) env);
      None
    with E.Found cr -> Some cr
