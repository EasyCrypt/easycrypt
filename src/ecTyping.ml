(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUid
open EcUtils
open EcPath
open EcMaps
open EcSymbols
open EcLocation
open EcParsetree
open EcTypes
open EcDecl
open EcModules
open EcFol

module MMsym = EcSymbols.MMsym
module Mid   = EcIdent.Mid

module EqTest = EcReduction.EqTest
module NormMp = EcEnv.NormMp

module TC = EcTypeClass

(* -------------------------------------------------------------------- *)
type opmatch = [
  | `Op   of EcPath.path * EcTypes.ty list
  | `Lc   of EcIdent.t
  | `Var  of EcTypes.prog_var
  | `Proj of EcTypes.prog_var * EcTypes.ty * (int * int)
]

type tymod_cnv_failure =
| E_TyModCnv_ParamCountMismatch
| E_TyModCnv_ParamTypeMismatch of EcIdent.t
| E_TyModCnv_MissingComp       of symbol
| E_TyModCnv_MismatchFunSig    of symbol

type modapp_error =
| MAE_WrongArgPosition
| MAE_WrongArgCount
| MAE_InvalidArgType
| MAE_AccesSubModFunctor

type modtyp_error =
| MTE_FunSigDoesNotRepeatArgNames
| MTE_InternalFunctor

type funapp_error =
| FAE_WrongArgCount

type mem_error =
| MAE_IsConcrete

type tyerror =
| UniVarNotAllowed
| FreeTypeVariables
| TypeVarNotAllowed
| OnlyMonoTypeAllowed
| UnboundTypeParameter   of symbol
| UnknownTypeName        of qsymbol
| UnknownTypeClass       of qsymbol
| UnknownRecFieldName    of qsymbol
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
| UnitFunWithReturn
| TypeMismatch           of (ty * ty) * (ty * ty)
| TypeClassMismatch
| TypeModMismatch        of tymod_cnv_failure
| NotAFunction
| UnknownVarOrOp         of qsymbol * ty list
| MultipleOpMatch        of qsymbol * ty list * (opmatch * EcUnify.unienv) list
| UnknownModName         of qsymbol
| UnknownTyModName       of qsymbol
| UnknownFunName         of qsymbol
| UnknownModVar          of qsymbol
| UnknownMemName         of int * symbol
| InvalidFunAppl         of funapp_error
| InvalidModAppl         of modapp_error
| InvalidModType         of modtyp_error
| InvalidMem             of symbol * mem_error
| FunNotInModParam       of qsymbol
| NoActiveMemory
| PatternNotAllowed
| MemNotAllowed
| UnknownScope           of qsymbol

exception TyError of EcLocation.t * EcEnv.env * tyerror

let tyerror loc env e = raise (TyError (loc, env, e))

(* -------------------------------------------------------------------- *)
let pp_cnv_failure fmt _env error =
  let msg x = Format.fprintf fmt x in

  match error with
  | E_TyModCnv_ParamCountMismatch ->
      msg "not the same number of module arguments"

  | E_TyModCnv_ParamTypeMismatch x ->
      msg "the module argument `%s' does not have the expected type"
        (EcIdent.name x)

  | E_TyModCnv_MissingComp x ->
      msg "the item `%s' is missing" x

  | E_TyModCnv_MismatchFunSig x ->
      msg "the item `%s' does not have a compatible kind/type" x

let pp_modappl_error fmt error =
  let msg x = Format.fprintf fmt x in

  match error with
  | MAE_WrongArgPosition ->
      msg "wrong arguments position"

  | MAE_WrongArgCount ->
      msg "wrong number of arguments"

  | MAE_InvalidArgType ->
      msg "arguments do not match required interfaces"

  | MAE_AccesSubModFunctor ->
      msg "cannot access a sub-module of a partially applied functor"

let pp_tyerror env fmt error =
  let env   = EcPrinting.PPEnv.ofenv env in
  let msg x = Format.fprintf fmt x in
  let pp_type fmt ty = EcPrinting.pp_type env fmt ty in

  match error with
  | UniVarNotAllowed ->
      msg "type place holders not allowed"

  | FreeTypeVariables ->
      msg "this expression contains free type variables"

  | TypeVarNotAllowed ->
      msg "type variables not allowed"

  | OnlyMonoTypeAllowed ->
      msg "%s, %s"
        "only monomorphic types are allowed"
        "you may have to add type annotations"

  | UnboundTypeParameter x ->
      msg "unbound type parameter: %s" x

  | UnknownTypeName qs ->
      msg "unknown type name: %a" pp_qsymbol qs

  | UnknownTypeClass qs ->
      msg "unknown type class: %a" pp_qsymbol qs

  | UnknownRecFieldName qs ->
      msg "unknown (record) field name: %a" pp_qsymbol qs

  | DuplicatedRecFieldName qs ->
      msg "duplicated (record) field name: %s" qs

  | MissingRecField qs ->
      msg "missing (record) field: %s" qs

  | MixingRecFields (p1, p2) ->
      msg "mixing (record) fields from different record types: %a / %a"
        (EcPrinting.pp_tyname env) p1
        (EcPrinting.pp_tyname env) p2

  | UnknownProj qs ->
      msg "unknown record projection: %a" pp_qsymbol qs

  | AmbiguousProj qs ->
      msg "ambiguous record projection: %a" pp_qsymbol qs

  | AmbiguousProji (i, ty) ->
    let i = max (i + 1) 2 in
    msg "type %a should be a tuple of at least %i elements" pp_type ty i 

  | InvalidTypeAppl (name, _, _) ->
      msg "invalid type application: %a" pp_qsymbol name

  | DuplicatedTyVar ->
      msg "a type variable appear at least twice"

  | DuplicatedLocal name ->
      msg "duplicated local/parameters name: `%s'" name

  | DuplicatedField name ->
      msg "duplicated field name: `%s'" name

  | NonLinearPattern ->
      msg "non-linear pattern matching"

  | LvNonLinear ->
      msg "This left-value is contains twice the same variable"

  | NonUnitFunWithoutReturn ->
      msg "This function must return a value"

  | UnitFunWithReturn ->
      msg "This void function cannot return a value"

  | TypeMismatch ((ty1, ty2), _) ->
      msg "This expression has type@\n";
      msg "  @[<hov 2> %a@]@\n" pp_type ty2;
      msg "but is expected to have type@\n";
      msg "  @[<hov 2> %a@]" pp_type ty1

  | TypeClassMismatch ->
      msg "Type-class unification failure"

  | TypeModMismatch err ->
      msg "this module body does not meet its interface:@\n";
      msg "  @[<hov 2>%t@]" (fun fmt -> pp_cnv_failure fmt env err)

  | NotAFunction ->
      msg "too many arguments"

  | UnknownVarOrOp (name, tys) -> begin
      match tys with
      | [] -> msg "unknown variable or constant: `%a'" pp_qsymbol name
      | _  ->
          msg
            "no matching operator, named `%a', for the following parameters' type:@\n"
            pp_qsymbol name;
          List.iteri (fun i ty -> msg "  [%d]: @[%a@]@\n" (i+1) pp_type ty) tys
  end

  | MultipleOpMatch (name, tys, matches) -> begin
      let uvars = List.map EcTypes.Tuni.univars tys in
      let uvars = List.fold_left Suid.union Suid.empty uvars in

      begin match tys with
      | [] ->
          msg
            "more that one variable or constant matches `%a'@\n"
            pp_qsymbol name
  
      | _  ->
          let pp_argty i ty = msg "  [%d]: @[%a@]@\n" (i+1) pp_type ty in
          msg "more than one operator, named `%a', matches.@\n@\n" pp_qsymbol name;
          msg "operator parameters' type were:@\n";
          List.iteri pp_argty tys
      end;
      msg "@\n";

      let pp_op fmt ((op, inst), subue) =
        let inst = Tuni.offun_dom (EcUnify.UniEnv.assubst subue) inst in

        begin match inst with
        | [] ->
            Format.fprintf fmt "%a"
              EcPrinting.pp_path op
        | _  ->
          Format.fprintf fmt "%a <%a>"
            EcPrinting.pp_path op
            (EcPrinting.pp_list ",@ " pp_type) inst
        end;

        let myuvars = List.map EcTypes.Tuni.univars inst in
        let myuvars = List.fold_left Suid.union uvars myuvars in
        let myuvars = Suid.elements myuvars in

        let tysubst = Tuni.offun (EcUnify.UniEnv.assubst subue) in
        let myuvars = List.pmap
          (fun uid ->
            match tysubst (tuni uid) with
            | { ty_node = Tunivar uid' } when uid = uid' -> None
            | ty -> Some (uid, ty))
          myuvars
        in

        if not (List.isempty myuvars) then begin
          Format.fprintf fmt "@\n    where@\n";
          List.iter (fun (uid, uidty) ->
            Format.fprintf fmt "      %a = %a@\n"
              (EcPrinting.pp_tyunivar env) uid pp_type uidty)
            myuvars
        end
      in

      msg "the list of matching objects follows:@\n";
      List.iter (fun (m, ue) ->
        let (title, Cb (x, pp)) =
          match m with
          | `Var  pv         -> ("prog. variable", Cb (pv      , EcPrinting.pp_pv env))
          | `Lc   id         -> ("local variable", Cb (id      , EcPrinting.pp_local env))
          | `Proj (pv, _, _) -> ("variable proj.", Cb (pv      , EcPrinting.pp_pv env))
          | `Op   op         -> ("operator"      , Cb ((op, ue), pp_op))
        in
          msg "  [%s]: %a@\n" title pp x)
        matches
  end

  | UnknownModName name ->
      msg "unknown module: %a" pp_qsymbol name

  | UnknownTyModName name ->
      msg "unknown type name: %a" pp_qsymbol name

  | UnknownFunName name ->
      msg "unknown function: %a" pp_qsymbol name

  | UnknownModVar x ->
      msg "unknown module-level variable: %a" pp_qsymbol x

  | UnknownMemName (g, m) ->
      msg "unknown memory: %s[g=%d]" m g

  | InvalidFunAppl FAE_WrongArgCount ->
      msg "invalid function application: wrong number of arguments"

  | InvalidModAppl err ->
      msg "invalid module application:@ %a" pp_modappl_error err

  | InvalidModType MTE_FunSigDoesNotRepeatArgNames ->
      msg "applied argument names must repeat functor argument names"

  | InvalidModType MTE_InternalFunctor ->
      msg "functors must be top-level modules"

  | InvalidMem (name, MAE_IsConcrete) ->
      msg "the memory %s must be abstract" name

  | FunNotInModParam name ->
      msg "the function %a is not provided by a module parameter"
        pp_qsymbol name

  | NoActiveMemory ->
      msg "no active memory at this point"

  | PatternNotAllowed ->
      msg "pattern not allowed here"

  | MemNotAllowed ->
      msg "memory not allowed here"

  | UnknownScope sc ->
      msg "unknown scope: `%a'" pp_qsymbol sc

let () =
  let pp fmt exn =
    match exn with
    | TyError (_, env, e) ->
        pp_tyerror env fmt e
    | _ -> raise exn
  in
    EcPException.register pp

(* -------------------------------------------------------------------- *)
type ptnmap = ty EcIdent.Mid.t ref

(* -------------------------------------------------------------------- *)
module UE = EcUnify.UniEnv

let unify_or_fail (env : EcEnv.env) ue loc ~expct:ty1 ty2 = 
  try  EcUnify.unify env ue ty1 ty2 
  with EcUnify.UnificationFailure pb ->
    match pb with
    | `TyUni (t1, t2)->
        let tyinst = Tuni.offun (UE.assubst ue) in
          tyerror loc env (TypeMismatch ((tyinst ty1, tyinst ty2),
                                         (tyinst  t1, tyinst  t2)))
    | `TcCtt _ ->
        tyerror loc env TypeClassMismatch

(* -------------------------------------------------------------------- *)
let e_inuse =
  let rec inuse (map : Sx.t) (e : expr) =
    match e.e_node with
    | Evar p -> begin
        match p.pv_kind with
        | PVglob -> Sx.add p.pv_name map
        | _      -> map
      end
    | _ -> e_fold inuse map e
  in
    fun e -> inuse Sx.empty e

(* -------------------------------------------------------------------- *)
let empty_uses : uses = mk_uses [] Sx.empty Sx.empty

let add_call (u : uses) p : uses =
  mk_uses (p::u.us_calls) u.us_reads u.us_writes

let add_read (u : uses) p : uses =
  if is_glob p then 
    mk_uses u.us_calls (Sx.add p.pv_name u.us_reads) u.us_writes
  else u 

let add_write (u : uses) p : uses =
  if is_glob p then
    mk_uses u.us_calls u.us_reads (Sx.add p.pv_name u.us_writes)
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

    | LvMap (_, p, e, _) ->
      (* Maps are not modified in place but feed to a mutator
         operator that returns the augmented map and assigning the
         result to [p]. Hence the [`Read | `Write] flag. *)
      let map = add_write (add_read map p) p in
      let map = se_inuse map e in
        map

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

    | Sassert e ->
      se_inuse map e
    | Sabstract _ -> assert false (* FIXME *)

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
let select_pv env side name ue tvi psig = 
  if   tvi <> None
  then []
  else
    try
      let pvs = EcEnv.Var.lookup_progvar ?side name env in 
      let select (pv,ty) = 
        let subue = UE.copy ue in
        let texpected = EcUnify.tfun_expected subue psig in
          try
            EcUnify.unify env subue ty texpected;
            [(pv, ty, subue)]
          with EcUnify.UnificationFailure _ -> []
      in
        select pvs
    with EcEnv.LookupFailure _ -> []

(* -------------------------------------------------------------------- *)
module OpSelect = struct
  type 'a ctargs = 'a * EcTypes.ty

  type pvctor = [
    | `Proj of EcTypes.prog_var * EcTypes.ty * (int * int)
    | `Var  of EcTypes.prog_var
  ]

  type opctor = EcPath.path * EcTypes.ty list

  type 'a ctor = {
    ct_pv : EcMemory.memory option -> pvctor ctargs  -> 'a;
    ct_op : opctor ctargs -> 'a;
    ct_lc : EcIdent.ident ctargs -> 'a;
  }

  type mode = [`Form | `Expr of [`InProc | `InOp]]
end

let gen_select_op
    ~(actonly : bool)
    ~(mode    : OpSelect.mode)
    (ctor     : 'a OpSelect.ctor)
    (opsc     : path option)
    (tvi      : EcUnify.tvi)
    (env      : EcEnv.env)
    (name     : EcSymbols.qsymbol)
    (ue       : EcUnify.unienv)
    (psig     : EcTypes.dom)

    : ('a * EcTypes.ty * EcUnify.unienv * opmatch) list
=

  let open OpSelect in

  let fpv me (pv, ty, ue) = (ctor.ct_pv me (pv, ty), ty, ue, (pv     :> opmatch)) in
  let fop    (op, ty, ue) = (ctor.ct_op    (op, ty), ty, ue, (`Op op :> opmatch)) in
  let flc    (lc, ty, ue) = (ctor.ct_lc    (lc, ty), ty, ue, (`Lc lc :> opmatch)) in

  let filter =
    match mode with
    | `Expr _ -> fun op -> not (EcDecl.is_pred op)
    | `Form   -> fun _  -> true
  in

  match (if tvi = None then select_local env name else None) with
  | Some (id, ty) -> [ flc (id, ty, ue) ]

  | None ->
      let ops = EcUnify.select_op ~filter tvi env name ue psig in
      let ops =
        match ops, opsc with
        | _ :: _ :: _, Some opsc ->
            List.filter
              (fun ((p, _), _, _) ->
                  EcPath.p_equal opsc (oget (EcPath.prefix p)))
              ops
        | _, _ -> ops
      in

      let ops =
        match
          List.filter
            (fun ((p, _), _, _) ->
               match oget (EcEnv.Op.by_path_opt p env) with
               | { op_kind = OB_oper (Some OP_TC) } -> false
               | _ -> true)
            ops
        with
        | []   -> ops
        | notc -> notc
      in

      let me, pvs =
        match mode with
        | `Expr `InOp ->
            (None, [])
        | `Expr `InProc | `Form ->
            match EcEnv.Memory.get_active env, actonly with
            | None, true -> (None, [])
            | me  , _    -> (  me, select_pv env me name ue tvi psig)
      in
        (List.map (fpv me) pvs) @ (List.map fop ops)

(* -------------------------------------------------------------------- *)
let select_exp_op env mode opsc name ue tvi psig =
  let ctor =
    let ppv = (fun _ (pv, ty) -> match pv with
      | `Var   pv               -> e_var pv ty
      | `Proj (pv, _  , (0, 1)) -> e_var pv ty
      | `Proj (pv, ty', (i, _)) -> e_proj (e_var pv ty') i ty)

    and pop  = (fun ((op, tys), ty) -> e_op op tys ty)
    and flc  = (fun (id, ty) -> e_local id ty) in

    { OpSelect.ct_pv = ppv;
      OpSelect.ct_op = pop;
      OpSelect.ct_lc = flc; }
  in

  gen_select_op ~actonly:false ~mode:(`Expr mode)
    ctor opsc tvi env name ue psig

(* -------------------------------------------------------------------- *)
let select_form_op env opsc name ue tvi psig =
  let ctor =
    let ppv = (fun me (pv, ty) -> 
      match pv with 
      | `Var   pv               -> f_pvar pv ty (oget me)
      | `Proj (pv, _  , (0, 1)) -> f_pvar pv ty (oget me)
      | `Proj (pv, ty', (i, _)) -> f_proj (f_pvar pv ty' (oget me)) i ty)

    and pop = (fun ((op, tys), ty) -> f_op op tys ty)
    and flc = (fun (id, ty) -> f_local id ty) in

    { OpSelect.ct_pv = ppv;
      OpSelect.ct_op = pop;
      OpSelect.ct_lc = flc; }
  in

  gen_select_op ~actonly:true ~mode:`Form
    ctor opsc tvi env name ue psig 

(* -------------------------------------------------------------------- *)
let select_proj env opsc name ue tvi recty =
  let filter = (fun op -> EcDecl.is_proj op) in
  let ops = EcUnify.select_op ~filter tvi env name ue [recty] in

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
  tp_uni  : bool;   (* "_" (Tuniar) allowed  *)
  tp_tvar : bool;   (* type variable allowed *)
}

let tp_tydecl  = { tp_uni = false; tp_tvar = true ; } (* type decl. *)
let tp_relax   = { tp_uni = true ; tp_tvar = true ; } (* ops/forms/preds *)
let tp_nothing = { tp_uni = false; tp_tvar = false; } (* module type annot. *)
let tp_uni     = { tp_uni = true ; tp_tvar = false; } (* params/local vars. *)

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
        let for1 ({ pl_desc = x }, tc) = (EcIdent.create x, transtcs env tc) in
          if not (List.uniq (List.map (unloc |- fst) tparams)) then
            tyerror loc env DuplicatedTyVar;
          List.map for1 tparams)
  in
    EcUnify.UniEnv.create tparams

(* -------------------------------------------------------------------- *)
exception TymodCnvFailure of tymod_cnv_failure

let tymod_cnv_failure e =
  raise (TymodCnvFailure e)

let tysig_item_name = function
  | Tys_function (f, _) -> f.fs_name

let tysig_item_kind = function
  | Tys_function _ -> `Function

let rec check_sig_cnv mode (env:EcEnv.env) (sin:module_sig) (sout:module_sig) = 
  (* Check parameters for compatibility. Parameters names may be
   * different, hence, substitute in [tin.tym_params] types the names
   * of [tout.tym_params] *)
  
  if List.length sin.mis_params <> List.length sout.mis_params then
    tymod_cnv_failure E_TyModCnv_ParamCountMismatch;

  let bsubst =
    List.fold_left2
      (fun subst (xin, tyin) (xout, tyout) ->
        let tyout = EcSubst.subst_modtype subst tyout in
        check_modtype_cnv env tyin tyout;
        EcSubst.add_module subst xout (EcPath.mident xin))
      EcSubst.empty sin.mis_params sout.mis_params
  in
  (* Check for body inclusion (w.r.t the parameters names substitution).
   * This includes:
   * - functions inclusion with equal signatures + included use modifiers.
   *)
  let tin  = sin.mis_body 
  and tout = EcSubst.subst_modsig_body bsubst sout.mis_body in

  let env = 
    List.fold_left (fun env (xin,tyin) ->
      EcEnv.Mod.bind_local xin tyin (EcPath.Sx.empty, EcPath.Sm.empty) env)
      env sin.mis_params in

  let check_item_compatible = 
    let check_fun_compatible (fin,oin) (fout,oout) =
      assert (fin.fs_name = fout.fs_name);
 
      let (iargs, oargs) = (fin.fs_arg, fout.fs_arg) in
      let (ires , ores ) = (fin.fs_ret, fout.fs_ret) in

      if not (EqTest.for_type env iargs oargs) then
        tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);

      if not (EqTest.for_type env ires ores) then
          tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);

        let flcmp () =
          let norm oi = 
            List.fold_left (fun s f -> 
              EcPath.Sx.add (EcEnv.NormMp.norm_xfun env f) s)
              EcPath.Sx.empty oi.oi_calls
          in
          let icalls = norm oin in
          let ocalls = norm oout in
          match mode with
          | `Sub -> Sx.subset icalls ocalls
          | `Eq  -> Sx.equal  icalls ocalls
        in
        if not (flcmp ()) then
          tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);
        
    in
      fun i_item o_item ->
        match i_item, o_item with
        | Tys_function (fin,oin), Tys_function (fout,oout) -> 
          check_fun_compatible (fin,oin) (fout,oout)
  in

  let check_for_item (o_item : module_sig_body_item) =
    let o_name = tysig_item_name o_item
    and o_kind = tysig_item_kind o_item in

    let i_item =
      List.findopt
        (fun i_item ->
             (tysig_item_name i_item) = o_name
          && (tysig_item_kind i_item) = o_kind)
        tin
    in
      match i_item with
      | None -> tymod_cnv_failure (E_TyModCnv_MissingComp o_name)
      | Some i_item -> check_item_compatible i_item o_item
  in
    List.iter check_for_item tout;

    if mode = `Eq then begin
      List.iter
        (fun i_item ->
          let i_name = tysig_item_name i_item
          and i_kind = tysig_item_kind i_item in
          let b =
            List.exists
              (fun o_item ->
                   (tysig_item_name o_item) = i_name
                && (tysig_item_kind o_item) = i_kind)
              tout
          in
            if not b then
              tymod_cnv_failure (E_TyModCnv_MissingComp i_name))
        tin
    end

and check_modtype_cnv env (tyin:module_type) (tyout:module_type) = 
  let sin = EcEnv.ModTy.sig_of_mt env tyin in
  let sout = EcEnv.ModTy.sig_of_mt env tyout in
  check_sig_cnv `Eq env sin sout

let check_sig_mt_cnv env sin tyout = 
  let sout = EcEnv.ModTy.sig_of_mt env tyout in
  check_sig_cnv `Sub env sin sout

(* -------------------------------------------------------------------- *)
type restriction_who =
| RW_mod of EcPath.mpath
| RW_fun of EcPath.xpath 

type restriction_err =
| RE_UseVariable          of EcPath.xpath
| RE_UseVariableViaModule of EcPath.xpath * EcPath.mpath
| RE_UseModule            of EcPath.mpath
| RE_VMissingRestriction  of EcPath.xpath * EcPath.mpath pair
| RE_MMissingRestriction  of EcPath.mpath * EcPath.mpath pair

type restriction_error = restriction_who * restriction_err

exception RestrictionError of restriction_error

let pp_restriction_error env fmt (w, e) = 
  let ppe = EcPrinting.PPEnv.ofenv env in
  let pp_v fmt xp = EcPrinting.pp_pv ppe fmt (pv_glob xp) in
  let pp_m fmt m  = EcPrinting.pp_topmod ppe fmt m in

  let pp_restriction_who fmt = function
    | RW_mod mp ->
        Format.fprintf fmt "the module %a" pp_m mp

    | RW_fun xp ->
        Format.fprintf fmt "the procedure %a" (EcPrinting.pp_funname ppe) xp in

  let pp_restriction_err fmt = function
    | RE_UseVariable x -> 
        Format.fprintf fmt
          "should not be able to use the variable %a"
          pp_v x

    | RE_UseVariableViaModule (x, m) -> 
        Format.fprintf fmt
          "should not be able to use %a (via %a)"
          pp_v x pp_m m

    | RE_UseModule m -> 
        Format.fprintf fmt
          "should not be able to use the module %a"
          pp_m m

    | RE_VMissingRestriction (x, (m1, m2))->
        Format.fprintf fmt
          "should not be able to use %a, add restriction %a to %a"
          pp_v x pp_m m1 pp_m m2

    | RE_MMissingRestriction (m, (m1, m2))->
        Format.fprintf fmt
          "should not be able to use %a, add restriction %a to %a or %a to %a"
          pp_m m pp_m m1 pp_m m2 pp_m m2 pp_m m1

  in Format.fprintf fmt "%a %a" pp_restriction_who w pp_restriction_err e

(* -------------------------------------------------------------------- *)
let check_restrictions env who use restr =
  let re_error = fun x -> raise (RestrictionError (who, x)) in

  let restr = NormMp.norm_restr env restr in

  let check_xp xp _ =
    (* We check that the variable is not a variable in restr *)
    if NormMp.use_mem_xp xp restr then
      re_error (RE_UseVariable xp);

    (* We check that the variable is in the restriction of the
     * abstract module in restr. *)
    let check id2 =
      let mp2 = EcPath.mident id2 in
      let r2  = NormMp.get_restr env mp2 in

      if not (NormMp.use_mem_xp xp r2) then
        re_error (RE_UseVariableViaModule (xp, mp2));
    in
      EcIdent.Sid.iter check restr.EcEnv.us_gl
  in
  EcPath.Mx.iter check_xp (use.EcEnv.us_pv);

  let check_gl id =
    let mp1 = EcPath.mident id in

    if NormMp.use_mem_gl mp1 restr then
      re_error (RE_UseModule mp1);

    let r1 = NormMp.get_restr env mp1 in

    let check_v xp2 _ =
      if not (NormMp.use_mem_xp xp2 r1) then
        re_error (RE_VMissingRestriction (xp2, (xp2.x_top, mp1)))
    in
    Mx.iter check_v restr.EcEnv.us_pv;

    let check_g id2 =
      let mp2 = EcPath.mident id2 in

      if not (NormMp.use_mem_gl mp2 r1) then
        let r2 = NormMp.get_restr env mp2 in
        if not (NormMp.use_mem_gl mp1 r2) then
          re_error (RE_MMissingRestriction (mp1, (mp1, mp2)));
    in
    EcIdent.Sid.iter check_g restr.EcEnv.us_gl

  in
  EcIdent.Sid.iter check_gl use.EcEnv.us_gl

let check_restrictions_fun env xp use restr =
  check_restrictions env (RW_fun xp) use restr 

(* -------------------------------------------------------------------- *)
let check_modtype_with_restrictions env mp mt i restr =
  check_sig_mt_cnv env mt i;
  let use = NormMp.mod_use env mp in
  check_restrictions env (RW_mod mp) use restr

(* -------------------------------------------------------------------- *)
let split_msymb (env : EcEnv.env) (msymb : pmsymbol located) =
  let (top, args, sm) = 
    try
      let (r, (x, args), sm) =
        List.find_split (fun (_,args) -> args <> None) msymb.pl_desc
      in
        (List.rev_append r [x, None], args, sm)
    with Not_found ->
      (msymb.pl_desc, None, [])
  in

  let (top, sm) =
    let ca (x, args) =
      if args <> None then
        tyerror msymb.pl_loc env (InvalidModAppl MAE_WrongArgPosition);
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
    | Some me -> me
  in

  let (params, istop) =
    match top_path.EcPath.m_top with
    | `Concrete (_, Some sub) ->
        if mod_expr.me_sig.mis_params <> [] then
          assert false;
        if args <> None then
          if not (EcPath.p_size sub = List.length sm) then
            tyerror loc env (InvalidModAppl MAE_WrongArgPosition);
        (params, false)

    | `Concrete (p, None) ->
        if (params <> []) || ((spi+1) <> EcPath.p_size p) then
          assert false;
        (mod_expr.me_sig.mis_params, true)

    | `Local _m ->
        if (params <> []) || spi <> 0 then
          assert false;
        (mod_expr.me_sig.mis_params, true)
  in

  let args = args |> omap (List.map (trans_msymbol env)) in

  match args with
  | None ->
    if not istop && params <> [] then
      tyerror loc env (InvalidModAppl MAE_AccesSubModFunctor); 

    (top_path, mod_expr.me_sig)

  | Some args ->
      if List.length args > List.length params then
        tyerror loc env (InvalidModAppl MAE_WrongArgCount);

      let params, remn = List.take_n (List.length args) params in

      List.iter2
        (fun (_, p) (_, a) ->
          try check_sig_mt_cnv env a p
          with TymodCnvFailure _ ->
            tyerror loc env (InvalidModAppl MAE_InvalidArgType))
        params args;

      let args  = List.map fst args in
      let subst = 
          List.fold_left2
            (fun s (x,_) a -> EcSubst.add_module s x a) 
            EcSubst.empty params args
      in

      let keepcall =
        let used = EcIdent.Sid.of_list (List.map fst params) in
          fun xp ->
            match xp.EcPath.x_top.EcPath.m_top with
            | `Local id -> not (EcIdent.Sid.mem id used)
            | _ -> true
      in

      let body =
        List.map 
          (fun (Tys_function (s, oi)) ->
            Tys_function(s, { oi_calls = List.filter keepcall oi.oi_calls;
                              oi_in    = oi.oi_in; }))
          mod_expr.me_sig.mis_body
      in
      let body = EcSubst.subst_modsig_body subst body in

        (EcPath.mpath top_path.EcPath.m_top args, {mis_params = remn; mis_body = body})

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
    let m,_ = trans_msymbol env gp in
    tglob m

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
      if not (List.uniq xs) then
        tyerror p.pl_loc env NonLinearPattern
      else
        let xs     = List.map EcIdent.create xs in
        let subtys = List.map (fun _ -> UE.fresh ue) xs in
        (LTuple (List.combine xs subtys), ttuple subtys)

  | LPRecord fields ->
      let xs = List.map (unloc |- snd) fields in
      if not (List.uniq xs) then
        tyerror p.pl_loc env NonLinearPattern;

      let fields =
        let for1 (name, v) =
          let filter = fun op -> EcDecl.is_proj op in
          let fds    = EcUnify.select_op ~filter None env (unloc name) ue [] in
            match List.ohead fds with
            | None ->
              let exn = UnknownRecFieldName (unloc name) in
                tyerror name.pl_loc env exn

            | Some ((fp, _tvi), opty, subue) ->
              let field = oget (EcEnv.Op.by_path_opt fp env) in
              let (recp, fieldidx, _) = EcDecl.operator_as_proj field in
                EcUnify.UniEnv.restore ~src:subue ~dst:ue;
                ((recp, fieldidx), opty, (name, v))
        in
          List.map for1 fields in

      let recp = Sp.of_list (List.map (fst |- proj3_1) fields) in
      let recp =
        match Sp.elements recp with
        | []        -> assert false
        | [recp]    -> recp
        | p1::p2::_ -> tyerror p.pl_loc env (MixingRecFields (p1, p2))
      in

      let recty  = oget (EcEnv.Ty.by_path_opt recp env) in
      let rec_   = snd (EcDecl.tydecl_as_record recty) in
      let reccty = tconstr recp (List.map (tvar |- fst) recty.tyd_params) in
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
          ty_fun_app loc env ue codom targs
  end

let transbinding env ue bd =
  let trans_bd1 env (xs, pty) = 
    let ty = transty tp_relax env ue pty in
    let xs = List.map (fun x -> EcIdent.create x.pl_desc, ty) xs in
    let env = EcEnv.Var.bind_locals xs env in
    env, xs in
  let env, bd = List.map_fold trans_bd1 env bd in
  let bd = List.flatten bd in
  env, bd

(* -------------------------------------------------------------------- *)
let trans_record env ue subtt (loc, fields) =                                                                    
  let fields =
    let for1 rf =
      let filter = fun op -> EcDecl.is_proj op in
      let tvi    = rf.rf_tvi |> omap (transtvi env ue) in
      let fds    = EcUnify.select_op ~filter tvi env (unloc rf.rf_name) ue [] in
        match List.ohead fds with
        | None ->
            let exn = UnknownRecFieldName (unloc rf.rf_name) in
              tyerror rf.rf_name.pl_loc env exn

        | Some ((fp, _tvi), opty, subue) ->
            let field = oget (EcEnv.Op.by_path_opt fp env) in
            let (recp, fieldidx, _) = EcDecl.operator_as_proj field in
              EcUnify.UniEnv.restore ~src:subue ~dst:ue;
              ((recp, fieldidx), opty, rf)
    in
      List.map for1 fields in

  let recp = Sp.of_list (List.map (fst |- proj3_1) fields) in
  let recp =
    match Sp.elements recp with
    | []        -> assert false
    | [recp]    -> recp
    | p1::p2::_ -> tyerror loc env (MixingRecFields (p1, p2))
  in

  let recty  = oget (EcEnv.Ty.by_path_opt recp env) in
  let rec_   = snd (EcDecl.tydecl_as_record recty) in
  let reccty = tconstr recp (List.map (tvar |- fst) recty.tyd_params) in
  let reccty, rtvi = EcUnify.UniEnv.openty ue recty.tyd_params None reccty in
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

  List.iteri
    (fun i (name, _) ->
       if not (Mint.mem i fields) then
         let exn = MissingRecField name in
           tyerror loc env exn)
    rec_;

  let fields = Mint.values fields in (* sorted by field idx *)
  let fields =
    let for1 (_, opty, rf) =
      let pty = EcUnify.UniEnv.fresh ue in
      (try  EcUnify.unify env ue (tfun reccty pty) opty
       with EcUnify.UnificationFailure _ -> assert false);
      let e, ety = subtt rf.rf_value in
      unify_or_fail env ue rf.rf_value.pl_loc ~expct:pty ety;
      (e, ety)
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
let transexp (env : EcEnv.env) mode ue e =
  let rec transexp_r (osc : EcPath.path option) (env : EcEnv.env) (e : pexpr) =
    let loc = e.pl_loc in
    let transexp = transexp_r osc in

    match e.pl_desc with
    | PEint i -> (e_int i, tint)

    | PEident ({ pl_desc = name }, tvi) -> 
        let tvi = tvi |> omap (transtvi env ue) in
        let ops = select_exp_op env mode osc name ue tvi [] in
        begin match ops with
        | [] -> tyerror loc env (UnknownVarOrOp (name, []))

        | [op, ty, subue, _] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            op, ty

        | _ ->
          let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
          tyerror loc env (MultipleOpMatch (name, [], matches))
        end

    | PEscope (popsc, e) ->
        let opsc = lookup_scope env popsc in
          transexp_r (Some opsc) env e

    | PEapp ({pl_desc = PEident({ pl_desc = name; pl_loc = loc }, tvi)}, pes) ->
        let tvi  = tvi |> omap (transtvi env ue) in  
        let es   = List.map (transexp env) pes in
        let esig = snd (List.split es) in
        let ops  = select_exp_op env mode osc name ue tvi esig in
        begin match ops with
        | [] ->
            let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
            tyerror loc env (UnknownVarOrOp (name, esig))

        | [op, ty, subue, _] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            let esig = List.map2 (fun e l -> mk_loc l.pl_loc e) esig pes in
            let codom = ty_fun_app _dummy env ue ty esig in
              (e_app op (List.map fst es) codom, codom)

        | _ ->
            let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
            let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
            tyerror loc env (MultipleOpMatch (name, esig, matches))
        end

    | PEapp (pe, pes) ->
        let e, ty = transexp env pe in
        let es = List.map (transexp env) pes in
        let esig = List.map2 (fun (_, ty) l -> mk_loc l.pl_loc ty) es pes in
        let codom = ty_fun_app loc env ue ty esig in
          (e_app e (List.map fst es) codom, codom)

    | PElet (p, (pe1, paty), pe2) ->
        let (penv, pt, pty) = transpattern env ue p in
        let aty = paty |> omap (transty tp_relax env ue) in

        let e1, ty1 = transexp env pe1 in
        unify_or_fail env ue pe1.pl_loc ~expct:pty ty1;
        aty |> oiter (fun aty -> unify_or_fail env ue pe1.pl_loc ~expct:aty ty1);
  
        let e2, ty2 = transexp penv pe2 in
        (e_let pt e1 e2, ty2)

    | PEtuple es -> begin
        let tes = List.map (transexp env) es in

        match tes with
        | []      -> (e_tt, EcTypes.tunit)
        | [e, ty] -> (e, ty)
        | _       ->
            let es, tys = List.split tes in
              (e_tuple es, ttuple tys)
    end

    | PEif (pc, pe1, pe2) ->
      let c, tyc = transexp env pc in
      let e1, ty1 = transexp env pe1 in
      let e2, ty2 = transexp env pe2 in
        unify_or_fail env ue pc .pl_loc ~expct:tbool tyc;
        unify_or_fail env ue pe2.pl_loc ~expct:ty1   ty2;
        (e_if c e1 e2, ty1)

    | PElambda (bd, pe) ->
        let env, xs = transbinding env ue bd in
        let e, ty = transexp env pe in
        let ty =
          List.fold_right
            (fun (_, xty) ty -> EcTypes.tfun xty ty)
            xs ty
        in
          (e_lam xs e, ty)

    | PErecord fields ->
        let (ctor, fields, (rtvi, reccty)) =
          trans_record env ue (transexp env) (loc, fields) in
        let ctor = e_op ctor rtvi (toarrow (List.map snd fields) reccty) in
        let ctor = e_app ctor (List.map fst fields) reccty in
          ctor, reccty

    | PEproj (sube, x) -> begin
      let sube, ety = transexp env sube in
      match select_proj env osc (unloc x) ue None ety with
      | [] -> 
        let ty = Tuni.offun (EcUnify.UniEnv.assubst ue) ety in
        let me = EcFol.mhr in
        let mp = 
          match ty.ty_node with
          | Tglob mp -> mp 
          | _ -> tyerror x.pl_loc env (UnknownProj (unloc x)) in
        let f = NormMp.norm_glob env me mp in
        let lf = 
          match f.f_node with
          | Ftuple l -> l 
          | _ -> tyerror x.pl_loc env (UnknownProj (unloc x)) in
        let vx,ty =
          match EcEnv.Var.lookup_progvar_opt ~side:me (unloc x) env with
          | None -> tyerror x.pl_loc env (UnknownVarOrOp (unloc x, []))
          | Some (x1, ty) -> 
              match x1 with
              | `Var x -> NormMp.norm_pvar env x, ty 
              | _ -> tyerror x.pl_loc env (UnknownVarOrOp (unloc x, [])) in 
        let find f1 =
           match f1.f_node with
            | Fpvar (x1, _) -> EcTypes.pv_equal vx (NormMp.norm_pvar env x1)
            | _ -> false in 
        let i = 
          match List.findex find lf with
          | None -> tyerror x.pl_loc env (UnknownProj (unloc x))
          | Some i -> i in
        e_proj sube i ty, ty
        

      | _::_::_ -> tyerror x.pl_loc env (AmbiguousProj (unloc x))
      | [(op, tvi), pty, subue] ->
        EcUnify.UniEnv.restore ~src:subue ~dst:ue;
        let rty = EcUnify.UniEnv.fresh ue in
        (try  EcUnify.unify env ue (tfun ety rty) pty
         with EcUnify.UnificationFailure _ -> assert false);
        (e_app (e_op op tvi pty) [sube] rty, rty)
    end
    | PEproji(sube, i) -> begin
      let sube', ety = transexp env sube in
      let ty = Tuni.offun (EcUnify.UniEnv.assubst ue) ety in
      match (EcEnv.Ty.hnorm ty env).ty_node with
      | Ttuple l when i < List.length l ->
        let ty = List.nth l i in
        e_proj sube' i ty, ty
      | _ -> tyerror sube.pl_loc env (AmbiguousProji(i,ty))
    end
        
  in
    transexp_r None env e

let transexpcast (env : EcEnv.env) mode ue t e =
  let (e', t') = transexp env mode ue e in
    unify_or_fail env ue e.pl_loc ~expct:t t'; e'

let transexpcast_opt (env : EcEnv.env) mode ue oty e =
  match oty with
  | None   -> fst (transexp env mode ue e)
  | Some t -> transexpcast env mode ue t e

(* -------------------------------------------------------------------- *)
exception DuplicatedSigItemName
exception DuplicatedArgumentsName of pfunction_decl

(* -------------------------------------------------------------------- *)
let name_of_sigitem = function
  | `FunctionDecl f -> f.pfd_name

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
  let (p, sig_) = lookup_module_type env modty in
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
        if _sig.mis_params <> [] then
          tyerror gp.pl_loc env (UnknownFunName (modsymb, funsymb));
        EcPath.xpath_fun mpath funsymb

(* -------------------------------------------------------------------- *)
let rec transmodsig (env : EcEnv.env) (name : symbol) (modty : pmodule_sig) =
  let Pmty_struct modty = modty in

  let margs =
    List.map (fun (x, i) ->
      (EcIdent.create (unloc x), fst (transmodtype env i)))
      modty.pmsig_params
  in
  let sa = 
    List.fold_left (fun sa (x,_) -> Sm.add (EcPath.mident x) sa) Sm.empty margs
  in
  let env  = EcEnv.Mod.enter name margs env in
  let body = transmodsig_body env sa modty.pmsig_body in
  { mis_params = margs;
    mis_body   = body; }

(* -------------------------------------------------------------------- *)
and transmodsig_body (env : EcEnv.env) (sa : Sm.t)
    (is : pmodule_sig_struct_body) =
  let transsig1 (`FunctionDecl f) =
    let name   = f.pfd_name in
    let tyarg, tyargs =
      match f.pfd_tyargs with
      | Fparams_exp l ->
        let tyargs = 
          List.map                          (* FIXME: continuation *)
            (fun (x, ty) -> { v_name = x.pl_desc; 
                              v_type = transty_for_decl env ty}) l in
        if not (List.uniq (List.map fst l)) then
          raise (DuplicatedArgumentsName f);
        let tyarg = ttuple (List.map (fun vd -> vd.v_type) tyargs) in
        tyarg, Some tyargs
      | Fparams_imp ty ->
        let tyarg = transty_for_decl env ty in
        tyarg, None in

    let resty = transty_for_decl env f.pfd_tyresult in

    let (uin, calls) =
      let calls =
        match snd f.pfd_uses with
        | None -> 
            let do_one mp calls = 
              let sig_ = (EcEnv.Mod.by_mpath mp env).me_sig in
                if sig_.mis_params <> [] then calls
                else
                  let fs = List.map (fun (Tys_function (fsig, _)) ->
                    EcPath.xpath_fun mp fsig.fs_name) sig_.mis_body
                  in
                    fs@calls
            in
              Sm.fold do_one sa []
  
        | Some pfd_uses ->
            List.map (fun name -> 
              let f = fst (lookup_fun env name) in
              let p = f.EcPath.x_top in
                if not (Sm.mem p sa) then 
                  tyerror name.pl_loc env (FunNotInModParam name.pl_desc);
                f)
              pfd_uses
      in
        (fst f.pfd_uses, calls)
    in

    let sig_ = { fs_name   = name.pl_desc;
                 fs_arg    = tyarg;
                 fs_anames = tyargs;
                 fs_ret    = resty; }
    and oi = { oi_calls = calls; oi_in = uin; } in
      Tys_function (sig_, oi)

  in

  let items = List.map transsig1 is in
  let names = List.map name_of_sigitem is in

    if not (List.uniq names) then
      raise DuplicatedSigItemName
    else
      items

(* -------------------------------------------------------------------- *)
let rec transmod ~attop (env : EcEnv.env) (x : symbol) (me : pmodule_expr) =
  match me.pl_desc with
  | Pm_ident (params,m) -> 
    let stparams, env = transmod_params env x params in
    let (mp, sig_) = trans_msymbol env {pl_desc = m; pl_loc = me.pl_loc} in
    let extraparams = sig_.mis_params in
    let allparams = stparams @ extraparams in
    if allparams <> [] && not attop then
      tyerror me.pl_loc env (InvalidModAppl MAE_WrongArgCount);
    let me = EcEnv.Mod.by_mpath mp env in
    let arity = List.length stparams in
    { me with 
      me_name  = x; 
      me_body  = ME_Alias (arity,mp);
      me_sig   = { sig_ with mis_params = allparams }; 
    }

  | Pm_struct st -> transstruct ~attop env x (mk_loc me.pl_loc st)

(* -------------------------------------------------------------------- *)
and transmod_params env x params = 
    (* Check parameters types *) (* FIXME: dup names *)
  let stparams =
    List.map                          (* FIXME: exn *)
      (fun (a, aty) ->
         (EcIdent.create a.pl_desc, fst (transmodtype env aty)))
      params
  in

  (* Check structure items, extending environment initially with
   * structure arguments, and then with previously checked items. *)
  let env = EcEnv.Mod.enter x stparams env in
  stparams, env

and transstruct ~attop (env : EcEnv.env) (x : symbol) (st : pstructure located) =
  let { pl_loc = loc; pl_desc = st; } = st in

  if not attop && st.ps_params <> [] then
    tyerror loc env (InvalidModType MTE_InternalFunctor);

  let stparams, env0 = transmod_params env x st.ps_params in

  let (envi, items) =
    let tydecl1 (x, obj) =
      match obj with
      | MI_Module   m -> (x, `Module   m)
      | MI_Variable v -> (x, `Variable (EcTypes.PVglob, v.v_type))
      | MI_Function f -> (x, `Function f)
    in
    List.fold_left
      (fun (env, acc) item ->
        let newitems = transstruct1 env item in
        let env = EcEnv.bindall (List.map tydecl1 newitems) env in
        (env, List.rev_append acc newitems))
      (env0, []) st.ps_body
  in
  let items = List.map snd items in

  (* Generate structure signature *)
  let tymod =
    let mparams = 
      List.fold_left (fun mparams (id,_) ->
        Sm.add (EcPath.mident id) mparams) Sm.empty stparams in 
    let tymod1 = function
      | MI_Module   _ -> None
      | MI_Variable _ -> None
      | MI_Function f -> 
        let rec f_call c f =
          let f = EcEnv.NormMp.norm_xfun envi f in
          if EcPath.Sx.mem f c then c
          else 
            let c = EcPath.Sx.add f c in
            match (EcEnv.Fun.by_xpath f envi).f_def with
            | FBalias _ -> assert false
            | FBdef def -> List.fold_left f_call c def.f_uses.us_calls 
            | FBabs oi  -> List.fold_left f_call c oi.oi_calls in
        let all_calls = 
          match f.f_def with
          | FBalias f -> f_call EcPath.Sx.empty f 
          | FBdef def ->      
            List.fold_left f_call EcPath.Sx.empty def.f_uses.us_calls 
          | FBabs _ -> assert false in
        let filter f = 
          let ftop = EcPath.m_functor f.EcPath.x_top in
          Sm.mem ftop mparams in
        let calls = List.filter filter (EcPath.Sx.elements all_calls) in
        Some (Tys_function (f.f_sig, { oi_calls = calls; oi_in = true; }))
    in

    let sigitems = List.pmap tymod1 items in
      { mis_params = stparams;
        mis_body   = sigitems; };    
  in

  (* Check that generated signature is structurally included in
   * associated type mode. *)
  let check1 { pl_desc = (aty, oatyp); pl_loc = loc } =
    let (aty, _asig) = transmodtype env aty in
    if oatyp <> [] then
      begin 
        let cmp (x1, _) x2 = (EcIdent.name x1 = unloc x2) in
        if not (List.all2 cmp stparams oatyp) then
          tyerror loc env
            (InvalidModType MTE_FunSigDoesNotRepeatArgNames);
        (* Now we check the signature *)
        try  check_sig_mt_cnv env tymod aty
        with TymodCnvFailure err -> tyerror loc env (TypeModMismatch err)
      end
    else (* In that case we check the fully applied signature *)
      let sig_ = 
        { mis_params = [];
          mis_body = List.map 
            (fun (Tys_function (s, oi)) ->
              Tys_function (s, { oi_calls = []; oi_in = oi.oi_in }))
            tymod.mis_body } in
      try  check_sig_mt_cnv env0 sig_ aty
      with TymodCnvFailure err -> tyerror loc env0 (TypeModMismatch err)
  in
    List.iter check1 st.ps_signature;

  (* Construct structure representation *)
  let me =
    { me_name  = x;
      me_body  = ME_Structure { ms_body = items; };
      me_comps = items;
      me_sig   = tymod; }
  in
    me
  
(* -------------------------------------------------------------------- *)
and transstruct1 (env : EcEnv.env) (st : pstructure_item located) =
  match unloc st with
  | Pst_mod ({ pl_desc = m }, me) ->
      let me = transmod ~attop:false env m me in
        [(m, MI_Module me)]

  | Pst_var (xs, ty) ->
      let ty = transty_for_decl env ty in
        List.map
          (fun { pl_desc = x } ->
            (x, MI_Variable { v_name = x; v_type = ty; }))
          xs

  | Pst_fun (decl, body) -> begin
      let ue  = UE.create (Some []) in
      let env = EcEnv.Fun.enter decl.pfd_name.pl_desc env in

      let symbols = ref Sstr.empty
      and env     = ref env in

      (* Type-check function parameters / check for dups *)
      let dtyargs = 
        match decl.pfd_tyargs with
        | Fparams_imp _ -> assert false
        | Fparams_exp l -> l in
      let params =
        let params = ref [] in
        let add_param (x, pty) =
          let ty = transty tp_uni !env ue pty in
          let pr = (unloc x, `Variable (PVloc, ty)) in
            fundef_add_symbol !env symbols x;
            params  := ({ v_name = unloc x; v_type = ty }, pty.pl_loc) :: !params;
            env     := EcEnv.bindall [pr] !env
        in
          List.iter add_param dtyargs;
          List.rev !params
      in

      (* Type-check body *)
      let retty = transty tp_uni !env ue decl.pfd_tyresult in
      let (env, stmt, result, prelude, locals) =
        transbody ue symbols !env retty (mk_loc st.pl_loc body)
      in
      (* Close all types *)
      let su      = Tuni.offun (UE.close ue) in
      let retty   = fundef_check_type su env (retty, decl.pfd_tyresult.pl_loc) in
      let params  = List.map (fundef_check_decl  su env) params in
      let locals  = List.map (fundef_check_decl  su env) locals in
      let prelude = List.map (fundef_check_iasgn su env) prelude in

      let clsubst = { EcTypes.e_subst_id with es_ty = su } in
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
            fs_anames = Some params;
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
        [(decl.pfd_name.pl_desc, MI_Function fun_)]
  end

  | Pst_alias ({pl_desc = name},f) ->
    let f = trans_gamepath env f in
    let sig_ = (EcEnv.Fun.by_xpath f env).f_sig in
    let fun_ = { 
      f_name = name;
      f_sig = { sig_ with fs_name = name };
      f_def = FBalias f;
    } in
    [(name, MI_Function fun_)]

(* -------------------------------------------------------------------- *)
and transbody ue symbols (env : EcEnv.env) retty pbody =
  let { pl_loc = loc; pl_desc = pbody; } = pbody in

  let env     = ref env
  and prelude = ref []
  and locals  = ref [] in

  let mpath = oget (EcEnv.xroot !env) in

  (* Type-check local variables / check for dups *)
  let add_local local =
    List.iter (fundef_add_symbol !env symbols) (snd (unloc local.pfl_names));

    let xs     = snd (unloc local.pfl_names) in
    let mode   = fst (unloc local.pfl_names) in
    let init   = local.pfl_init |> omap (fst -| transexp !env `InProc ue) in
    let ty     = local.pfl_type |> omap (transty tp_uni !env ue) in

    let ty =
      match ty, init with
      | None   , None   -> None
      | Some ty, None   -> Some ty
      | None   , Some e -> Some e.e_ty
      | Some ty, Some e -> begin
          let loc =  (oget local.pfl_init).pl_loc in
            unify_or_fail !env ue loc ~expct:ty e.e_ty; Some ty
      end
    in

    let xsvars = List.map (fun _ -> UE.fresh ue) xs in

    begin
      ty |> oiter (fun ty ->
        match mode with
        | `Single -> List.iter (fun a -> EcUnify.unify !env ue a ty) xsvars
        | `Tuple  -> unify_or_fail !env ue local.pfl_names.pl_loc ~expct:ty (ttuple xsvars))
    end;

    env := begin
      let topr = fun x xty -> (unloc x, `Variable (PVloc, xty)) in
        EcEnv.bindall (List.map2 topr xs xsvars) !env
    end;

    let mylocals =
      List.map2
        (fun { pl_desc = x; pl_loc = loc; } xty ->
          ({ v_name = x; v_type = xty }, pv_loc mpath x, xty, loc))
        xs xsvars
    in

    locals :=
       List.rev_append
        (List.map (fun (v, _, _, pl) -> (v, pl)) mylocals)
        !locals;

    init |> oiter
      (fun init ->
        let iasgn = List.map (fun (_, v, xty, _) -> (v, xty)) mylocals in
          prelude := ((mode, iasgn), init, _dummy) :: !prelude)
  in

  List.iter add_local pbody.pfb_locals;

  let body   = transstmt !env ue pbody.pfb_body in
  let result =
    match pbody.pfb_return with
    | None ->
        begin
          try  EcUnify.unify !env ue tunit retty
          with EcUnify.UnificationFailure _ ->
            tyerror loc !env NonUnitFunWithoutReturn
        end;
        None

    | Some pe ->
        let (e, ety) = transexp !env `InProc ue pe in
          try
            EcUnify.unify !env ue tunit retty;
            tyerror loc !env UnitFunWithReturn
          with EcUnify.UnificationFailure _ ->
            unify_or_fail !env ue pe.pl_loc ~expct:retty ety;
            Some e
  in
    if not (UE.closed ue) then
      tyerror loc !env OnlyMonoTypeAllowed;
    (!env, body, result, List.rev !prelude, List.rev !locals)

(* -------------------------------------------------------------------- *)
and fundef_add_symbol env symbols x =  (* for locals dup check *)
  if Sstr.mem x.pl_desc !symbols then
    tyerror x.pl_loc env (DuplicatedLocal x.pl_desc);
  symbols := Sstr.add x.pl_desc !symbols

and fundef_check_type subst_uni env (ty, loc) = 
  let ty = subst_uni ty in
    if not (EcUid.Suid.is_empty (Tuni.fv ty)) then
      tyerror loc env OnlyMonoTypeAllowed;
    ty

and fundef_check_decl subst_uni env (decl, loc) =
  { decl with
      v_type = fundef_check_type subst_uni env (decl.v_type, loc) }

and fundef_check_iasgn subst_uni env ((mode, pl), init, loc) =
  let pl =
    List.map
      (fun (p, ty) ->
        (p, fundef_check_type subst_uni env (ty, loc)))
      pl
  in
  let pl =
    match mode with
    | `Single -> List.map (fun xty -> LvVar xty) pl
    | `Tuple  -> [LvTuple pl]
  in

  let clsubst = { EcTypes.e_subst_id with es_ty = subst_uni } in
  let init    = e_subst clsubst init in

    List.map (fun lv -> i_asgn (lv, init)) pl

(* -------------------------------------------------------------------- *)
and transstmt (env : EcEnv.env) ue (stmt : pstmt) : stmt =
  EcModules.stmt (List.map (transinstr env ue) stmt)

(* -------------------------------------------------------------------- *)
and transinstr (env : EcEnv.env) ue (i : pinstr) =
  let transcall name args = 
    let fpath = trans_gamepath env name in
    let fsig  = (EcEnv.Fun.by_xpath fpath env).f_sig in
    let (args, ty) =
      transcall (transexp env `InProc ue) env ue name.pl_loc fsig args
    in
      (fpath, args, ty)
  in

  match i.pl_desc with
  | PSasgn (plvalue, prvalue) -> begin
      match unloc prvalue with
      | PEapp ( { pl_desc = PEident (f, None) },
                [{ pl_desc = PEtuple es; pl_loc = les; }])
          when EcEnv.Fun.lookup_opt (unloc f) env <> None
          ->
        let fident { pl_loc = loc; pl_desc = (nm, x); } =
          let nm = List.map (fun x -> (mk_loc loc x, None)) nm in
            mk_loc loc (nm, mk_loc loc x)
        in
        let call = PScall (Some plvalue, fident f, mk_loc les es) in
          transinstr env ue (mk_loc i.pl_loc call)

      | _ ->
        let lvalue, lty = translvalue ue env plvalue in
        let rvalue, rty = transexp env `InProc ue prvalue in
          unify_or_fail env ue prvalue.pl_loc ~expct:lty rty;
          i_asgn (lvalue, rvalue)
    end

  | PSrnd (plvalue, prvalue) -> 
      let lvalue, lty = translvalue ue env plvalue in
      let rvalue, rty = transexp env `InProc ue prvalue in
      unify_or_fail env ue prvalue.pl_loc ~expct:(tdistr lty) rty;
      i_rnd (lvalue, rvalue)

  | PScall (None, name, args) ->
      let (fpath, args, rty) = transcall name (unloc args) in
      unify_or_fail env ue i.pl_loc ~expct:tunit rty;
      i_call (None, fpath, args)

  | PScall (Some lvalue, name, args) ->
      let lvalue, lty = translvalue ue env lvalue in
      let (fpath, args, rty) = transcall name (unloc args) in
      unify_or_fail env ue name.pl_loc ~expct:lty rty;
      i_call (Some lvalue, fpath, args)

  | PSif ((pe, s), cs, sel) -> begin
      let rec for1_i (pe, s) sel =
        let e, ety = transexp env `InProc ue pe in
        let s = transstmt env ue s in
        unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
        i_if (e, s, sel)
      
      and for1_s (pe, s) sel = stmt [for1_i (pe, s) sel] in

      for1_i (pe, s)
        (List.fold_right for1_s cs (transstmt env ue sel))
  end

  | PSwhile (pe, pbody) ->
      let e, ety = transexp env `InProc ue pe in
      let body = transstmt env ue pbody in
      unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
      i_while (e, body)

  | PSassert pe ->
      let e, ety = transexp env `InProc ue pe in 
      unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
      i_assert e

(* -------------------------------------------------------------------- *)
and trans_pv env { pl_desc = x; pl_loc = loc } = 
  let side = EcEnv.Memory.get_active env in
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
      LvVar pty, snd pty

  | PLvTuple xs -> 
      let xs = List.map (trans_pv env) xs in
      if not (List.uniqf (EqTest.for_pv_norm env) (List.map fst xs)) then
        tyerror lvalue.pl_loc env LvNonLinear;
      let ty = ttuple (List.map snd xs) in
      (LvTuple xs, ty)

  | PLvMap (x, tvi, e) ->
      let tvi = tvi |> omap (transtvi env ue) in
      let codomty = UE.fresh ue in
      let pv, xty = trans_pv env x in
      let e, ety = transexp env `InProc ue e in
      let name = ([], EcCoreLib.s_set) in
      let esig = [xty; ety; codomty] in
      let ops = select_exp_op env `InProc None name ue tvi esig in

      match ops with
      | [] ->
          let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
          tyerror x.pl_loc env (UnknownVarOrOp (name, esig))

      | [{ e_node = Eop (p, tys) }, opty, subue, _] ->
          EcUnify.UniEnv.restore ~src:subue ~dst:ue;
          let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
          let esig = toarrow esig xty in
          unify_or_fail env ue lvalue.pl_loc ~expct:esig opty;
          (LvMap ((p, tys), pv, e, xty), codomty)

      | [_] ->
          let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
          tyerror x.pl_loc env (UnknownVarOrOp (name, esig))

      | _ ->
          let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
          let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
          tyerror x.pl_loc env (MultipleOpMatch (name, esig, matches))

(* -------------------------------------------------------------------- *)
let transmem env m =
  match EcEnv.Memory.lookup 0 (unloc m) env with
  | None ->
      tyerror m.pl_loc env (UnknownMemName (0, unloc m))
      
  | Some me ->
(*      if (EcMemory.memtype me) <> None then
        tyerror m.pl_loc env (InvalidMem (unloc m, MAE_IsConcrete)); *)
      (fst me)

(* -------------------------------------------------------------------- *)
let trans_topmsymbol env gp = 
  (* FIXME *)
  let (mp,_) = trans_msymbol env gp in
  let top = EcPath.m_functor mp in
  let mp = EcPath.m_apply top mp.EcPath.m_args in
  mp

(* -------------------------------------------------------------------- *)
let trans_form_or_pattern env (ps, ue) pf tt =
  let rec transf_r opsc env f =
    let transf = transf_r opsc in

    match f.pl_desc with
    | PFhole -> begin
      match ps with
      | None    -> tyerror f.pl_loc env PatternNotAllowed
      | Some ps ->
        let x  = EcIdent.create "_p" in
        let ty = UE.fresh ue in
          ps := Mid.add x ty !ps; f_local x ty
    end

    | PFmem _ -> tyerror f.pl_loc env MemNotAllowed

    | PFscope (popsc, f) ->
        let opsc = lookup_scope env popsc in
          transf_r (Some opsc) env f

    | PFglob gp ->
        let (mp,_) = trans_msymbol env gp in
        let me =  
          match EcEnv.Memory.current env with
          | None -> tyerror f.pl_loc env NoActiveMemory
          | Some me -> EcMemory.memory me
        in
          f_glob mp me
      
    | PFint n ->
        f_int n

    | PFtuple args -> begin
        let args = List.map (transf env) args in
          match args with
          | []  -> f_tt
          | [f] -> f
          | fs  -> f_tuple fs
    end

    | PFident ({ pl_desc = name;pl_loc = loc }, tvi) -> 
        let tvi = tvi |> omap (transtvi env ue) in
        let ops = select_form_op env opsc name ue tvi [] in
        begin match ops with
        | [] ->
            tyerror loc env (UnknownVarOrOp (name, []))

        | [op, _, subue, _] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue; op

        | _ ->
            let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
            tyerror loc env (MultipleOpMatch (name, [], matches))
        end

    | PFside (f, side) -> begin
        let (sloc, (gen, side)) = (side.pl_loc, unloc side) in
        let me =
          match EcEnv.Memory.lookup gen side env with
          | None -> tyerror sloc env (UnknownMemName (gen, side))
          | Some me -> EcMemory.memory me
        in
          transf (EcEnv.Memory.set_active me env) f
      end

    | PFeqveq (xs, om) ->
        let lookup me x =
          match EcEnv.Var.lookup_progvar_opt ~side:me (unloc x) env with
          | None -> tyerror x.pl_loc env (UnknownVarOrOp (unloc x, []))
          | Some (x, ty) -> 
              match x with
              | `Var x -> f_pvar x ty me
              | `Proj (x, ty', (i, n)) -> 
                  if   i = 0 && n = 1
                  then f_pvar x ty me 
                  else f_proj (f_pvar x ty' me) i ty
        in

        let check_mem loc me = 
          match EcEnv.Memory.byid me env with
          | None -> tyerror loc env (UnknownMemName (0, EcIdent.name me))
          | Some _ -> ()
        in

        let qual (mq : pmsymbol option) (x : pqsymbol) =
          match mq with
          | None    -> x
          | Some qs ->
              let (nm, name) = x.pl_desc in
              { x with pl_desc = ((List.map (unloc |- fst) qs)@nm, name) }
        in

         let do1 = function
          | GVvar x ->
              let x1 = lookup EcFol.mleft  (qual (om |> omap fst) x) in
              let x2 = lookup EcFol.mright (qual (om |> omap snd) x) in
                unify_or_fail env ue x.pl_loc ~expct:x1.f_ty x2.f_ty;
                f_eq x1 x2

          | GVglob gp ->
              let (mp, _) = trans_msymbol env gp in
                let x1 = f_glob mp EcFol.mleft in
                let x2 = f_glob mp EcFol.mright in
                  unify_or_fail env ue gp.pl_loc ~expct:x1.f_ty x2.f_ty;
                  f_eq x1 x2
        in
          check_mem f.pl_loc EcFol.mleft;
          check_mem f.pl_loc EcFol.mright;
          EcFol.f_ands (List.map do1 xs)

    | PFapp ({pl_desc = PFident ({ pl_desc = name; pl_loc = loc }, tvi)}, pes) ->
        let tvi  = tvi |> omap (transtvi env ue) in  
        let es   = List.map (transf env) pes in
        let esig = List.map EcFol.f_ty es in 
        let ops  = select_form_op env opsc name ue tvi esig in
          begin match ops with
          | [] ->
              let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
                tyerror loc env (UnknownVarOrOp (name, esig))

          | [op, _, subue, _] ->
              EcUnify.UniEnv.restore ~src:subue ~dst:ue;
              let esig = List.map2 (fun e l -> mk_loc l.pl_loc e) esig pes in
              let codom = ty_fun_app _dummy env ue op.f_ty esig in
                f_app op es codom

          | _ ->
              let esig = Tuni.offun_dom (EcUnify.UniEnv.assubst ue) esig in
              let matches = List.map (fun (_, _, subue, m) -> (m, subue)) ops in
              tyerror loc env (MultipleOpMatch (name, esig, matches))
          end

    | PFapp (e, pes) ->
        let es    = List.map (transf env) pes in
        let esig  = List.map2 (fun f l -> mk_loc l.pl_loc f.f_ty) es pes in
        let op    = transf env e in
        let codom = ty_fun_app f.pl_loc env ue op.f_ty esig in
        f_app op es codom

    | PFif (pf1, pf2, pf3) ->
        let f1 = transf env pf1 in
        let f2 = transf env pf2 in
        let f3 = transf env pf3 in
          unify_or_fail env ue pf1.pl_loc ~expct:tbool   f1.f_ty;
          unify_or_fail env ue pf3.pl_loc ~expct:f2.f_ty f3.f_ty;
          f_if f1 f2 f3

    | PFlet (lp, (pf1, paty), f2) ->
        let (penv, p, pty) = transpattern env ue lp in
        let aty = paty |> omap (transty tp_uni env ue) in
        let f1 = transf env pf1 in
        unify_or_fail env ue pf1.pl_loc ~expct:pty f1.f_ty;
        aty |> oiter (fun aty-> unify_or_fail env ue pf1.pl_loc ~expct:pty aty);
        let f2 = transf penv f2 in
        f_let p f1 f2 

    | PFforall (xs, pf) ->
        let env, xs = trans_fbind env ue xs in
        let f = transf env pf in
          unify_or_fail env ue pf.pl_loc ~expct:tbool f.f_ty;
          f_forall xs f

    | PFexists (xs, f1) ->
        let env, xs = trans_fbind env ue xs in
        let f = transf env f1 in
          unify_or_fail env ue f1.pl_loc ~expct:tbool f.f_ty;
          f_exists xs f

    | PFlambda (xs, f1) ->
        let env, xs = transbinding env ue xs in
        let f = transf env f1 in
          f_lambda (List.map (fun (x,ty) -> (x,GTty ty)) xs) f

    | PFrecord fields ->
        let (ctor, fields, (rtvi, reccty)) =
          trans_record env ue
            (fun f -> let f = transf env f in (f, f.f_ty))
            (f.pl_loc, fields) in
        let ctor = f_op ctor rtvi (toarrow (List.map snd fields) reccty) in
        let ctor = f_app ctor (List.map fst fields) reccty in
          ctor

    | PFproj (subf, x) -> begin
      let subf = transf env subf in
      match select_proj env opsc (unloc x) ue None subf.f_ty with
      | [] -> 
        let ty = Tuni.offun (EcUnify.UniEnv.assubst ue) subf.f_ty in
        let me = EcFol.mhr in
        let mp = 
          match ty.ty_node with
          | Tglob mp -> mp 
          | _ -> tyerror x.pl_loc env (UnknownProj (unloc x)) in
        let f = NormMp.norm_glob env me mp in
        let lf = 
          match f.f_node with
          | Ftuple l -> l 
          | _ -> tyerror x.pl_loc env (UnknownProj (unloc x)) in
        let vx,ty =
          match EcEnv.Var.lookup_progvar_opt ~side:me (unloc x) env with
          | None -> tyerror x.pl_loc env (UnknownVarOrOp (unloc x, []))
          | Some (x1, ty) -> 
              match x1 with
              | `Var x -> NormMp.norm_pvar env x, ty 
              | _ -> tyerror x.pl_loc env (UnknownVarOrOp (unloc x, [])) in 
        let find f1 =
           match f1.f_node with
            | Fpvar (x1, _) -> EcTypes.pv_equal vx (NormMp.norm_pvar env x1)
            | _ -> false in 
        let i = 
          match List.findex find lf with
          | None -> tyerror x.pl_loc env (UnknownProj (unloc x))
          | Some i -> i in
        f_proj subf i ty

      | _::_::_ -> tyerror x.pl_loc env (AmbiguousProj (unloc x))
      | [(op, tvi), pty, subue] ->
        EcUnify.UniEnv.restore ~src:subue ~dst:ue;
        let rty = EcUnify.UniEnv.fresh ue in
        (try  EcUnify.unify env ue (tfun subf.f_ty rty) pty
         with EcUnify.UnificationFailure _ -> assert false);
        f_app (f_op op tvi pty) [subf] rty
    end

    | PFproji (subf, i) -> begin
      let subf' = transf env subf in
      let ty = Tuni.offun (EcUnify.UniEnv.assubst ue) subf'.f_ty in
      match (EcEnv.Ty.hnorm ty env).ty_node with
      | Ttuple l when i < List.length l ->
        let ty = List.nth l i in
        f_proj subf' i ty
      | _ -> tyerror subf.pl_loc env (AmbiguousProji(i,ty))
    end

    | PFprob (gp, args, m, event) ->
        let fpath = trans_gamepath env gp in
        let fun_  = EcEnv.Fun.by_xpath fpath env in
        let args,_ = 
          transcall (fun f -> let f = transf env f in f, f.f_ty)
            env ue f.pl_loc fun_.f_sig args in
        let memid = transmem env m in
        let env = EcEnv.Fun.prF fpath env in
        let event' = transf env event in
        unify_or_fail env ue event.pl_loc ~expct:tbool event'.f_ty;
        f_pr memid fpath (f_tuple args) event'

    | PFhoareF (pre, gp, post) ->
        let fpath = trans_gamepath env gp in
        let penv, qenv = EcEnv.Fun.hoareF fpath env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
          unify_or_fail penv ue pre.pl_loc  ~expct:tbool pre' .f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
          f_hoareF pre' fpath post'

    | PFBDhoareF (pre, gp, post, hcmp, bd) ->
        let fpath = trans_gamepath env gp in
        let penv, qenv = EcEnv.Fun.hoareF fpath env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
        let bd'   = transf penv bd in
          (* FIXME: check that there are not pvars in bd *)
          unify_or_fail penv ue pre .pl_loc ~expct:tbool pre' .f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
          unify_or_fail env  ue bd  .pl_loc ~expct:treal bd'  .f_ty;
          f_bdHoareF pre' fpath post' hcmp bd'

    | PFlsless gp ->
        let fpath = trans_gamepath env gp in
          f_losslessF fpath

    | PFequivF (pre, (gp1, gp2), post) ->
        let fpath1 = trans_gamepath env gp1 in
        let fpath2 = trans_gamepath env gp2 in
        let penv, qenv = EcEnv.Fun.equivF fpath1 fpath2 env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
          unify_or_fail penv ue pre .pl_loc ~expct:tbool pre' .f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
          f_equivF pre' fpath1 fpath2 post'

    | PFeagerF (pre, (s1,gp1,gp2,s2), post) ->
        let fpath1 = trans_gamepath env gp1 in
        let fpath2 = trans_gamepath env gp2 in
        let penv, qenv = EcEnv.Fun.equivF fpath1 fpath2 env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
        let s1    = transstmt env ue s1 in
        let s2    = transstmt env ue s2 in
        unify_or_fail penv ue pre .pl_loc ~expct:tbool pre' .f_ty;
        unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
        f_eagerF pre' s1 fpath1 fpath2 s2 post'

  and trans_fbind env ue decl = 
    let trans1 env (xs, pgty) =
        match pgty with
        | PGTY_Type ty -> 
          let ty = transty tp_relax env ue ty in
          let xs = List.map (fun x -> EcIdent.create x.pl_desc, ty) xs in
          let env = EcEnv.Var.bind_locals xs env in
          let xs = List.map (fun (x,ty) -> x,GTty ty) xs in
          env, xs
  
        | PGTY_ModTy(mi,restr) ->
          let (mi, _) = transmodtype env mi in
          (* FIXME ? why do we use trans_topmsymbol 
             and not trans_msymbol here *)
          let restr = Sx.empty, Sm.of_list (List.map (trans_topmsymbol env) restr) in
          let ty = GTmodty (mi, restr) in
          let add1 env x = 
            let x = EcIdent.create x.pl_desc in
            let env = EcEnv.Mod.bind_local x mi restr env in
            env, (x, ty) in
          List.map_fold add1 env xs 

        | PGTY_Mem ->
          let ty = GTmem None in
          let add1 env x = 
            let x = EcIdent.create x.pl_desc in
            let env = EcEnv.Memory.push (EcMemory.abstract x) env in
            env, (x, ty) in
          List.map_fold add1 env xs in
    let env, bd = List.map_fold trans1 env decl in
    env, List.flatten bd
  in

  let f = transf_r None env pf in
  tt |> oiter (fun tt -> unify_or_fail env ue pf.pl_loc ~expct:tt f.f_ty);
  f

(* -------------------------------------------------------------------- *)
let trans_form_opt env ue pf oty =
  trans_form_or_pattern env (None, ue) pf oty

(* -------------------------------------------------------------------- *)
let trans_form env ue pf ty =
  trans_form_opt env ue pf (Some ty)

(* -------------------------------------------------------------------- *)
let trans_prop env ue pf = 
  trans_form env ue pf tbool

(* -------------------------------------------------------------------- *)
let trans_pattern env (ps, ue) pf =
  trans_form_or_pattern env (Some ps, ue) pf None

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
        Some (inst, Tuni.offun (EcUnify.UniEnv.close ue) gty, cr)
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
