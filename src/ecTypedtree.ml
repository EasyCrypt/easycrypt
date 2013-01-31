

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcParsetree
open EcTypes
open EcDecl
open EcTypesmod
open EcFol

module Sp = EcPath.Sp
module Mp = EcPath.Mp

(* -------------------------------------------------------------------- *)
let dloc = Location.dummy               (* FIXME: TO BE REMOVED *)

(* -------------------------------------------------------------------- *)
type tyerror =
  | UnknownVariable          of qsymbol
  | UnknownFunction          of qsymbol
  | UnknownTypeName          of qsymbol
  | UnknownTyModName         of qsymbol
  | UnknownModName           of qsymbol
  | UnknownOperatorForSig    of qsymbol * ty list
  | InvalidNumberOfTypeArgs  of qsymbol * int * int
  | ApplInvalidArity
  | UnboundTypeParameter     of symbol
  | OpNotOverloadedForSig    of qsymbol * ty list
  | UnexpectedType           of ty * ty * ty * ty
  | NonLinearPattern         of lpattern
  | DuplicatedLocals         of psymbol option
  | ProbaExpressionForbidden
  | PatternForbiden
  | ModApplToNonFunctor
  | ModApplInvalidArity
  | ModApplInvalidArgInterface
  | UnificationVariableNotAllowed
  | TypeVariableNotAllowed
  | RandomExprNotAllowed
  | UnNamedTypeVariable
  | UnusedTypeVariable

exception TyError of Location.t * tyerror

let tyerror loc x = raise (TyError (loc, x))

(* -------------------------------------------------------------------- *)
let e_inuse =
  let rec inuse (map : Sp.t) (e : tyexpr) =
    match e.tye_desc with
    | Evar p -> begin
        match p.pv_kind with
        | PVglob -> Sp.add p.pv_name map
        | _      -> map
      end
    | _ -> e_fold inuse map e
  in
    fun e -> inuse Sp.empty e
  
(* -------------------------------------------------------------------- *)
let (i_inuse, s_inuse) =
  let addflag p e map =
     Mp.change
       (fun flags -> Some (UM.add (odfl UM.empty flags) e))
       p map
  in

  let rec lv_inuse (map : use_flags Mp.t) (lv : lvalue) =
    match lv with
    | LvVar (p,_) ->
        addflag p.pv_name `Write map

    | LvTuple ps ->
        List.fold_left
          (fun map (p, _) -> addflag p.pv_name `Write map)
          map ps

    | LvMap (_, p, e, _) ->
        (* Maps are not modified in place but feed to a mutator
           operator that returns the augmented map, keeping the previous
           one untouched. Hence the [`Read] flag. *)
      let map = addflag p.pv_name `Read map in
      let map = se_inuse map e in
        map

  and i_inuse (map : use_flags Mp.t) (i : instr) =
    match i with
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
      let map = addflag p `Call map in
      let map = ofold lv ((^~) lv_inuse) map in
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

  and s_inuse (map : use_flags Mp.t) (s : stmt) =
    List.fold_left i_inuse map s

  and se_inuse (map : use_flags Mp.t) (e : tyexpr) =
    Sp.fold (fun p map -> addflag p `Read map) (e_inuse e) map

  in
    (i_inuse Mp.empty, s_inuse Mp.empty)

(* -------------------------------------------------------------------- *)
module UE = EcUnify.UniEnv

let filter_tvi = function 
  | None -> fun _ -> true
  | Some (UE.TVIunamed l) -> 
      let len = List.length l in
      fun op -> List.length op.op_params = len
  | Some (UE.TVInamed ls) -> fun op ->
      List.for_all 
        (fun (s,_) -> 
          List.exists (fun id -> EcIdent.name id = s) op.op_params) ls

(* Politique de nomage :
   les variables locales masquent les autres noms cours.
*)
  
let select_local env (qs,s) = 
  if qs = [] then EcEnv.Var.trylookup_local s env 
  else None 

let tfun_expected ue psig = 
  let tres = UE.fresh_uid ue in
  EcTypes.toarrow psig tres

let select_pv env name ue tvi psig = 
  if tvi <> None then [] 
  else
    let pvs = EcEnv.Var.all_pv name env in 
    let select (pv,ty) = 
      try 
        let subue = UE.copy ue in
        let texpected = tfun_expected subue psig in
        EcUnify.unify env subue ty texpected;
        Some (pv, ty, subue)
      with _ -> None in
    List.pmap select pvs

let select_op1 pred tvi env name ue psig = 
  let fti = filter_tvi tvi in 
  let fop op =
    (pred || not (is_pred op)) && 
    fti op in
  let ops = EcEnv.Op.all fop name env in
  let select (path, op) = 
    let subue,(dom,codom),tys = UE.freshensig ue op.op_params tvi (op_sig op) in
    try 
      let top = EcTypes.toarrow dom codom in
      let texpected = tfun_expected subue psig in
      EcUnify.unify env subue top texpected; 
      Some ((path,tys), top, subue) 
    with _ -> None in
  List.pmap select ops

let gen_select_op pred tvi env name ue psig =
  match select_local env name with
  | Some(id,ty) -> 
      if tvi <> None then assert false; (* FIXME error message *)
      [ (e_local id, ty, ue) ]
  | None ->
      let pvs = select_pv env name ue tvi psig in
      let ops = select_op1 pred tvi env name ue psig in
      List.map (fun (pv,ty,ue) -> e_var pv, ty, ue) pvs @ 
      List.map (fun ((op,tys), ty,ue) -> e_op op tys, ty, ue) ops

let select_op env name ue tvi psig =
  gen_select_op false tvi env name ue psig 

type typolicy = {
    tp_uni         : bool;   (* "_" allowed                         *)
    tp_tvar        : bool;   (* type variable allowed               *)
  }

(* for type declaration *)
let tp_tydecl = {
  tp_uni         = false;
  tp_tvar        = true;
}

(* used for operators, formulas and predicate *)
let tp_relax = {
  tp_uni         = true;
  tp_tvar        = true;
}

(* used for global variables, signature of function in module type *)
let tp_nothing = {
  tp_uni         = false;
  tp_tvar        = false;
}

(* used for declaration of parameters and local variables in function *)
let tp_uni = {
  tp_uni         = true;
  tp_tvar        = false;
}

(* -------------------------------------------------------------------- *)
let rec transty tp (env : EcEnv.env) ue ty =
  match ty.pl_desc with
   | PTunivar ->
       if tp.tp_uni then UE.fresh_uid ue
       else tyerror ty.pl_loc UnificationVariableNotAllowed;

   | PTvar s ->
       if tp.tp_tvar then 
         try Tvar (UE.get_var ue s.pl_desc)
         with _ -> tyerror s.pl_loc (UnboundTypeParameter s.pl_desc)
       else tyerror s.pl_loc TypeVariableNotAllowed;

  | PTtuple tys   -> 
      Ttuple (transtys tp env ue tys)

  | PTnamed { pl_desc = name } -> 
      begin match EcEnv.Ty.trylookup name env with
      | None -> tyerror ty.pl_loc (UnknownTypeName name)
      | Some (p, tydecl) ->
          if tydecl.tyd_params <> [] then
            tyerror ty.pl_loc
              (InvalidNumberOfTypeArgs(name,List.length tydecl.tyd_params, 0));
          Tconstr (p, [])
      end
  | PTfun(ty1,ty2) ->
      Tfun(transty tp env ue ty1, transty tp env ue ty2) 
        
  | PTapp ({ pl_desc = name }, tyargs) -> 
      begin match EcEnv.Ty.trylookup name env with
      | None -> tyerror ty.pl_loc (UnknownTypeName name)
      | Some (p, tydecl) ->
          let nargs = List.length tyargs in
          let expected = List.length tydecl.tyd_params in
          if nargs <> expected then
            tyerror ty.pl_loc (InvalidNumberOfTypeArgs (name, expected, nargs));
          let tyargs = transtys tp env ue tyargs in 
          Tconstr (p, tyargs)
      end

and transtys tp (env : EcEnv.env) ue tys = 
  List.map (transty tp env ue) tys

let transty_nothing = 
  let ue = UE.create (Some []) in
  fun env ty -> transty tp_nothing env ue ty

(* -------------------------------------------------------------------- *)
exception NonLinearPattern of EcParsetree.lpattern

let transpattern1 _env ue (p : EcParsetree.lpattern) = 
  match p with
  | LPSymbol { pl_desc = x } ->
      let ty = UE.fresh_uid ue in
      let x  = EcIdent.create x in
      (LSymbol x, ty)

  | LPTuple xs ->
      let xs = unlocs xs in
      if not (List.uniq xs) then raise (NonLinearPattern p)
      else
        let xs     = List.map EcIdent.create xs in
        let subtys = List.map (fun _ -> UE.fresh_uid ue) xs in
        (LTuple xs, Ttuple subtys)

let transpattern env ue (p : EcParsetree.lpattern) =
  match transpattern1 env ue p with
  | LSymbol x as p, ty ->
      EcEnv.Var.bind x ty None env, p, ty
  | LTuple xs as p, (Ttuple lty as ty) ->
      EcEnv.Var.bindall (List.combine xs lty) None env, p, ty
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let unify_error env ue loc ty1 ty2 = 
  try  EcUnify.unify env ue ty1 ty2 
  with EcUnify.UnificationFailure(t1,t2) ->
    let inst_uni = Tuni.subst (UE.asmap ue) in
    tyerror loc (UnexpectedType (inst_uni ty1, inst_uni ty2, 
                                 inst_uni t1 , inst_uni t2 ))

let transtvi env ue tvi = 
  match tvi with
  | None -> None
  | Some (TVIunamed lt) ->
      Some (UE.TVIunamed (List.map (transty tp_relax env ue) lt))
  | Some (TVInamed lst) ->
      let add l (s,t) = 
        try
          let s' = fst (List.find (fun (s',_) -> unloc s = unloc s') l) in
          tyerror s.pl_loc (DuplicatedLocals (Some s'))
        with Not_found ->
          (s, transty tp_relax env ue t) :: l in
      let lst = List.fold_left add [] lst in
      Some (UE.TVInamed (List.rev_map (fun (s,t) -> unloc s, t) lst))
  
let rec destr_tfun env ue tf = 
  match tf with
  | Tunivar _ ->
      let tf' = UE.repr ue tf in
      assert (not (tf == tf'));
      destr_tfun env ue tf'
  | Tfun(ty1,ty2) -> ty1, ty2
  | Tconstr(p,tys) when EcEnv.Ty.defined p env ->
      destr_tfun env ue (EcEnv.Ty.unfold p tys env) 
  | _ -> assert false (* FIXME error message *)

let rec ty_fun_app env ue tf targs = 
  match targs with
  | [] -> tf
  | t1 :: targs ->
      let dom,codom = destr_tfun env ue tf in
      (try EcUnify.unify env ue t1 dom with _ -> assert false);
      ty_fun_app env ue codom targs

  
  
let transexp (env : EcEnv.env) (ue : EcUnify.unienv) e =

  let rec transexp (env : EcEnv.env) (e : pexpr) =
    let loc = e.pl_loc in

    match e.pl_desc with
    | PEint i -> (e_int i, tint)

    | PEident ({ pl_desc = name }, tvi) -> 
        let tvi = transtvi env ue tvi in
        let ops = select_op env name ue tvi [] in
        begin match ops with
        | [] | _ :: _ :: _ -> (* FIXME: better error message *)
            tyerror loc (UnknownOperatorForSig (name, []))
        | [op, ty, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            op, ty
        end

    | PEapp ({ pl_desc = name }, tvi, es) -> begin
      let tvi = transtvi env ue tvi in  
      let es   = List.map (transexp env) es in
      let esig = snd (List.split es) in
      let ops  = select_op env name ue tvi esig in
        match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror loc (UnknownOperatorForSig (name, esig))

        | [op, ty, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            let codom = ty_fun_app env ue ty esig in
            (e_app op (List.map fst es), codom)
    end

    | PElet (p, pe1, pe2) ->
      let (penv, p, pty) = transpattern env ue p in
      let e1, ty1 = transexp  env pe1 in
      let e2, ty2 = transexp penv pe2 in
      (* FIXME loc should be p *)
      unify_error env ue loc pty ty1;
      (e_let p e1 e2, ty2)

    | PEtuple es ->
        let tes = List.map (transexp env) es in
        let es, tys = List.split tes in
          (e_tuple es, Ttuple tys)

    | PEif (pc, pe1, pe2) ->
      let c, tyc = transexp env pc in
      let e1, ty1 = transexp env pe1 in
      let e2, ty2 = transexp env pe2 in
        unify_error env ue pc.pl_loc tyc tbool;
        unify_error env ue pe2.pl_loc ty2 ty1;
        (e_if c e1 e2, ty1)

  in
    transexp env e

let transexpcast (env : EcEnv.env) (ue : EcUnify.unienv) t e =
  let e',t' = transexp env ue e in
  try EcUnify.unify env ue t' t; e'
  with EcUnify.UnificationFailure(t1,t2) ->
    tyerror e.pl_loc (UnexpectedType (t',t, t1, t2))

(* -------------------------------------------------------------------- *)
(* FIXME move this *)
let lvalue_mapty onty = function 
  | LvVar(id,ty) -> LvVar(id,onty ty)
  | LvTuple l -> LvTuple (List.map (fun (id,ty) -> id, onty ty) l)
  | LvMap(set,m,e,ty) -> 
      LvMap(set,m,Esubst.mapty onty e, onty ty)

let rec stmt_mapty onty s = List.map (instr_mapty onty) s 

and instr_mapty onty = function
  | Sasgn(x,e) -> Sasgn(lvalue_mapty onty x, Esubst.mapty onty e)
  | Srnd(x,e) -> Sasgn(lvalue_mapty onty x, Esubst.mapty onty e)
  | Scall(x,f,args) -> Scall(omap x (lvalue_mapty onty), f, 
                             List.map (Esubst.mapty onty) args)
  | Sif(e,s1,s2) -> 
      Sif(Esubst.mapty onty e, stmt_mapty onty s1, stmt_mapty onty s2)
  | Swhile(e,s) ->
      Swhile(Esubst.mapty onty e, stmt_mapty onty s)
  | Sassert e -> Sassert (Esubst.mapty onty e)

(* -------------------------------------------------------------------- *)
exception DuplicatedSigItemName   of psignature
exception DuplicatedArgumentsName of pfunction_decl

let name_of_sigitem = function
  | `VariableDecl v -> v.pvd_name
  | `FunctionDecl f -> f.pfd_name

let rec transsig (env : EcEnv.env) (is : psignature) =
  let transsig1 = function
    | `VariableDecl x ->
        let name  = x.pvd_name.pl_desc in
        let type_ = transty_nothing env x.pvd_type in
          Tys_variable (name, type_)

    | `FunctionDecl f ->
        let name   = f.pfd_name in
        let tyargs =
          List.map                      (* FIXME: continuation *)
            (fun (x, ty) -> (EcIdent.create x.pl_desc, transty_nothing env ty))
            f.pfd_tyargs
        in
        let resty  = transty_nothing env f.pfd_tyresult in
          if not (List.uniq (List.map fst f.pfd_tyargs)) then
            raise (DuplicatedArgumentsName f);
          Tys_function
            { fs_name = name.pl_desc;
              fs_sig  = (tyargs, resty);
              fs_uses = Mp.empty; }

  in

  let items = List.map transsig1 is in
  let names = List.map name_of_sigitem is in

    if not (List.uniq names) then
      raise (DuplicatedSigItemName is)
    else
      items

and transtymod (env : EcEnv.env) (tymod : pmodule_type) =
  match tymod with
  | Pty_app _ -> assert false

  | Pty_func (args, i) ->
      if not (List.uniq (List.map fst args)) then
        tyerror dloc (DuplicatedLocals None); (* FIXME as fun decl *)

      let args =
        List.map
          (fun (x, iname) ->
              (EcIdent.create x.pl_desc,
               snd (EcEnv.ModTy.lookup (unloc iname) env)))
          args
      in
        { tym_params = args;
          tym_sig    = transsig (EcEnv.ModTy.bindall args env) i;
          tym_mforb  = Sp.empty; }

  | Pty_sig i ->
      { tym_params = [];
        tym_sig    = transsig env i;
        tym_mforb  = Sp.empty; }

(* -------------------------------------------------------------------- *)
type tymod_cnv_failure =
| E_TyModCnv_ParamCountMismatch
| E_TyModCnv_ParamTypeMismatch of (EcIdent.t * tymod_cnv_failure)
| E_TyModCnv_MissingComp       of symbol
| E_TyModCnv_MismatchVarType   of symbol
| E_TyModCnv_MismatchFunSig    of symbol

exception TymodCnvFailure of tymod_cnv_failure

let tymod_cnv_failure e =
  raise (TymodCnvFailure e)

let tysig_item_name = function
  | Tys_variable (x, _) -> x
  | Tys_function f      -> f.fs_name

let tysig_item_kind = function
  | Tys_variable _ -> `Variable
  | Tys_function _ -> `Function

let rec check_tymod_cnv mode (env : EcEnv.env) (tin : tymod) (tout : tymod) =
  (* Check parameters for compatibility. Parameters names may be
   * different, hence, substitute in [tin.tym_params] types the names
   * of [tout.tym_params] *)
  
  if List.length tin.tym_params <> List.length tout.tym_params then
    tymod_cnv_failure E_TyModCnv_ParamCountMismatch;

  let bsubst =
    List.fold_left2
      (fun subst (xin, tyin) (xout, tyout) ->
        let tyin = EcSubst.subst_modtype subst tyin in
          begin
            try check_tymod_cnv `Eq env tyin tyout
            with
            | TymodCnvFailure e ->
                tymod_cnv_failure (E_TyModCnv_ParamTypeMismatch (xin, e))
          end;
          EcSubst.add subst xout (`Local xin))
      EcSubst.empty tin.tym_params tout.tym_params
  in
    (* Check for body inclusion (w.r.t the parameters names substitution).
     * This includes:
     * - Variables / functions inclusion with equal signatures +
     *   included use modifiers.
     * - Inclusion of forbidden names set *)

  let tin = EcSubst.subst_modtype bsubst tin in

  let check_item_compatible =
    let check_var_compatible (xin, tyin) (xout, tyout) =
      assert (xin = xout);
      if not (EcEnv.equal_type env tyin tyout) then
        tymod_cnv_failure (E_TyModCnv_MismatchVarType xin)

    and check_fun_compatible fin fout =
      assert (fin.fs_name = fout.fs_name);
      (* We currently reject function with compatible signatures but
       * for the arguments names. We plan to leviate this restriction
       * later on, but note that this may require to alpha-convert when
       * instnatiating an abstract module by a implementation. *)

      let arg_compatible (aname1, aty1) (aname2, aty2) =
           (EcIdent.name aname1) = (EcIdent.name aname2)
        && EcEnv.equal_type env aty1 aty2
      in

      let (iargs, oargs) = (fst fin.fs_sig, fst fin.fs_sig) in
      let (ires , ores ) = (snd fin.fs_sig, snd fin.fs_sig) in

        if List.length iargs <> List.length oargs then
          tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);
        if not (List.for_all2 arg_compatible iargs oargs) then
          tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);
        if not (EcEnv.equal_type env ires ores) then
          tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);

        let flcmp =
          match mode with
          | `Sub -> Mp.submap (fun _ flin flout -> UM.included flin flout)
          | `Eq  -> Mp.equal  (fun flin flout -> UM.equal flin flout)
        in
          if not (flcmp fin.fs_uses fout.fs_uses) then
            tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);

    in
      fun i_item o_item ->
        match i_item, o_item with
        | Tys_variable xin, Tys_variable xout -> check_var_compatible xin xout
        | Tys_function fin, Tys_function fout -> check_fun_compatible fin fout
        | _               , _                 -> assert false
  in

  let check_for_item (i_item : tysig_item) =
    let i_name = tysig_item_name i_item
    and i_kind = tysig_item_kind i_item in

    let o_item =
      List.findopt
        (fun o_item ->
             (tysig_item_name o_item) = i_name
          && (tysig_item_kind o_item) = i_kind)
        tout.tym_sig
    in
      match o_item with
      | None -> tymod_cnv_failure (E_TyModCnv_MissingComp i_name)
      | Some o_item -> check_item_compatible i_item o_item
  in
    List.iter check_for_item tin.tym_sig;

    if mode = `Eq then begin
      List.iter
        (fun o_item ->
          let o_name = tysig_item_name o_item
          and o_kind = tysig_item_kind o_item in
          let b =
            List.exists
              (fun i_item ->
                   (tysig_item_name i_item) = o_name
                && (tysig_item_kind i_item) = o_kind)
              tin.tym_sig
          in
            if not b then
              tymod_cnv_failure (E_TyModCnv_MissingComp o_name))
        tout.tym_sig
    end

let check_tymod_sub = check_tymod_cnv `Sub
and check_tymod_eq  = check_tymod_cnv `Eq

(* -------------------------------------------------------------------- *)
let rec transmod (env : EcEnv.env) (x : EcIdent.t) (m : pmodule_expr) =
  match m with
  | Pm_ident ({ pl_desc = m }, args) -> begin
      let (mname, mty) = EcEnv.Mod.lookup m env in
      let args = List.map (EcEnv.Mod.lookup^~ env) (unlocs args) in

        match mty.tym_params with
        | [] ->
            if args <> [] then
              tyerror dloc ModApplToNonFunctor;

            { me_name = x;
              me_body = ME_Ident mname;
              me_meta = None;     (* FIXME *)
              me_sig  = mty; }

        | _ ->
            let (anames, atymods) = List.split mty.tym_params in

            (* Check module application *)
            if List.length mty.tym_params <> List.length args then
              tyerror dloc ModApplInvalidArity;
            List.iter2
              (fun iarg arg ->
                try check_tymod_sub env arg iarg
                with TymodCnvFailure _ ->
                  tyerror dloc ModApplInvalidArgInterface)
              atymods (List.map snd args);

            (* EcSubstitute args. in result type *)
            let tyres =
              EcSubst.subst_modtype
                (EcSubst.create
                   (List.map2
                      (fun aname arg -> (aname, `Path (fst arg)))
                      anames args))
                { tym_params = [];
                  tym_sig    = mty.tym_sig;
                  tym_mforb  = Sp.empty; }
            in
              { me_name = x;
                me_body = ME_Application (mname, List.map fst args);
                me_meta = None;
                me_sig  = tyres; }
  end

  | Pm_struct st ->
      transstruct env x st

(* -------------------------------------------------------------------- *)
and transintf (env : EcEnv.env) ((iname, iargs) : pmodule_intf) : tymod =
  let rec transintf_r ((mname, margs) : pmodule_intf) : tymod =
    match EcEnv.Mod.trylookup (unloc mname) env with
    | None -> tyerror mname.pl_loc (UnknownModName (unloc mname))
    | Some (_, i) ->  begin
        if List.length i.tym_params <> List.length margs then
          tyerror dloc ModApplInvalidArity;
        List.iter2
          (fun marg (_, mtymod) ->
            check_tymod_sub env (transintf_r marg) mtymod)
          margs i.tym_params;
        i                             (* FIXME: subst *)
      end
  in
    match EcEnv.ModTy.trylookup (unloc iname) env with
    | None -> tyerror iname.pl_loc (UnknownTyModName (unloc iname))
    | Some (_, i) -> begin
        if List.length i.tym_params <> List.length iargs then
          tyerror dloc ModApplInvalidArity;
        List.iter2
          (fun iarg (_, mtymod) ->
            check_tymod_sub env (transintf_r iarg) mtymod)
          iargs i.tym_params;
        i                               (* FIXME: subst *)
    end

(* -------------------------------------------------------------------- *)
and transstruct (env : EcEnv.env) (x : EcIdent.t) (st : pstructure) =
  (* Check parameters types *)
  let stparams =
    List.map                          (* FIXME: exn *)
      (fun (a, aty) -> (EcIdent.create a.pl_desc,
                        snd (EcEnv.ModTy.lookup aty.pl_desc env)))
      st.ps_params
  in

  (* Check structure items, extending environment initially with
   * structure arguments, and then with previously checked items.
   *)
  let _, items =
    let tydecl1 ((x, obj) : EcIdent.t * _) =
      match obj with
      | MI_Module   m -> (x, `Module   m.me_sig)
      | MI_Variable v -> (x, `Variable (Some EcTypes.PVglob, v.v_type))
      | MI_Function f -> (x, `Function f.f_sig)
    in
      List.fold_left
        (fun (env, acc) item ->
          let newitems = transstruct1 env item in
            (EcEnv.bindall (List.map tydecl1 newitems) env,
             List.rev_append acc newitems))
        (EcEnv.Mod.bindall_s stparams env, [])
        st.ps_body
  in

  (* Generate structure signature *)
  let tymod =
    let tymod1 = function
      | MI_Module   _ -> None           (* FIXME: what ? *)
      | MI_Variable v -> Some (Tys_variable (EcIdent.name v.v_name, v.v_type))
      | MI_Function f -> Some (Tys_function f.f_sig) 
    in

    let sigitems = List.pmap tymod1 (List.map snd items) in
      { tym_params = stparams;
        tym_sig    = sigitems;
        tym_mforb  = Sp.empty; }
      
  in
    { me_name = x;
      me_body = ME_Structure { ms_params = stparams;
                               ms_body   = List.map snd items; };
      me_meta = None;
      me_sig  = tymod; }

(* -------------------------------------------------------------------- *)
and transstruct1 (env : EcEnv.env) (st : pstructure_item) =
  match st with
  | Pst_mod ({ pl_desc = m }, me, mi) ->
      let m  = EcIdent.create m in
      let me = transmod env m me in
      let mi = omap mi (transintf env) in
        oiter mi (fun mi -> check_tymod_sub env me.me_sig mi);
        [(m, MI_Module me)]

  | Pst_var (xs, ty) ->
      let ty = transty_nothing env ty in
        List.map
          (fun { pl_desc = x } ->
            let x = EcIdent.create x in
              (x, MI_Variable { v_name = x; v_type = ty; }))
          xs

  | Pst_fun (decl, body) -> begin
      let fid = EcIdent.create decl.pfd_name.pl_desc in
      let ue = UE.create (Some []) in
      let known_ids = ref Mstr.empty in
      let add_local s = 
        match Mstr.find_opt s.pl_desc !known_ids with
        | None -> 
            known_ids := Mstr.add s.pl_desc s !known_ids;
            EcIdent.create s.pl_desc
        | Some s' -> tyerror s.pl_loc (DuplicatedLocals (Some s')) in
      (* First we add the parameters *)
      let add_param (s,ty) = add_local s, transty tp_uni env ue ty in
      let params = List.map add_param decl.pfd_tyargs in
      let params_ = 
        List.map (fun (id,ty) -> id, `Variable (Some PVloc, ty)) params in
      let env = EcEnv.bindall params_ env in
      let init = ref [] in
      let locals = ref [] in
      let add_local ty s = add_local s, `Variable (Some PVloc, ty) in
      let add_locals env (ss,ty, e) = 
        let ty = transty tp_uni env ue ty in
        let locs = List.map (add_local ty) ss in
        let newenv = EcEnv.bindall locs env in
        List.iter (fun (id, _) -> locals := (id,ty) :: !locals) locs;
        oiter e (fun pe -> 
          let e, ety = transexp env ue pe in
          unify_error env ue pe.pl_loc ety ty;
          List.iter (fun (id,_) ->
            let p,_ = 
              oget (EcEnv.Var.trylookup_pv ([],(EcIdent.name id)) newenv) in
            init := Sasgn(LvVar(p,ty) , e) :: !init) locs);
        newenv in
      let env = List.fold_left add_locals env body.pfb_locals in
      let stmt = transstmt ue env body.pfb_body in 
      let rty = transty tp_uni env ue decl.pfd_tyresult in
      let re =
        match body.pfb_return with
        | None    -> 
            (* FIXME error message or location *)
            unify_error env ue decl.pfd_tyresult.pl_loc rty tunit; None
        | Some pe ->
            let re, ty = transexp env ue pe in
            unify_error env ue pe.pl_loc ty rty; Some re in
      let subst_uni = Tuni.subst (UE.close ue) in
      let check_type ty = 
        let ty = subst_uni ty in
        assert (EcUidgen.Suid.is_empty (Tuni.fv ty)); (* FIXME error message *)
        ty in
      let check_decl (id,ty) = id, check_type ty in
      let params = List.map check_decl params in
      let locals = List.rev_map check_decl !locals in
      let rty = check_type rty in
      let stmt = stmt_mapty subst_uni stmt in
      let re = omap re (Esubst.mapty subst_uni) in
      let fun_ = 
        { f_name   = fid;
          f_sig    = {
            fs_name = decl.pfd_name.pl_desc;
            fs_sig  = params, rty;
            fs_uses = Mp.empty;   (* FIXME *)
          };
          f_locals = locals;
          f_body   = stmt;
          f_ret    = re
        } in 
      [(fid, MI_Function fun_)]
  end

  | Pst_alias _ -> assert false

(* -------------------------------------------------------------------- *)
and transstmt ue (env : EcEnv.env) (stmt : pstmt) =
  List.map (transinstr ue env) stmt

(* -------------------------------------------------------------------- *)
and transinstr ue (env : EcEnv.env) (i : pinstr) =
  let transcall name args =
    let fpath, fsig =
      try  EcEnv.Fun.lookup name env
      with EcEnv.LookupFailure _ -> tyerror dloc (UnknownFunction name)
    in
      if List.length args <> List.length (fst fsig.fs_sig) then
        tyerror dloc ApplInvalidArity;
  
      let args =
        List.map2
          (fun a (_, ty) ->
            let a, aty = transexp env ue a in
              EcUnify.unify env ue aty ty; a)
          args (fst fsig.fs_sig)
      in
        (fpath, args, snd fsig.fs_sig)
  in

  match i with
  | PSasgn (lvalue, rvalue) -> begin
      let rvalue_as_fun () =
        match rvalue.pl_desc with
        | PEapp ({ pl_desc = name }, None, args) when  EcEnv.Fun.exists name env ->
            let (fpath, args, rty) = transcall name args in
              Some (`Call (fpath, args), rty)
        | _ -> None

      and rvalue_as_expr () =
        let e, ty = transexp env ue rvalue in
          Some (`Expr e, ty)
      in

      let lvalue, lty = translvalue ue env lvalue in
      let rvalue, rty = oget (List.fpick [rvalue_as_fun; rvalue_as_expr]) in

        EcUnify.unify env ue lty rty;
        match rvalue with
        | `Call (fpath, args) -> Scall (Some lvalue, fpath, args)
        | `Expr e -> Sasgn (lvalue, e)
    end
  | PSrnd(lvalue, rvalue) -> 
      let lvalue, lty = translvalue ue env lvalue in
      let rvalue, rty = transexp env ue rvalue in
      EcUnify.unify env ue (tdistr lty) rty;
      Srnd(lvalue,rvalue)

  | PScall ({ pl_desc = name }, args) ->
      let (fpath, args, rty) = transcall name args in
        EcUnify.unify env ue tunit rty;
        Scall (None, fpath, args)

  | PSif (e, s1, s2) ->
      let e, ety = transexp env ue e in
      let s1 = transstmt ue env s1 in
      let s2 = transstmt ue env s2 in
  
        EcUnify.unify env ue ety tbool;
        Sif (e, s1, s2)

  | PSwhile (e, body) ->
      let e, ety = transexp env ue e in
      let body = transstmt ue env body in

        EcUnify.unify env ue ety tbool;
        Swhile (e, body)

  | PSassert e ->
     let e, ety = transexp env ue e in 
       EcUnify.unify env ue ety tbool;
       Sassert e

(* -------------------------------------------------------------------- *)
and trans_pv env { pl_desc = x; pl_loc = loc } = 
  match EcEnv.Var.trylookup_pv x env with
  | None -> tyerror loc (UnknownVariable x)
  | Some(pv,xty) -> pv, xty 

and translvalue ue (env : EcEnv.env) lvalue =
  match lvalue with
  | PLvSymbol x ->
      let pty = trans_pv env x in
      LvVar pty, snd pty

  | PLvTuple xs -> 
      let xs = List.map (trans_pv env) xs in
      let ty = Ttuple (List.map snd xs) in
      (LvTuple xs, ty)

  | PLvMap (x, tvi, e) ->
      let tvi = transtvi env ue tvi in  
      let codomty = UE.fresh_uid ue in
      let pv,xty = trans_pv env x in
      let e, ety = transexp env ue e in
      let name =  ([],EcCoreLib.s_set) in
      let esig = [xty; ety; codomty] in
      let ops = select_op env name ue tvi esig in
      match ops with
      | [ ({tye_desc = Eop (p,tys) }, _, subue)] ->
          EcUnify.UniEnv.restore ~src:subue ~dst:ue;
          (LvMap ((p,tys), pv, e, codomty), codomty) 
      | _ ->        (* FIXME: better error message *)
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
          tyerror x.pl_loc (UnknownOperatorForSig (name, esig))
       
               

(* -------------------------------------------------------------------- *)
(** Translation of formula *)
type var_kind = 
  | Llocal of EcIdent.t * ty
  | Lprog  of EcTypes.prog_var * ty * Side.t
  | Lctnt  of EcPath.path * ty list * ty 

type op_kind = 
  | Lop of EcPath.path * operator
(*    | Lpred of EcPath.path * *)

module Fenv = struct

  type fenv = {
      fe_locals : (EcIdent.t * ty) EcIdent.Map.t; 
      fe_envs : EcEnv.env EcMaps.Mint.t;
      fe_cur : int
    }

  let mono_fenv env = {
    fe_locals = EcIdent.Map.empty;
    fe_envs = EcMaps.Mint.add 0 env EcMaps.Mint.empty;
    fe_cur = 0;
  }

  let mono fenv = 
    try EcMaps.Mint.find 0 fenv.fe_envs
    with _ -> assert false 

  let bind_local fenv x ty =
   { fenv with 
     fe_locals = EcIdent.Map.add x (x,ty) fenv.fe_locals }

  let bind_locals = List.fold_left2 bind_local 

  let fenv_hyps env hyps = 
    let fenv = mono_fenv env in
    let locals = 
      List.prmap (fun (id,k) -> 
        match k with EcFol.LD_var(ty,_) -> Some (id,ty) | _ -> None) 
        hyps.h_local in
    let lid,lty = List.split locals in
    bind_locals fenv lid lty 

  let current_env fenv = 
    try EcMaps.Mint.find fenv.fe_cur fenv.fe_envs 
    with _ -> assert false (* FIXME *)

  let set_side fenv side = 
    if EcMaps.Mint.mem side fenv.fe_envs then
      { fenv with fe_cur = side }
    else assert false (* FIXME *)

  let select_logical fenv (qs,s) =
    if qs = [] then
      match EcIdent.Map.byname s fenv.fe_locals with
      | None -> None
      | Some (x, ty) -> Some (x, snd ty)
    else None

  let select_op fenv name ue tvi psig =
    match select_logical fenv name with
    | Some(id,ty) ->
        if tvi <> None then assert false; (* FIXME error message *)
        [ (f_local id ty, ue) ]
    | None ->
        let pvs = select_pv (current_env fenv) name ue tvi psig in
        let ops = select_op1 true tvi (mono fenv) name ue psig in
        let side = fenv.fe_cur in
        List.map (fun (pv,ty,ue) -> f_pvar pv ty side, ue) pvs @ 
        List.map (fun ((op,tys), ty,ue) -> f_op op tys ty, ue) ops

end
      
let transl tp fenv ue decl = 
  let transl1 (fenv,ld) ({ pl_desc = x },pty) =
    let ty = transty tp (Fenv.mono fenv) ue pty in
    let x = EcIdent.create x in
    Fenv.bind_local fenv x ty, (x,ty)::ld in
  let fenv, ld = List.fold_left transl1 (fenv,[]) decl in
  fenv, List.rev ld

let transfpattern fenv ue (p : EcParsetree.lpattern) =
  match transpattern1 (Fenv.mono fenv) ue p with
  | LSymbol x, ty ->
      (Fenv.bind_local fenv x ty, LSymbol x, ty)
  | LTuple xs, (Ttuple lty as ty) ->
      (Fenv.bind_locals fenv xs lty, LTuple xs, ty)
  | _ -> assert false

let transform fenv ue pf tt =
  let rec transf fenv f = 
    match f.pl_desc with
    | PFint n -> f_int n
    | PFtuple args -> f_tuple (List.map (transf fenv) args)
    | PFident ({ pl_desc = name;pl_loc = loc }, tvi) -> 
        let tvi = transtvi (Fenv.mono fenv) ue tvi in
        let ops = Fenv.select_op fenv name ue tvi [] in
        begin match ops with
        | [] | _ :: _ :: _ -> (* FIXME: better error message *)
            tyerror loc (UnknownOperatorForSig (name, []))
        | [op, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            op
        end
    | PFside(f,side) ->
        let fenv = Fenv.set_side fenv side in
        transf fenv f
    | PFapp({ pl_desc = name; pl_loc = loc }, tvi, es) ->
        let tvi = transtvi (Fenv.mono fenv) ue tvi in  
        let es   = List.map (transf fenv) es in
        let esig = List.map EcFol.ty es in 
        let ops  = Fenv.select_op fenv name ue tvi esig in
        begin match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror loc (UnknownOperatorForSig (name, esig))

        | [op, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            let codom = ty_fun_app (Fenv.mono fenv) ue op.f_ty esig in
            f_app op es codom
        end

    | PFif(pf1,f2,f3) ->
        let f1 = transf fenv pf1 in
        unify_error (Fenv.mono fenv) ue pf1.pl_loc f1.f_ty tbool;
        let f2 = transf fenv f2 in
        let f3 = transf fenv f3 in
        f_if f1 f2 f3
    | PFlet(lp,pf1,f2) ->
        let (penv, p, pty) = transfpattern fenv ue lp in
        let f1 = transf fenv pf1 in
        unify_error (Fenv.mono fenv) ue pf1.pl_loc f1.f_ty pty;
        let f2 = transf penv f2 in
        f_let p f1 f2 
    | PFforall(xs, pf) ->
        let fenv, xs = transl tp_relax fenv ue xs in
        let f = transf fenv pf in
        unify_error (Fenv.mono fenv) ue pf.pl_loc f.f_ty tbool;
        f_forall xs f
    | PFexists(xs, f1) ->
        let fenv, xs = transl tp_relax fenv ue xs in
        let f = transf fenv f1 in
        unify_error (Fenv.mono fenv) ue pf.pl_loc f.f_ty tbool;
        f_exists xs f
    (* FIXME *) 
    | PFprob _ -> f_int 0 
    | PFforallm _ -> f_true 
    | PFexistsm _ -> f_true 
  in
  let f = transf fenv pf in
  unify_error (Fenv.mono fenv) ue pf.pl_loc f.f_ty tt;
  f 

let transformula fenv ue pf = 
  transform fenv ue pf tbool

 

