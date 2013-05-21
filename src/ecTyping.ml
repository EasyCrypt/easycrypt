(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcLocation
open EcParsetree
open EcTypes
open EcDecl
open EcModules
open EcFol

module MMsym = EcSymbols.MMsym

module Sp = EcPath.Sp
module Mp = EcPath.Mp

module Sm = EcPath.Sm
module Mm = EcPath.Mm

module Sx = EcPath.Sx
module Mx = EcPath.Mx

module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type modapp_error =
| MAE_WrongArgPosition
| MAE_WrongArgCount
| MAE_InvalidArgType

type modtyp_error =
| MTE_FunSigDoesNotRepeatArgNames

type funapp_error =
| FAE_WrongArgCount

type mem_error =
| MAE_IsConcrete

type tyerror =
| UniVarNotAllowed
| TypeVarNotAllowed
| OnlyMonoTypeAllowed
| UnboundTypeParameter of symbol
| UnknownTypeName      of qsymbol
| InvalidTypeAppl      of qsymbol * int * int
| DuplicatedTyVar
| DuplicatedLocal      of symbol
| NonLinearPattern
| TypeMismatch         of (ty * ty) * (ty * ty)
| UnknownVarOrOp       of qsymbol * ty list
| MultipleOpMatch      of qsymbol * ty list
| UnknownModName       of qsymbol
| UnknownTyModName     of qsymbol
| UnknownFunName       of qsymbol
| UnknownModVar        of qsymbol
| UnknownMemName       of int * symbol
| InvalidFunAppl       of funapp_error
| InvalidModAppl       of modapp_error
| InvalidModType       of modtyp_error
| InvalidMem           of symbol * mem_error
| OnlyModParamAreOracle of qsymbol
exception TyError of EcLocation.t * EcEnv.env * tyerror

let tyerror loc env e = raise (TyError (loc, env, e))

(* -------------------------------------------------------------------- *)
let pp_tyerror fmt env error =
  let msg x = Format.fprintf fmt x in

  let pp_type fmt ty =
    EcPrinting.pp_type env fmt ty
  in

  match error with
  | UniVarNotAllowed ->
      msg "type place holders not allowed"

  | TypeVarNotAllowed ->
      msg "type variables not allowed"

  | OnlyMonoTypeAllowed ->
      msg "only monomorph types allowed here"

  | UnboundTypeParameter x ->
      msg "unbound type parameter: %s" x

  | UnknownTypeName qs ->
      msg "unknown type name: %a" pp_qsymbol qs

  | InvalidTypeAppl (name, _, _) ->
      msg "invalid type application: %a" pp_qsymbol name

  | DuplicatedTyVar ->
      msg "a type variable appear at least twice"

  | DuplicatedLocal name ->
      msg "duplicated local/parameters name: %s" name

  | NonLinearPattern ->
      msg "non-linear pattern matching"

  | TypeMismatch ((ty1, ty2), _) ->
      msg "incompatible type\n";
      msg "expecting: %a" pp_type ty1;
      msg "      got: %a" pp_type ty2

  | UnknownVarOrOp (name, _) ->
      msg "unknown variable or operator: %a" pp_qsymbol name

  | MultipleOpMatch (name, _) ->
      msg "more than one operator matches: %a" pp_qsymbol name

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

  | InvalidModAppl MAE_WrongArgPosition ->
      msg "invalid module application: wrong arguments position"

  | InvalidModAppl MAE_WrongArgCount ->
      msg "invalid module application: wrong number of arguments"

  | InvalidModAppl MAE_InvalidArgType ->
      msg "invalid module application: arguments do not match required interfaces"

  | InvalidModType MTE_FunSigDoesNotRepeatArgNames ->
      msg "applied argument names must repeat functor argument names"

  | InvalidMem (name, MAE_IsConcrete) ->
      msg "the memory %s must be abstract" name
  | OnlyModParamAreOracle name ->
    msg "the function %a is not provided by a module parameter"
      pp_qsymbol name

let () =
  let pp fmt exn =
    match exn with
    | TyError (_, env, e) -> pp_tyerror fmt env e
    | _ -> raise exn
  in
    EcPException.register pp

(* -------------------------------------------------------------------- *)
module UE = EcUnify.UniEnv

let unify_or_fail (env : EcEnv.env) ue loc ty1 ty2 = 
  try  EcUnify.unify env ue ty1 ty2 
  with EcUnify.UnificationFailure(t1, t2) ->
    let tyinst = Tuni.subst (UE.asmap ue) in
      tyerror loc env (TypeMismatch ((tyinst ty1, tyinst ty2),
                                     (tyinst  t1, tyinst  t2)))

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
let empty_uses : uses =
  { us_calls  = [];
    us_reads  = Sx.empty;
    us_writes = Sx.empty; }

let add_call (u : uses) p : uses =
  { u with us_calls = p :: u.us_calls }

let add_read (u : uses) p : uses =
  { u with us_reads = Sx.add p u.us_reads }

let add_write (u : uses) p : uses =
  { u with us_writes = Sx.add p u.us_writes }

let norm_uses (env : EcEnv.env) (u : uses) =
  let norm map =
    Sx.fold
      (fun p map -> Sx.add (EcEnv.NormMp.norm_xpath env p) map)
      Sx.empty map
  in
    (norm (Sx.of_list u.us_calls), (norm u.us_reads, norm u.us_writes))

let (i_inuse, s_inuse, se_inuse) =
  let rec lv_inuse (map : uses) (lv : lvalue) =
    match lv with
    | LvVar (p,_) ->
        add_write map p.pv_name

    | LvTuple ps ->
        List.fold_left
          (fun map (p, _) -> add_write map p.pv_name)
          map ps

    | LvMap (_, p, e, _) ->
      (* Maps are not modified in place but feed to a mutator
         operator that returns the augmented map and assigning the
         result to [p]. Hence the [`Read | `Write] flag. *)
      let map = add_write (add_read map p.pv_name) p.pv_name in
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

  and s_inuse (map : uses) (s : stmt) =
    List.fold_left i_inuse map s.s_node

  and se_inuse (u : uses) (e : expr) =
    { u with us_reads = Sx.union u.us_reads (e_inuse e) }

  in
    (i_inuse empty_uses, s_inuse empty_uses, se_inuse)

(* -------------------------------------------------------------------- *)
let select_local env (qs,s) = 
  if   qs = []
  then EcEnv.Var.lookup_local_opt s env 
  else None 

let select_pv env side name ue tvi psig = 
  if   tvi <> None
  then []
  else
    try
      let pvs = EcEnv.Var.lookup_progvar ?side name env in 
      let select (pv,ty) = 
        let subue = UE.copy ue in
        let texpected = EcUnify.tfun_expected subue psig in
        EcUnify.unify env subue ty texpected;
        [(pv, ty, subue)]
      in
        select pvs
    with EcEnv.LookupFailure _ -> []

let gen_select_op pred tvi env name ue psig =
  match select_local env name with
  | Some(id, ty) -> 
      if tvi <> None then assert false; (* FIXME error message *)
      [ (e_local id ty, ty, ue) ]
  | None ->
      let pvs = select_pv env None name ue tvi psig in
      let ops = EcUnify.select_op pred tvi env name ue psig in
      List.map (fun (pv,ty,ue) -> e_var pv ty, ty, ue) pvs @ 
      List.map (fun ((op,tys), ty,ue) -> e_op op tys ty, ty, ue) ops

let select_op env name ue tvi psig =
  gen_select_op false tvi env name ue psig 

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
let ue_for_decl (env : EcEnv.env) (loc, tparams) =
  let tparams = omap tparams
    (fun tparams ->
      let tparams = List.map unloc tparams in
        if not (List.uniq tparams) then
          tyerror loc env DuplicatedTyVar;
        List.map EcIdent.create tparams)
  in
    EcUnify.UniEnv.create tparams

(* -------------------------------------------------------------------- *)
let rec transty (tp : typolicy) (env : EcEnv.env) ue ty =
  match ty.pl_desc with
   | PTunivar ->
       if   tp.tp_uni
       then UE.fresh_uid ue
       else tyerror ty.pl_loc env UniVarNotAllowed

   | PTvar s ->
       if tp.tp_tvar then 
         try tvar (UE.get_var ue s.pl_desc)
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
        
  | PTapp ({ pl_desc = name }, tyargs) -> begin
      match EcEnv.Ty.lookup_opt name env with
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

and transtys tp (env : EcEnv.env) ue tys = 
  List.map (transty tp env ue) tys

let transty_for_decl =
  let ue = UE.create (Some []) in
  fun env ty -> transty tp_nothing env ue ty

(* -------------------------------------------------------------------- *)
let transpattern1 env ue (p : EcParsetree.plpattern) = 
  match p.pl_desc with
  | LPSymbol { pl_desc = x } ->
      let ty = UE.fresh_uid ue in
      let x  = EcIdent.create x in
      (LSymbol (x,ty), ty)

  | LPTuple xs ->
      let xs = unlocs xs in
      if not (List.uniq xs) then
        tyerror p.pl_loc env NonLinearPattern
      else
        let xs     = List.map EcIdent.create xs in
        let subtys = List.map (fun _ -> UE.fresh_uid ue) xs in
        (LTuple (List.combine xs subtys), ttuple subtys)

let transpattern env ue (p : EcParsetree.plpattern) =
  match transpattern1 env ue p with
  | (LSymbol (x,ty)) as p, _ ->
      EcEnv.Var.bind_local x ty env, p, ty

  | LTuple xs as p, ty ->
      EcEnv.Var.bind_locals xs env, p, ty

(* -------------------------------------------------------------------- *)
let transtvi env ue tvi = 
  match tvi.pl_desc with
  | TVIunamed lt ->
      UE.TVIunamed (List.map (transty tp_relax env ue) lt)

  | TVInamed lst ->
      let add locals (s, t) =
        if List.exists (fun (s', _) -> unloc s = unloc s') locals then
          tyerror tvi.pl_loc env DuplicatedTyVar;
        (s, transty tp_relax env ue t) :: locals
      in

      let lst = List.fold_left add [] lst in
        UE.TVInamed (List.rev_map (fun (s,t) -> unloc s, t) lst)
  
let rec destr_tfun env ue tf = 
  match tf.ty_node with
  | Tunivar _ ->
      let tf' = UE.repr ue tf in
      assert (not (tf == tf')); (* FIXME error message *)
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

let transbinding env ue bd =
  let trans_bd1 env (xs, pty) = 
    let ty = transty tp_relax env ue pty in
    let xs = List.map (fun x -> EcIdent.create x.pl_desc, ty) xs in
    let env = EcEnv.Var.bind_locals xs env in
    env, xs in
  let env, bd = List.map_fold trans_bd1 env bd in
  let bd = List.flatten bd in
  env, bd

let transexp (env : EcEnv.env) (ue : EcUnify.unienv) e =
  let rec transexp (env : EcEnv.env) (e : pexpr) =
    let loc = e.pl_loc in

    match e.pl_desc with
    | PEint i -> (e_int i, tint)

    | PEident ({ pl_desc = name }, tvi) -> 
        let tvi = omap tvi (transtvi env ue) in
        let ops = select_op env name ue tvi [] in
        begin match ops with
        | [] -> tyerror loc env (UnknownVarOrOp (name, []))

        | _ :: _ :: _ ->
            tyerror loc env (MultipleOpMatch (name, []))

        | [op, ty, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            op, ty
        end

    | PEapp ({pl_desc = PEident({ pl_desc = name; pl_loc = loc }, tvi)}, es) ->
        let tvi  = omap tvi (transtvi env ue) in  
        let es   = List.map (transexp env) es in
        let esig = snd (List.split es) in
        let ops  = select_op env name ue tvi esig in
        begin match ops with
        | [] ->
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
          tyerror loc env (UnknownVarOrOp (name, esig))

        | _ :: _ :: _ ->
            let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
              tyerror loc env (MultipleOpMatch (name, esig))
              
        | [op, ty, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            let codom = ty_fun_app env ue ty esig in
              (e_app op (List.map fst es) codom, codom)
        end

    | PEapp (pe, pes) ->
        let e,ty = transexp env pe in
        let es = List.map (transexp env) pes in
        let esig = snd (List.split es) in
        let codom = ty_fun_app env ue ty esig in
          (e_app e (List.map fst es) codom, codom)

    | PElet (p, pe1, pe2) ->
        let (penv, pt, pty) = transpattern env ue p in
  
        let e1, ty1 = transexp  env pe1 in
        unify_or_fail env ue p.pl_loc pty ty1;
  
        let e2, ty2 = transexp penv pe2 in
        (e_let pt e1 e2, ty2)

    | PEtuple es ->
        let tes = List.map (transexp env) es in
        let es, tys = List.split tes in
          (e_tuple es, ttuple tys)

    | PEif (pc, pe1, pe2) ->
      let c, tyc = transexp env pc in
      let e1, ty1 = transexp env pe1 in
      let e2, ty2 = transexp env pe2 in
        unify_or_fail env ue pc.pl_loc tyc tbool;
        unify_or_fail env ue pe2.pl_loc ty2 ty1;
        (e_if c e1 e2, ty1)

    | PElambda(bd, pe) ->
        let env, xs = transbinding env ue bd in
        let e, ty = transexp env pe in
        let ty =
          List.fold_right
            (fun (_, xty) ty -> EcTypes.tfun xty ty)
            xs ty
        in
          (e_lam xs e, ty)

  in
    transexp env e

let transexpcast (env : EcEnv.env) (ue : EcUnify.unienv) t e =
  let (e', t') = transexp env ue e in

  try  EcUnify.unify env ue t' t; e'
  with EcUnify.UnificationFailure (t1, t2) ->
    tyerror e.pl_loc env (TypeMismatch ((t', t), (t1, t2)))

(* -------------------------------------------------------------------- *)
exception DuplicatedSigItemName
exception DuplicatedArgumentsName of pfunction_decl

(* -------------------------------------------------------------------- *)
let name_of_sigitem = function
  | `VariableDecl v -> v.pvd_name
  | `FunctionDecl f -> f.pfd_name

(* -------------------------------------------------------------------- *)
let lookup_module (env : EcEnv.env) (name : pqsymbol) =
  match EcEnv.Mod.lookup_opt (unloc name) env with
  | None   -> tyerror name.pl_loc env (UnknownModName (unloc name))
  | Some x -> x

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
   (* mt_forb   = 
      (* TODO BENJ : get the top module in normal form *)
      List.fold_left (fun f m ->
        Sm.add (fst (lookup_module env m)) f) Sm.empty restr *)
  } in
    (modty, sig_)


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
  let transsig1 = function
    | `VariableDecl _x -> assert false (* Not implemented for the moment *)
(*        let name  = x.pvd_name.pl_desc in
        let type_ = transty_nothing env x.pvd_type in
          Tys_variable { v_name = name; v_type = type_ } *)

    | `FunctionDecl f ->
        let name   = f.pfd_name in
        let tyargs =
          List.map                      (* FIXME: continuation *)
            (fun (x, ty) -> { v_name = x.pl_desc; 
                              v_type = transty_for_decl env ty})
            f.pfd_tyargs
        in
        let resty = transty_for_decl env f.pfd_tyresult in
          if not (List.uniq (List.map fst f.pfd_tyargs)) then
            raise (DuplicatedArgumentsName f);
        let calls = 
          match f.pfd_uses with
          | None -> []
          | Some pfd_uses ->
            List.map (fun name -> 
              let f, _ = lookup_fun env name in
              let p = f.EcPath.x_top in
              if not (Sm.mem p sa) then 
                tyerror name.pl_loc env (OnlyModParamAreOracle name.pl_desc);
              f
            )
              pfd_uses in
        Tys_function
          ({ fs_name   = name.pl_desc;
             fs_params = tyargs;
             fs_ret    = resty; },
           { oi_calls = calls;
             (*oi_reads = Sx.empty;
             oi_writes = Sx.empty; *)
             })
  in

  let items = List.map transsig1 is in
  let names = List.map name_of_sigitem is in

    if not (List.uniq names) then
      raise DuplicatedSigItemName
    else
      items

(* -------------------------------------------------------------------- *)
type tymod_cnv_failure =
| E_TyModCnv_ParamCountMismatch
| E_TyModCnv_ParamTypeMismatch of EcIdent.t
| E_TyModCnv_MissingComp       of symbol
| E_TyModCnv_MismatchVarType   of symbol
| E_TyModCnv_MismatchFunSig    of symbol

exception TymodCnvFailure of tymod_cnv_failure

(*
let check_mod_app_disjoint env mp =
  let norm_nu nu = 
    EcPath.Sm.fold (fun mp nu ->
      match (EcEnv.Mod.by_mpath mp env).me_body with
      | ME_Decl _ -> EcPath.Sm.add mp nu 
      | ME_Structure ms ->
        EcPath.Sm.add mp (EcPath.Sm.union ms.ms_uses nu)
      | ME_Alias _ -> assert false) 
      nu EcPath.Sm.empty in
(* FIXME : the ms_uses field is rely in normal form ? *)
  let disjoint mp1 mp2 = 
    let me1, me2 = EcEnv.Mod.by_mpath mp1 env, EcEnv.Mod.by_mpath mp2 env in
    match me1.me_body, me2.me_body with
    | ME_Decl(_,nu1), ME_Decl(_,nu2) ->
      EcPath.Sm.mem mp2 nu1 || EcPath.Sm.mem mp1 nu2
    | ME_Decl(_,nu1), ME_Structure ms2 ->
      let nu1 = norm_nu nu1 in
      EcPath.Sm.mem mp2 nu1 &&
        EcPath.Sm.for_all (fun m -> EcPath.Sm.mem m nu1) ms2.ms_uses
    | ME_Structure ms1, ME_Decl(_,nu2) ->
      let nu2 = norm_nu nu2 in
      EcPath.Sm.mem mp1 nu2 &&
        EcPath.Sm.for_all (fun m -> EcPath.Sm.mem m nu2) ms1.ms_uses
    | ME_Structure ms1, ME_Structure ms2 ->
      let us1 = EcPath.Sm.add mp1 ms1.ms_uses in
      let us2 = EcPath.Sm.add mp2 ms2.ms_uses in
      EcPath.Sm.disjoint us1 us2 
    | _, _ -> assert false in
  let rec uses us mp = 
    let top = 
      match mp.EcPath.m_top with
      | `Concrete(p,_) -> EcPath.mpath (`Concrete(p,None)) [] 
      | t              -> EcPath.mpath t [] in
    List.fold_left uses (EcPath.Sm.add top us) mp.EcPath.m_args in
  let rec check f a = 
    let uses = uses EcPath.Sm.empty a in
    if EcPath.Sm.for_all (fun u ->
      EcPath.Sm.for_all (disjoint u) f) uses then
      EcPath.Sm.union uses f 
    else assert false in (* TODO error message *)
  let mp = EcEnv.NormMp.norm_mpath env mp in
  let top = 
    match mp.EcPath.m_top with
    | `Concrete(p,_) -> EcPath.mpath (`Concrete(p,None)) [] 
    | t              -> EcPath.mpath t [] in
  let f = EcPath.Sm.singleton top in
  ignore (List.fold_left check f mp.EcPath.m_args)
*)
let tymod_cnv_failure e =
  raise (TymodCnvFailure e)

let tysig_item_name = function
(*  | Tys_variable {v_name = x } -> x *)
  | Tys_function (f,_)      -> f.fs_name

let tysig_item_kind = function
(*  | Tys_variable _ -> `Variable *)
  | Tys_function _ -> `Function


let rec check_tymod_cnv mode (env : EcEnv.env) tin tout =
  (* Check parameters for compatibility. Parameters names may be
   * different, hence, substitute in [tin.tym_params] types the names
   * of [tout.tym_params] *)
  
  if List.length tin.mis_params <> List.length tout.mis_params then
    tymod_cnv_failure E_TyModCnv_ParamCountMismatch;

  let bsubst =
    List.fold_left2
      (fun subst (xin, tyin) (xout, tyout) ->
        let tyin = EcSubst.subst_modtype subst tyin in
          begin
            if not (EcEnv.ModTy.mod_type_equiv env tyin tyout) then
              tymod_cnv_failure (E_TyModCnv_ParamTypeMismatch xin)
          end;
          EcSubst.add_module subst xout (EcPath.mident xin))
      EcSubst.empty tin.mis_params tout.mis_params
  in
    (* Check for body inclusion (w.r.t the parameters names substitution).
     * This includes:
     * - Variables / functions inclusion with equal signatures +
     *   included use modifiers.
     * - Inclusion of forbidden names set *)
  (* TODO PY : Should we inverse the subtitution (ie subst in tout) *)
  let tin  = EcSubst.subst_modsig_body bsubst tin.mis_body
  and tout = tout.mis_body in

  let check_item_compatible =
   (* let check_var_compatible vdin vdout = 
      assert (vdin.v_name = vdout.v_name);
      if not (EcReduction.equal_type env vdin.v_type vdout.v_type) then
        tymod_cnv_failure (E_TyModCnv_MismatchVarType vdin.v_name) in *)

    let check_fun_compatible fin fout =
      assert (fin.fs_name = fout.fs_name);
      (* We currently reject function with compatible signatures but
       * for the arguments names. We plan to leviate this restriction
       * later on, but note that this may require to alpha-convert when
       * instantiating an abstract module with an implementation. *)

      let arg_compatible vd1 vd2 = 
        vd1.v_name = vd2.v_name && EcReduction.equal_type env vd1.v_type vd2.v_type 
      in

      let (iargs, oargs) = (fin.fs_params, fout.fs_params) in
      let (ires , ores ) = ( fin.fs_ret, fout.fs_ret) in

        if List.length iargs <> List.length oargs then
          tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);
        if not (List.for_all2 arg_compatible iargs oargs) then
          tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);
        if not (EcReduction.equal_type env ires ores) then
          tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);

        let flcmp () =
          true 
(* TODO B : FIXME *)
(*
          let (icalls, (ireads, iwrites)) = norm_uses env fin.fs_uses
          and (ocalls, (oreads, owrites)) = norm_uses env fout.fs_uses in

          match mode with
          | `Sub ->
                 (Sx.subset icalls  ocalls )
              && (Sx.subset ireads  oreads )
              && (Sx.subset iwrites owrites)

          | `Eq  ->
                 (Sx.equal icalls  ocalls )
              && (Sx.equal ireads  oreads )
              && (Sx.equal iwrites owrites)
*)

        in
          if false then                 (* FIXME: renable *)
            if not (flcmp ()) then
              tymod_cnv_failure (E_TyModCnv_MismatchFunSig fin.fs_name);

    in
      fun i_item o_item ->
        match i_item, o_item with
(*        | Tys_variable xin, Tys_variable xout -> check_var_compatible xin xout *)
        | Tys_function (fin,_), Tys_function (fout,_) -> check_fun_compatible fin fout
(*        | _               , _                 -> assert false *)
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

let check_tymod_sub = check_tymod_cnv `Sub
and check_tymod_eq  = check_tymod_cnv `Eq

(* -------------------------------------------------------------------- *)
let rec transmod (env : EcEnv.env) (x : symbol) (me : pmodule_expr) =
  match me.pl_desc with
  | Pm_ident (m, args) -> begin
      let (mname, mty) = lookup_module env m in
      let args = List.map (lookup_module env) args in
      let atymods = mty.me_sig.mis_params in
      (* Check module application *)
      if List.length atymods <> List.length args then
        tyerror me.pl_loc env (InvalidModAppl MAE_WrongArgCount);
      let metypes =
        let metype1 mty1 =
          assert (List.length mty1.mt_params = List.length atymods);
          let s =
            List.fold_left2
              (fun s (xarg, _) (xty, _) ->
                 EcSubst.add_module s xty xarg)
              EcSubst.empty args mty1.mt_params
          in
            { mty1 with
                mt_params = [];
                mt_args   = List.map (EcSubst.subst_mpath s) mty1.mt_args; }
        in
          List.map metype1 mty.me_types
      in
      let bsubst =
        List.fold_left2
          (fun subst (xarg, arg) (xty, tymod) ->
             let tymod = EcSubst.subst_modtype subst tymod in
             if not (EcEnv.ModTy.has_mod_type env arg.me_types tymod) then
               tymod_cnv_failure (E_TyModCnv_ParamTypeMismatch xty);
             EcSubst.add_module subst xty xarg)
          EcSubst.empty args atymods
      in
        (* EcSubstitute args. in result type *)
      { me_name  = x;
        me_body  = ME_Alias (EcPath.m_apply mname (List.map fst args));
        me_comps = EcSubst.subst_module_comps bsubst mty.me_comps;
        me_sig   = {
          mis_params = [];
          mis_body   = EcSubst.subst_modsig_body bsubst mty.me_sig.mis_body;
        };
        me_types = metypes; }
  end

  | Pm_struct st ->
    let res = transstruct env x st in
    res

(* -------------------------------------------------------------------- *)
and transstruct (env : EcEnv.env) (x : symbol) (st : pstructure) =
  (* Check parameters types *) (* FIXME: dup names *)
  let stparams =
    List.map                          (* FIXME: exn *)
      (fun (a, aty) ->
         (EcIdent.create a.pl_desc, fst (transmodtype env aty)))
      st.ps_params
  in

  (* Check structure items, extending environment initially with
   * structure arguments, and then with previously checked items.
   *)
  let (envi, items) =
    let tydecl1 (x, obj) =
      match obj with
      | MI_Module   m -> (x, `Module   m)
      | MI_Variable v -> (x, `Variable (EcTypes.PVglob, v.v_type))
      | MI_Function f -> (x, `Function f)
    in

    let env = EcEnv.Mod.enter x stparams env in
    List.fold_left
      (fun (env, acc) item ->
        let newitems = transstruct1 env item in
        let env = EcEnv.bindall (List.map tydecl1 newitems) env in
        (env, List.rev_append acc newitems))
      (env, []) st.ps_body
  in

  (* Generate structure signature *)
  let tymod =
    let tymod1 = function
      | MI_Module   _  -> None
      | MI_Variable _v -> None           (* Some (Tys_variable v)  *)
      | MI_Function f  -> 
(* TODO B : Fix oracle info ? *)
        Some (Tys_function (f.f_sig, {oi_calls  = [];
                                      (*oi_reads  = Sx.empty;
                                      oi_writes = Sx.empty; *)}))
    in

    let sigitems = List.pmap tymod1 (List.map snd items) in
      { mis_params = stparams;
        mis_body   = sigitems; };    (* FIXME *)
  in

  (* Check that generated signature is structurally included in
   * associated type mode. *)
  let types =
    List.map
      (fun { pl_desc = (aty, oatyp); pl_loc = loc } ->
        if oatyp <> [] then begin
          let cmp (x1, _) x2 = (EcIdent.name x1 = unloc x2) in
            if not (List.all2 cmp stparams oatyp) then
                tyerror loc env
                  (InvalidModType MTE_FunSigDoesNotRepeatArgNames)
        end;
(*        TODO B : FIXME restriction *)
        let (aty, asig) = transmodtype env aty in
        let aparams =
          match oatyp = [] with
          | true  -> stparams @ asig.mis_params
          | false -> asig.mis_params
        in
        check_tymod_sub env tymod { asig with mis_params = aparams };
        match oatyp = [] with
        | true  -> { aty with mt_params = stparams @ aty.mt_params }
        | false ->
          let subst =
            List.fold_left2
              (fun subst (x1, _) (x2, _) ->
                EcSubst.add_module subst x1 (EcPath.mident x2))
              EcSubst.empty asig.mis_params aty.mt_params
          in
          { aty with
            mt_params = asig.mis_params;
            mt_args   = List.map (EcSubst.subst_mpath subst) aty.mt_args })
      st.ps_signature
  in
  (* Construct structure representation *)
  let items = List.map snd items in
  (* TODO : PY : it is strange to have the module parameter in the path of the
                 variable *)
  let vars = 
    List.fold_left (fun vs item ->
      match item with
      | MI_Module me ->
        begin match me.me_body with
        | ME_Structure ms -> 
          EcPath.Mx.union (fun _ _ _ -> assert false) vs ms.ms_vars
        | _ -> vs 
        end 
      | MI_Variable x ->
        let mp = EcEnv.mroot env in
        let xp  = EcPath.xpath mp (EcPath.psymbol x.v_name) in
        EcPath.Mx.add xp x.v_type vs
      | MI_Function _ -> vs) EcPath.Mx.empty items in

  let mroot = EcEnv.mroot envi in
  let top = 
    match mroot.EcPath.m_top with
    | `Concrete(p,_) -> EcPath.mpath (`Concrete(p,None)) []
    | _ -> assert false in
  let rm = List.fold_left (fun rm mp -> EcPath.Sm.add mp rm) 
    (EcPath.Sm.singleton top) mroot.EcPath.m_args in
  let rec add_uses us mp = 
    let mp = EcEnv.NormMp.norm_mpath envi mp in
    let top = 
      match mp.EcPath.m_top with
      | `Concrete(p,_) -> EcPath.mpath (`Concrete(p,None)) [] 
      | t -> EcPath.mpath t [] in
    let us = 
      if EcPath.Sm.mem top rm then us 
      else
        let uses = 
          match (EcEnv.Mod.by_mpath top envi).me_body with
          | ME_Structure ms -> EcPath.Sm.add top ms.ms_uses
          | _ -> assert false in
        EcPath.Sm.union uses us in
    List.fold_left add_uses us mp.EcPath.m_args in
  let rec uses us items = 
    List.fold_left (fun us item ->
      match item with
      | MI_Module me ->
        begin match me.me_body with
        | ME_Structure ms -> EcPath.Sm.union us ms.ms_uses 
        | ME_Alias mp -> add_uses us mp 
        | ME_Decl _ -> assert false
        end
      | MI_Variable _ -> us
      | MI_Function fd ->
        begin match fd.f_def with
        | FBdef fdef ->
          let fus = fdef.f_uses in
          let us = 
            List.fold_left (fun us fn ->
              add_uses us fn.EcPath.x_top) us fus.us_calls in
          EcPath.Sx.fold (fun xp us ->
            add_uses us xp.EcPath.x_top)
            (EcPath.Sx.union fus.us_reads fus.us_writes) us
        | FBabs _ -> assert false
        end) us items in
  let uses = uses EcPath.Sm.empty items in
(*  Format.printf "uses %s = " (EcPath.m_tostring mroot);
  EcPath.Sm.iter (fun m -> Format.printf "%s " (EcPath.m_tostring m))
    uses;
  Format.printf "@."; *)
  { me_name  = x;
    me_body  = 
      ME_Structure 
        { ms_params = stparams;
          ms_body   = items; 
          ms_vars   = vars; 
          ms_uses   = uses };
    me_comps = items;
    me_sig   = tymod;
    me_types = types; }
  
(* -------------------------------------------------------------------- *)
and transstruct1 (env : EcEnv.env) (st : pstructure_item) =
  match st with
  | Pst_mod ({ pl_desc = m }, me) ->
    let me = transmod env m me in
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
      let params =
        let params = ref [] in
        let add_param (x, pty) =
          let ty = transty tp_uni !env ue pty in
          let pr = (unloc x, `Variable (PVloc, ty)) in
            fundef_add_symbol !env symbols x;
            params  := ({ v_name = unloc x; v_type = ty }, pty.pl_loc) :: !params;
            env     := EcEnv.bindall [pr] !env
        in
          List.iter add_param decl.pfd_tyargs;
          List.rev !params
      in

      (* Type-check body *)
      let retty = transty tp_uni !env ue decl.pfd_tyresult in
      let (env, stmt, result, prelude, locals) =
        transbody ue symbols !env retty body
      in

      (* Close all types *)
      let su      = Tuni.subst (UE.close ue) in
      let retty   = fundef_check_type su env (retty, decl.pfd_tyresult.pl_loc) in
      let params  = List.map (fundef_check_decl  su env) params in
      let locals  = List.map (fundef_check_decl  su env) locals in
      let prelude = List.map (fundef_check_iasgn su env) prelude in

      let clsubst = { EcTypes.e_subst_id with es_ty = su } in
      let stmt    = s_subst clsubst stmt
      and result  = omap result (e_subst clsubst) in
      let stmt    = EcModules.stmt (prelude @ stmt.s_node) in

      (* Computes reads/writes/calls *)
      let uses = ofold result ((^~) se_inuse) (s_inuse stmt) in

      (* Compose all results *)
      let fun_ =
        { f_name   = decl.pfd_name.pl_desc;
          f_sig    = {
            fs_name   = decl.pfd_name.pl_desc;
            fs_params = params;
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

  | Pst_alias _ -> assert false

(* -------------------------------------------------------------------- *)
and transbody ue symbols (env : EcEnv.env) retty pbody =
    let env     = ref env
    and prelude = ref []
    and locals  = ref [] in

    let mpath = oget (EcEnv.xroot !env) in

    (* Type-check local variables / check for dups *)
    let add_local (xs, pty, init) =
      List.iter (fundef_add_symbol !env symbols) xs;

      let ty     = transty tp_uni !env ue pty in
      let xsvars =
        match xs with
        | [_] -> [ty]
        | _   -> List.map (fun _ -> UE.fresh_uid ue) xs in
      let init   =
        let check_init pinit =
          let (init, initty) = transexp !env ue pinit in
            unify_or_fail !env ue pinit.pl_loc ty initty;
            init
        in
          omap init check_init
      in
        begin
          let xsty =
            match xsvars with
            | [ty] -> ty
            | _    -> ttuple xsvars
          in
            unify_or_fail !env ue pty.pl_loc ty xsty
        end;

        env := begin
          let topr = fun x xty -> (unloc x, `Variable (PVloc, xty)) in
            EcEnv.bindall (List.map2 topr xs xsvars) !env
        end;

        let mylocals =
          List.map2
            (fun x xty ->
               let x = unloc x in
               let p = EcPath.xqname mpath x in
                 ({ v_name  = x; v_type  = xty   },
                  { pv_name = p; pv_kind = PVloc },
                  xty, pty.pl_loc))
            xs xsvars
        in

        locals :=
           List.rev_append
            (List.map (fun (v, _, _, pl) -> (v, pl)) mylocals)
            !locals;

        oiter init
          (fun init ->
            let iasgn =
              List.map (fun (_, v, xty, _) -> (v, xty)) mylocals
            in
               prelude := (iasgn, init, pty.pl_loc) :: !prelude)
    in

    List.iter add_local pbody.pfb_locals;

    let body   = transstmt ue !env pbody.pfb_body in
    let result =
      match pbody.pfb_return with
      | None ->
          unify_or_fail !env ue EcLocation._dummy retty tunit;
          None

      | Some pe ->
          let (e, ety) = transexp !env ue pe in
            unify_or_fail !env ue pe.pl_loc ety retty;
            Some e
    in
      (!env, body, result, List.rev !prelude, List.rev !locals)

(* -------------------------------------------------------------------- *)
and fundef_add_symbol env symbols x =  (* for locals dup check *)
  if Sstr.mem x.pl_desc !symbols then
    tyerror x.pl_loc env (DuplicatedLocal x.pl_desc);
  symbols := Sstr.add x.pl_desc !symbols

and fundef_check_type subst_uni env (ty, loc) = 
  let ty = subst_uni ty in
    if not (EcUidgen.Suid.is_empty (Tuni.fv ty)) then
      tyerror loc env OnlyMonoTypeAllowed;
    ty

and fundef_check_decl subst_uni env (decl, loc) =
  { decl with
      v_type = fundef_check_type subst_uni env (decl.v_type, loc) }

and fundef_check_iasgn subst_uni env (pl, init, loc) =
  let pl =
    List.map
      (fun (p, ty) ->
        (p, fundef_check_type subst_uni env (ty, loc)))
      pl
  in
  let pl =
    match pl with
    | [xty] -> LvVar xty
    | xtys  -> LvTuple xtys
  in

  let clsubst = { EcTypes.e_subst_id with es_ty = subst_uni } in

    i_asgn (pl, e_subst clsubst init)

(* -------------------------------------------------------------------- *)
and transstmt ue (env : EcEnv.env) (stmt : pstmt) : stmt =
  EcModules.stmt (List.map (transinstr ue env) stmt)

(* -------------------------------------------------------------------- *)
and transinstr ue (env : EcEnv.env) (i : pinstr) =
  let transcall name args =
    let fpath, fdef = lookup_fun env name in
      if List.length args <> List.length fdef.f_sig.fs_params then
        tyerror name.pl_loc env (InvalidFunAppl FAE_WrongArgCount);
  
      let args =
        List.map2
          (fun a {v_type = ty} ->
            let a, aty = transexp env ue a in
              EcUnify.unify env ue aty ty; a)
          args fdef.f_sig.fs_params
      in
        (fpath, args, fdef.f_sig.fs_ret)
  in

  match i with
  | PSasgn (lvalue, rvalue) -> 
      let lvalue, lty = translvalue ue env lvalue in
      let rvalue, rty = transexp env ue rvalue in
      EcUnify.unify env ue lty rty;
      i_asgn (lvalue, rvalue)

  | PSrnd(lvalue, rvalue) -> 
      let lvalue, lty = translvalue ue env lvalue in
      let rvalue, rty = transexp env ue rvalue in
      EcUnify.unify env ue (tdistr lty) rty;
      i_rnd(lvalue, rvalue)

  | PScall (None, name, args) ->
      let (fpath, args, rty) = transcall name args in
      EcUnify.unify env ue tunit rty;
      i_call (None, fpath, args)

  | PScall (Some lvalue, name, args) ->
      let lvalue, lty = translvalue ue env lvalue in
      let (fpath, args, rty) = transcall name args in
      EcUnify.unify env ue lty rty;
      i_call (Some lvalue, fpath, args)

  | PSif (e, s1, s2) ->
      let e, ety = transexp env ue e in
      let s1 = transstmt ue env s1 in
      let s2 = transstmt ue env s2 in
  
        EcUnify.unify env ue ety tbool;
        i_if (e, s1, s2)

  | PSwhile (e, body) ->
      let e, ety = transexp env ue e in
      let body = transstmt ue env body in

        EcUnify.unify env ue ety tbool;
        i_while (e, body)

  | PSassert e ->
     let e, ety = transexp env ue e in 
       EcUnify.unify env ue ety tbool;
       i_assert e

(* -------------------------------------------------------------------- *)
and trans_pv env { pl_desc = x; pl_loc = loc } = 
  match EcEnv.Var.lookup_progvar_opt x env with
  | None -> tyerror loc env (UnknownModVar x)
  | Some(pv,xty) -> pv, xty 

and translvalue ue (env : EcEnv.env) lvalue =
  match lvalue.pl_desc with
  | PLvSymbol x ->
      let pty = trans_pv env x in
      LvVar pty, snd pty

  | PLvTuple xs -> 
      let xs = List.map (trans_pv env) xs in
      let ty = ttuple (List.map snd xs) in
      (LvTuple xs, ty)

  | PLvMap (x, tvi, e) ->
      let tvi = omap tvi (transtvi env ue) in
      let codomty = UE.fresh_uid ue in
      let pv,xty = trans_pv env x in
      let e, ety = transexp env ue e in
      let name =  ([],EcCoreLib.s_set) in
      let esig = [xty; ety; codomty] in
      let ops = select_op env name ue tvi esig in

      match ops with
      | [] ->
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror x.pl_loc env (UnknownVarOrOp (name, esig))

      | _ :: _ :: _ ->
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror x.pl_loc env (MultipleOpMatch (name, esig))

      | [({e_node = Eop (p, tys) }, _, subue)] ->
          EcUnify.UniEnv.restore ~src:subue ~dst:ue;
          (LvMap ((p, tys), pv, e, codomty), codomty)

      | [_] ->                          (* FIXME: dubious *)
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror x.pl_loc env (UnknownVarOrOp (name, esig))




(*let transmod (env : EcEnv.env) (x : symbol) (me : pmodule_expr) =
  let me = transmod env x me in
  begin match me.me_body with
  | ME_Alias mp -> check_mod_app_disjoint env mp
  | ME_Structure ms ->
    let rec check_item env = function
      | MI_Module me ->
        begin match me.me_body with
        | ME_Alias mp -> 
          check_mod_app_disjoint env mp;
        | ME_Structure ms ->
          check_struct env me.me_name ms 
        | ME_Decl _ -> assert false
        end;
        EcEnv.bind1 (me.me_name, `Module me)
      | MI_Variable v -> 
        EcEnv.bind1 (v.v_name, `Variable(PVglob,v.v_type)) env
      | MI_Function f ->
        EcEnv.bind1 (f.f_name,`Function f) env
    and check_struct env x ms =
      
    
  | _ -> ()
  end;
  me
*)


(* -------------------------------------------------------------------- *)
let process_msymb (env : EcEnv.env) (msymb : pmsymbol located) =
  let (top, args, sm) = 
    try
      let (r, (x, args), sm) =
        List.find_split (fun (_,args) -> args <> None) msymb.pl_desc
      in
        List.rev_append r [x,None], args, sm 
    with Not_found ->
      msymb.pl_desc, None, []
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
  let (top, args, sm) = process_msymb env msymb in

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
    match top_path with
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

    | `Abstract _m ->
        if (params <> []) || spi <> 0 then
          assert false;
        (mod_expr.me_sig.mis_params, true)
  in

  let args = omap args (List.map (trans_msymbol env)) in

  match args with
  | None ->
      let mp = EcPath.mpath top_path [] in
      let mt = mod_expr.me_types in
        (mp, mod_expr.me_sig.mis_params, mt)

  | Some args ->
      if List.length params <> List.length args then
        tyerror loc env (InvalidModAppl MAE_WrongArgCount);
      List.iter2
        (fun (_, p) (_, _, a) ->
          if not (EcEnv.ModTy.has_mod_type env a p) then
            tyerror loc env (InvalidModAppl MAE_InvalidArgType))
        params args;

      let args = List.map proj3_1 args in

      let subst = 
        List.fold_left2
          (fun s (x,_) a -> EcSubst.add_module s x a) 
          EcSubst.empty params args
      in

      let mp = EcPath.mpath top_path args in
      let mt =
        match istop with
        | false ->
            List.map (EcSubst.subst_modtype subst) mod_expr.me_types
        | true  ->
            List.map
              (fun mt ->
                { mt_name   = mt.mt_name;
                  mt_params = [];
                  mt_args   = List.map (EcSubst.subst_mpath subst) mt.mt_args;
                })
              mod_expr.me_types
              
      in
        (mp, [], mt)

(* -------------------------------------------------------------------- *)
 
and trans_gamepath (env : EcEnv.env) gp =
  let loc = gp.pl_loc in
  
  let modsymb = List.map (unloc -| fst) (fst (unloc gp))
  and funsymb = unloc (snd (unloc gp)) in
  
  let _ =
    match EcEnv.Fun.sp_lookup_opt (modsymb, funsymb) env with
    | None -> tyerror gp.pl_loc env (UnknownFunName (modsymb, funsymb))
    | Some _ -> ()
  in

  let (mpath, args, _) =
    trans_msymbol env (mk_loc loc (fst (unloc gp)))
  in
    if args <> [] then
      tyerror gp.pl_loc env (UnknownFunName (modsymb, funsymb));
    EcPath.xpath mpath (EcPath.psymbol funsymb)

(* -------------------------------------------------------------------- *)
let transfpattern env ue (p : EcParsetree.plpattern) =
  match transpattern1 env ue p with
  | LSymbol (x,ty) as p, _ ->
      (EcEnv.Var.bind_local x ty env, p, ty)
  | LTuple xs as p, ty ->
      (EcEnv.Var.bind_locals xs env, p , ty)

(* -------------------------------------------------------------------- *)
let transmem env m =
  match EcEnv.Memory.lookup 0 (unloc m) env with
  | None ->
      tyerror m.pl_loc env (UnknownMemName (0, unloc m))
      
  | Some me -> 
      if (EcMemory.memtype me) <> None then
        tyerror m.pl_loc env (InvalidMem (unloc m, MAE_IsConcrete));
      (fst me)

(* -------------------------------------------------------------------- *)
let trans_topmsymbol env gp = 
  let (mp,_,_) = trans_msymbol env gp in
  let top = 
    match mp.EcPath.m_top with
    | `Concrete(p,_) -> `Concrete(p,None)
    | t -> t in
  let mp = EcPath.mpath top mp.EcPath.m_args in
  mp 

let transform_opt env ue pf tt =
  let rec transf env f = 
    match f.pl_desc with
    | PFglob gp ->
      let mp = trans_topmsymbol env gp in
      let me =  
        match EcEnv.Memory.current env with
        | None -> assert false (* FIXME error message *)
        | Some me -> EcMemory.memory me in
      f_glob mp me
      
    | PFint n ->
        f_int n

    | PFtuple args ->
        f_tuple (List.map (transf env) args)

    | PFident ({ pl_desc = name;pl_loc = loc }, tvi) -> 
        let tvi = omap tvi (transtvi env ue) in
        let ops = select_sided_op env name ue tvi [] in
        begin match ops with
        | [] ->
            tyerror loc env (UnknownVarOrOp (name, []))

        | _ :: _ :: _ ->
            tyerror loc env (MultipleOpMatch (name, []))

        | [op, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            op
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

    | PFapp ({pl_desc = PFident({ pl_desc = name; pl_loc = loc }, tvi)}, es) ->
        let tvi  = omap tvi (transtvi env ue) in  
        let es   = List.map (transf env) es in
        let esig = List.map EcFol.f_ty es in 
        let ops  = select_sided_op env name ue tvi esig in
          begin match ops with
          | [] ->
              let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
                tyerror loc env (UnknownVarOrOp (name, esig))

          | _ :: _ :: _ ->
              let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
                tyerror loc env (MultipleOpMatch (name, esig))
  
          | [op, subue] ->
              EcUnify.UniEnv.restore ~src:subue ~dst:ue;
              let codom = ty_fun_app env ue op.f_ty esig in
                f_app op es codom
          end

    | PFapp (e, es) ->
        let es   = List.map (transf env) es in
        let esig = List.map EcFol.f_ty es in 
        let op  = transf env e in
        let codom = ty_fun_app env ue op.f_ty esig in
        f_app op es codom

    | PFif (pf1, pf2, pf3) ->
        let f1 = transf env pf1 in
        unify_or_fail env ue pf1.pl_loc f1.f_ty tbool;
        let f2 = transf env pf2 in
        let f3 = transf env pf3 in
        unify_or_fail env ue pf2.pl_loc f2.f_ty f3.f_ty;
        f_if f1 f2 f3

    | PFlet (lp, pf1, f2) ->
        let (penv, p, pty) = transfpattern env ue lp in
        let f1 = transf env pf1 in
        unify_or_fail env ue pf1.pl_loc f1.f_ty pty;
        let f2 = transf penv f2 in
        f_let p f1 f2 

    | PFforall (xs, pf) ->
        let env, xs = trans_fbind env ue xs in
        let f = transf env pf in
        unify_or_fail env ue pf.pl_loc f.f_ty tbool;
        f_forall xs f

    | PFexists (xs, f1) ->
        let env, xs = trans_fbind env ue xs in
        let f = transf env f1 in
        unify_or_fail env ue pf.pl_loc f.f_ty tbool;
        f_exists xs f

    | PFlambda (xs, f1) ->
        let env, xs = transbinding env ue xs in
        let f = transf env f1 in
        f_lambda (List.map (fun (x,ty) -> (x,GTty ty)) xs) f

    | PFprob (gp, args, m, event) ->
        let fpath = trans_gamepath env gp in
        let fun_  = EcEnv.Fun.by_xpath fpath env in
        let fsig  = fun_.f_sig.fs_params, fun_.f_sig.fs_ret in
        if List.length args <> List.length (fst fsig) then
          tyerror f.pl_loc env (InvalidFunAppl FAE_WrongArgCount);
        let args =
          let doit1 arg {v_type = aty} =
            let aout = transf env arg in
              unify_or_fail env ue arg.pl_loc aout.f_ty aty;
              aout
          in
            List.map2 doit1 args (fst fsig)
        in
        let memid = transmem env m in
        let event = transf (EcEnv.Fun.prF fpath env) event in
        f_pr memid fpath args event

    | PFhoareF (pre, gp, post) ->
        let fpath = trans_gamepath env gp in
        let penv, qenv = EcEnv.Fun.hoareF fpath env in
        let pre  = transf penv pre
        and post = transf qenv post
        in
        f_hoareF pre fpath post

    | PFhoareS (pre, body, post) ->
        let symbols = ref Mstr.empty in
        let ue      = UE.create (Some []) in

        let (env, stmt, _re, prelude, locals) =
          let env = EcEnv.Fun.enter "$stmt" env in
            transbody ue symbols env tunit body (* FIXME: $stmt ? *)
        in

        let su      = Tuni.subst (UE.close ue) in
        let locals  = List.map (fundef_check_decl  su env) locals in
        let prelude = List.map (fundef_check_iasgn su env) prelude in
        let clsubst = { EcTypes.e_subst_id with es_ty = su } in
        let stmt    = s_subst clsubst stmt in

        let (menv, env) = EcEnv.Fun.hoareS_anonym locals env in
        let pre  = transf env pre in
        let post = transf env post in
        f_hoareS menv pre (EcModules.stmt (prelude @ stmt.s_node)) post

    | PFequivF (pre, (gp1, gp2), post) ->
        let fpath1 = trans_gamepath env gp1 in
        let fpath2 = trans_gamepath env gp2 in
        let penv, qenv = EcEnv.Fun.equivF fpath1 fpath2 env in
        let pre = transf penv pre in
        let post = transf qenv post in
        f_equivF pre fpath1 fpath2 post

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
          let restr = 
            List.fold_left (fun r m -> 
              EcPath.Sm.add (trans_topmsymbol env m) r) EcPath.Sm.empty restr in

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

  and select_sided_op env ((qs, x) as name) ue tvi psig =
    let locals =
      if   qs = []
      then EcEnv.Var.lookup_local_opt x env
      else None
    in
      match locals with
      | Some (id, ty) ->
        if tvi <> None then assert false; (* FIXME : error message *)
        [ (f_local id ty, ue) ]

      | None -> 
        begin
        let ops = EcUnify.select_op true tvi env name ue psig in
        let prepare_op ((op, tys), ty, ue) = (f_op op tys ty, ue) in
        let ops = List.map prepare_op ops in
        match EcEnv.Memory.get_active env with
        | None -> ops 
        | Some me ->
          let pvs = select_pv env (Some me) name ue tvi psig in
          let prepare_pv (pv, ty, ue) = f_pvar pv ty me, ue in
          (List.map prepare_pv pvs) @ ops 
        end
  in

  let f = transf env pf in
  oiter tt (unify_or_fail env ue pf.pl_loc f.f_ty); 
  f
  
(* -------------------------------------------------------------------- *)
let transform env ue pf ty =
  transform_opt env ue pf (Some ty)

(* -------------------------------------------------------------------- *)
let transformula env ue pf = 
  transform env ue pf tbool
