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
| LvNonLinear
| NonUnitFunWithoutReturn
| UnitFunWithReturn
| TypeMismatch         of (ty * ty) * (ty * ty)
| TypeModMismatch      of tymod_cnv_failure
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
| FunNotInModParam     of qsymbol
| NoActiveMemory
| PatternNotAllowed
| UnknownScope         of qsymbol

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

  | LvNonLinear ->
      msg "This left-value is contains twice the same variable"

  | NonUnitFunWithoutReturn ->
      msg "This function must return a value"

  | UnitFunWithReturn ->
      msg "This void function cannot return a value"

  | TypeMismatch ((ty1, ty2), _) ->
      msg "This expression as type@\n";
      msg "  @[<hov 2> %a@]@\n" pp_type ty2;
      msg "but is expected to have type@\n";
      msg "  @[<hov 2> %a@]" pp_type ty1

  | TypeModMismatch err ->
      msg "this module body does not meet its interface:@\n";
      msg "  @[<hov 2>%t@]" (fun fmt -> pp_cnv_failure fmt env err)

  | UnknownVarOrOp (name, tys) -> begin
      match tys with
      | [] -> msg "unknown variable or constant: `%a'" pp_qsymbol name
      | _  -> msg "unknown operator `%a' for signature (%a)"
                pp_qsymbol name (EcPrinting.pp_list " *@ " pp_type) tys
      
  end

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

  | InvalidModAppl err ->
      msg "invalid module application:@ %a" pp_modappl_error err

  | InvalidModType MTE_FunSigDoesNotRepeatArgNames ->
      msg "applied argument names must repeat functor argument names"

  | InvalidMem (name, MAE_IsConcrete) ->
      msg "the memory %s must be abstract" name

  | FunNotInModParam name ->
      msg "the function %a is not provided by a module parameter"
        pp_qsymbol name

  | NoActiveMemory ->
      msg "no active memory at this point"

  | PatternNotAllowed ->
      msg "pattern not allowed here"

  | UnknownScope sc ->
      msg "unknown scope: `%a'" pp_qsymbol sc

let () =
  let pp fmt exn =
    match exn with
    | TyError (_, env, e) ->
        pp_tyerror fmt (EcPrinting.PPEnv.ofenv env) e
    | _ -> raise exn
  in
    EcPException.register pp

(* -------------------------------------------------------------------- *)
type ptnmap = ty EcIdent.Mid.t ref

(* -------------------------------------------------------------------- *)
module UE = EcUnify.UniEnv

let unify_or_fail (env : EcEnv.env) ue loc ~expct:ty1 ty2 = 
  try  EcUnify.unify env ue ty1 ty2 
  with EcUnify.UnificationFailure (t1, t2) ->
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
  if is_glob p then 
    { u with us_reads = Sx.add p.pv_name u.us_reads }
  else u 

let add_write (u : uses) p : uses =
  if is_glob p then
    { u with us_writes = Sx.add p.pv_name u.us_writes }
  else u

let (i_inuse, s_inuse, se_inuse) =
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

let gen_select_op ~actonly ~pred (fpv, fop, flc) opsc tvi env name ue psig =
  match (if tvi = None then select_local env name else None) with
  | Some (id, ty) ->
      [ flc (id, ty, ue) ]

  | None ->
      let ops = EcUnify.select_op pred tvi env name ue psig in
      let ops =
        match opsc with
        | None -> ops
        | Some opsc ->
            List.filter
              (fun ((p, _), _, _) ->
                  EcPath.isprefix opsc (oget (EcPath.prefix p)))
              ops
      in
      let me, pvs =
        match EcEnv.Memory.get_active env, actonly with
        | None, true -> (None, [])
        | me  , _    -> (  me, select_pv env me name ue tvi psig)
      in
        (List.map (fpv me) pvs) @ (List.map fop ops)

let select_exp_op env opsc name ue tvi psig =
  let ppv = (fun _ (pv, ty, ue) -> (e_var pv ty, ty, ue))
  and pop = (fun ((op, tys), ty, ue) -> (e_op op tys ty, ty, ue))
  and flc = (fun (id, ty, ue) -> (e_local id ty, ty, ue)) in
    gen_select_op ~actonly:false ~pred:false (ppv, pop, flc)
      opsc tvi env name ue psig 

let select_form_op env opsc name ue tvi psig =
  let ppv = (fun me (pv, ty, ue) -> (f_pvar pv ty (oget me), ue))
  and pop = (fun ((op, tys), ty, ue) -> (f_op op tys ty, ue))
  and flc = (fun (id, ty, ue) -> (f_local id ty, ue)) in
    gen_select_op ~actonly:true ~pred:true (ppv, pop, flc)
      opsc tvi env name ue psig 

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
  let rec transexp_r (osc : EcPath.path option) (env : EcEnv.env) (e : pexpr) =
    let loc = e.pl_loc in
    let transexp = transexp_r osc in

    match e.pl_desc with
    | PEint i -> (e_int i, tint)

    | PEident ({ pl_desc = name }, tvi) -> 
        let tvi = omap tvi (transtvi env ue) in
        let ops = select_exp_op env osc name ue tvi [] in
        begin match ops with
        | [] -> tyerror loc env (UnknownVarOrOp (name, []))

        | _ :: _ :: _ ->
            tyerror loc env (MultipleOpMatch (name, []))

        | [op, ty, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            op, ty
        end

    | PEscope (popsc, e) ->
        let opsc =
          match EcEnv.Theory.lookup_opt (unloc popsc) env with
          | None -> tyerror popsc.pl_loc env (UnknownScope (unloc popsc))
          | Some opsc -> fst opsc
        in
          transexp_r (Some opsc) env e

    | PEapp ({pl_desc = PEident({ pl_desc = name; pl_loc = loc }, tvi)}, es) ->
        let tvi  = omap tvi (transtvi env ue) in  
        let es   = List.map (transexp env) es in
        let esig = snd (List.split es) in
        let ops  = select_exp_op env osc name ue tvi esig in
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
  
        let e1, ty1 = transexp env pe1 in
          unify_or_fail env ue p.pl_loc ~expct:ty1 pty;
  
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
    transexp_r None env e

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
  let transsig1 (`FunctionDecl f) =
    let name   = f.pfd_name in
    let tyargs =
      List.map                          (* FIXME: continuation *)
        (fun (x, ty) -> { v_name = x.pl_desc; 
                          v_type = transty_for_decl env ty})
        f.pfd_tyargs
    in
    let resty = transty_for_decl env f.pfd_tyresult in

    if not (List.uniq (List.map fst f.pfd_tyargs)) then
      raise (DuplicatedArgumentsName f);

    let (uin, calls) =
      match f.pfd_uses with
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
          (true, Sm.fold do_one sa [])

      | Some (uin, pfd_uses) ->
        uin, List.map (fun name -> 
          let f = fst (lookup_fun env name) in
          let p = f.EcPath.x_top in
          if not (Sm.mem p sa) then 
            tyerror name.pl_loc env (FunNotInModParam name.pl_desc);
          f
        )
          pfd_uses
    in

    let sig_ = { fs_name   = name.pl_desc;
                 fs_params = tyargs;
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

  let check_item_compatible =
    let check_fun_compatible (fin,oin) (fout,oout) =
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
          let norm oi = 
            List.fold_left (fun s f -> 
              EcPath.Sx.add (EcEnv.NormMp.norm_xpath env f) s)
              EcPath.Sx.empty oi.oi_calls in
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

  let args = omap args (List.map (trans_msymbol env)) in

  match args with
  | None ->
    if not istop && params <> [] then
      tyerror loc env (InvalidModAppl MAE_AccesSubModFunctor); 

    (top_path, mod_expr.me_sig)

  | Some args ->
    let top_path = top_path.EcPath.m_top in
      if List.length params <> List.length args then
        tyerror loc env (InvalidModAppl MAE_WrongArgCount);
    List.iter2
      (fun (_, p) (_, a) ->
        try check_sig_mt_cnv env a p
        with TymodCnvFailure _ ->
          tyerror loc env (InvalidModAppl MAE_InvalidArgType))
      params args;
    let args = List.map fst args in
    let subst = 
        List.fold_left2
          (fun s (x,_) a -> EcSubst.add_module s x a) 
          EcSubst.empty params args
    in
    let body = EcSubst.subst_modsig_body subst mod_expr.me_sig.mis_body in
    let body = 
      List.map 
        (fun (Tys_function(s,oi)) -> 
          Tys_function(s,{oi_calls = []; oi_in = oi.oi_in})) body in
    let mp = EcPath.mpath top_path args in
    (mp, {mis_params = []; mis_body = body})

(* -------------------------------------------------------------------- *)
let rec transmod (env : EcEnv.env) (x : symbol) (me : pmodule_expr) =
  match me.pl_desc with
  | Pm_ident m -> 
    let (mp, _sig) = trans_msymbol env {pl_desc = m; pl_loc = me.pl_loc} in
    let params = _sig.mis_params in
    if params <> [] then (* FIXME do it only for internal module *)
      tyerror me.pl_loc env (InvalidModAppl MAE_WrongArgCount);
    (* FIXME Normally this is the expected code: but 
       I think that by_mpath is buggy :
    
    let me = EcEnv.Mod.by_mpath mp env in
    { me with me_name  = x; me_body  = ME_Alias mp; } *)
    begin match mp.EcPath.m_top with
    | `Concrete(_, Some _) 
    | _ when mp.EcPath.m_args = [] ->
      let me = EcEnv.Mod.by_mpath mp env in
      { me with me_name  = x; me_body  = ME_Alias mp; }
    | _ -> 
      let mpf = EcPath.mpath mp.EcPath.m_top [] in
      let mef = EcEnv.Mod.by_mpath mpf env in
      let subst = 
        List.fold_left2
          (fun subst (x,_) arg -> EcSubst.add_module subst x arg)
          EcSubst.empty mef.me_sig.mis_params mp.EcPath.m_args
      in
      let res = 
      { me_name  = x;
        me_body  = ME_Alias mp;
        me_comps = EcSubst.subst_module_comps subst mef.me_comps;
        me_sig   = {
          mis_params = [];
          mis_body   = 
            let rm_oi = function 
              | Tys_function (fsig,oi) -> 
                Tys_function(fsig, {oi_calls = []; oi_in = oi.oi_in}) in
            let body = List.map rm_oi mef.me_sig.mis_body in
            EcSubst.subst_modsig_body subst body;
        };
      } in
      res
    end 

  | Pm_struct st -> transstruct env x st

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
   * structure arguments, and then with previously checked items. *)
  let env0 = EcEnv.Mod.enter x stparams env in
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
  let mroot = EcEnv.mroot envi in
  let top   = EcPath.m_functor mroot in

  let mparams = 
    List.fold_left (fun rm mp -> EcPath.Sm.add mp rm) 
      EcPath.Sm.empty mroot.EcPath.m_args in

  let rm = EcPath.Sm.add top mparams in

  (* Generate structure signature *)
  let tymod =
    let mparams = 
      List.fold_left (fun mparams (id,_) ->
        Sm.add (EcPath.mident id) mparams) Sm.empty stparams in 
    let tymod1 = function
      | MI_Module   _ -> None
      | MI_Variable _ -> None           (* Some (Tys_variable v)  *)
      | MI_Function f -> 
        let all_calls = 
          match f.f_def with
          | FBdef def ->
            let rec f_call c f =
              let f = EcEnv.NormMp.norm_xpath envi f in
              if EcPath.Sx.mem f c then c
              else 
                let c = EcPath.Sx.add f c in
                match (EcEnv.Fun.by_xpath f envi).f_def with
                | FBdef def -> List.fold_left f_call c def.f_uses.us_calls 
                | FBabs oi  -> List.fold_left f_call c oi.oi_calls in
            List.fold_left f_call EcPath.Sx.empty def.f_uses.us_calls 
          | FBabs _ -> assert false in
        let filter f = 
          let ftop = EcPath.m_functor f.EcPath.x_top in
          Sm.mem ftop mparams in
        let calls = List.filter filter (EcPath.Sx.elements all_calls) in
        Some (Tys_function (f.f_sig, {oi_calls  = calls; oi_in = true }))
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
    else (* In that case we check the applied signature *)
      let sig_ = 
        { mis_params = [];
          mis_body = List.map 
            (fun (Tys_function(s,oi)) -> 
              Tys_function (s, { oi_calls = []; oi_in = oi.oi_in }))
            tymod.mis_body } in
      try  check_sig_mt_cnv env0 sig_ aty
      with TymodCnvFailure err -> tyerror loc env0 (TypeModMismatch err)
  in
    List.iter check1 st.ps_signature;

  (* Computes used variables / calls *)
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
        let mp = EcEnv.mroot env0 in
        let xp  = EcPath.xpath mp (EcPath.psymbol x.v_name) in
        EcPath.Mx.add xp x.v_type vs
      | MI_Function _ -> vs) EcPath.Mx.empty items in

   let rec uses us items =
    List.fold_left (fun us item ->
      match item with
      | MI_Module me ->
        begin match me.me_body with
        | ME_Structure ms -> EcPath.Sm.union us ms.ms_uses 
        | ME_Alias     mp -> EcEnv.NormMp.add_uses envi rm us mp
        | ME_Decl      _  -> assert false
        end
      | MI_Variable _  -> us
      | MI_Function fd ->
        begin match fd.f_def with
        | FBdef fdef ->
          let fus = fdef.f_uses in
          let us = 
            List.fold_left (fun us fn ->
              EcEnv.NormMp.add_uses envi rm us fn.EcPath.x_top) 
              us fus.us_calls in
          EcPath.Sx.fold (fun xp us ->
            EcEnv.NormMp.add_uses envi rm us xp.EcPath.x_top)
            (EcPath.Sx.union fus.us_reads fus.us_writes) us
        | FBabs _ -> assert false
        end) us items in
  let uses = uses EcPath.Sm.empty items in

  (* Construct structure representation *)
  let me =
    { me_name  = x;
      me_body  = 
        ME_Structure 
          { ms_body = items; 
            ms_vars = vars; 
            ms_uses = uses };
      me_comps = items;
      me_sig   = tymod; }
  in
    me
  
(* -------------------------------------------------------------------- *)
and transstruct1 (env : EcEnv.env) (st : pstructure_item located) =
  match unloc st with
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
        transbody ue symbols !env retty (mk_loc st.pl_loc body)
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
      let stmt    = EcModules.stmt (List.flatten prelude @ stmt.s_node) in

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
    let init   = omap local.pfl_init (fst -| transexp !env ue) in
    let ty     = omap local.pfl_type (transty tp_uni !env ue) in

    let ty =
      match ty, init with
      | None   , None   -> assert false
      | Some ty, None   -> ty
      | None   , Some e -> e.e_ty
      | Some ty, Some e -> begin
          let loc =  (oget local.pfl_init).pl_loc in
            unify_or_fail !env ue loc ~expct:ty e.e_ty; ty
      end
    in

    let xsvars = List.map (fun _ -> UE.fresh_uid ue) xs in

    begin
      match mode with
      | `Single -> List.iter (fun a -> EcUnify.unify !env ue a ty) xsvars
      | `Tuple  -> unify_or_fail !env ue local.pfl_names.pl_loc ~expct:ty (ttuple xsvars)
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

    oiter init
      (fun init ->
        let iasgn = List.map (fun (_, v, xty, _) -> (v, xty)) mylocals in
          prelude := ((mode, iasgn), init, _dummy) :: !prelude)
  in

  List.iter add_local pbody.pfb_locals;

  let body   = transstmt ue !env pbody.pfb_body in
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
        let (e, ety) = transexp !env ue pe in
          try
            EcUnify.unify !env ue tunit retty;
            tyerror loc !env UnitFunWithReturn
          with EcUnify.UnificationFailure _ ->
            unify_or_fail !env ue pe.pl_loc ~expct:retty ety;
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
            let loc = a.pl_loc in
            let a, aty = transexp env ue a in
            unify_or_fail env ue loc ~expct:ty aty; a)
          args fdef.f_sig.fs_params
      in
        (fpath, args, fdef.f_sig.fs_ret)
  in

  match i.pl_desc with
  | PSasgn (plvalue, prvalue) -> 
      let lvalue, lty = translvalue ue env plvalue in
      let rvalue, rty = transexp env ue prvalue in
      unify_or_fail env ue prvalue.pl_loc ~expct:lty rty;
      i_asgn (lvalue, rvalue)

  | PSrnd (plvalue, prvalue) -> 
      let lvalue, lty = translvalue ue env plvalue in
      let rvalue, rty = transexp env ue prvalue in
      unify_or_fail env ue prvalue.pl_loc ~expct:(tdistr lty) rty;
      i_rnd (lvalue, rvalue)

  | PScall (None, name, args) ->
      let (fpath, args, rty) = transcall name (unloc args) in
      unify_or_fail env ue i.pl_loc ~expct:tunit rty;
      i_call (None, fpath, args)

  | PScall (Some lvalue, name, args) ->
      if EcEnv.Fun.lookup_opt (unloc name) env <> None then
        let lvalue, lty = translvalue ue env lvalue in
        let (fpath, args, rty) = transcall name (unloc args) in
        unify_or_fail env ue name.pl_loc ~expct:lty rty;
        i_call (Some lvalue, fpath, args)
      else
        let fe   = mk_loc name.pl_loc (PEident (name, None)) in
        let args = mk_loc args.pl_loc (PEtuple (unloc args)) in
        
        let ope =
          mk_loc (EcLocation.merge fe.pl_loc args.pl_loc) (PEapp (fe, [args]))
        in
        transinstr ue env (mk_loc i.pl_loc (PSasgn (lvalue, ope)))

  | PSif (pe, s1, s2) ->
      let e, ety = transexp env ue pe in
      let s1 = transstmt ue env s1 in
      let s2 = transstmt ue env s2 in
      unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
      i_if (e, s1, s2)

  | PSwhile (pe, pbody) ->
      let e, ety = transexp env ue pe in
      let body = transstmt ue env pbody in
      unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
      i_while (e, body)

  | PSassert pe ->
      let e, ety = transexp env ue pe in 
      unify_or_fail env ue pe.pl_loc ~expct:tbool ety;
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
      if not (List.uniqf (EcReduction.pv_equal_norm env) (List.map fst xs)) then
        tyerror lvalue.pl_loc env LvNonLinear;
      let ty = ttuple (List.map snd xs) in
      (LvTuple xs, ty)

  | PLvMap (x, tvi, e) ->
      let tvi = omap tvi (transtvi env ue) in
      let codomty = UE.fresh_uid ue in
      let pv,xty = trans_pv env x in
      let e, ety = transexp env ue e in
      let name =  ([],EcCoreLib.s_set) in
      let esig = [xty; ety; codomty] in
      let ops = select_exp_op env None name ue tvi esig in

      match ops with
      | [] ->
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror x.pl_loc env (UnknownVarOrOp (name, esig))

      | _ :: _ :: _ ->
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror x.pl_loc env (MultipleOpMatch (name, esig))

      | [({e_node = Eop (p, tys) }, _, subue)] ->
          EcUnify.UniEnv.restore ~src:subue ~dst:ue;
          (LvMap ((p, tys), pv, e, xty), codomty)

      | [_] ->                          (* FIXME: dubious *)
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror x.pl_loc env (UnknownVarOrOp (name, esig))

(* -------------------------------------------------------------------- *)
let trans_gamepath (env : EcEnv.env) gp =
  let loc = gp.pl_loc in
  
  let modsymb = List.map (unloc -| fst) (fst (unloc gp))
  and funsymb = unloc (snd (unloc gp)) in
  
  let _ =
    match EcEnv.Fun.sp_lookup_opt (modsymb, funsymb) env with
    | None -> tyerror gp.pl_loc env (UnknownFunName (modsymb, funsymb))
    | Some _ -> ()
  in

  let (mpath, _sig) = trans_msymbol env (mk_loc loc (fst (unloc gp))) in
  if _sig.mis_params <> [] then
    tyerror gp.pl_loc env (UnknownFunName (modsymb, funsymb));
  EcPath.xpath_fun mpath funsymb

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
        let ty = UE.fresh_uid ue in
          ps := Mid.add x ty !ps; f_local x ty
    end

    | PFscope (popsc, f) ->
        let opsc =
          match EcEnv.Theory.lookup_opt (unloc popsc) env with
          | None -> tyerror popsc.pl_loc env (UnknownScope (unloc popsc))
          | Some opsc -> fst opsc
        in
          transf_r (Some opsc) env f

    | PFglob gp ->
        let mp = trans_topmsymbol env gp in
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
        let tvi = omap tvi (transtvi env ue) in
        let ops = select_form_op env opsc name ue tvi [] in
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

    | PFeqveq xs ->
        let lookup me x =
          match EcEnv.Var.lookup_progvar_opt ~side:me (unloc x) env with
          | None -> tyerror x.pl_loc env (UnknownVarOrOp (unloc x, []))
          | Some (x, ty) -> f_pvar x ty me
        in
        let check_mem loc me = 
          match EcEnv.Memory.byid me env with
          | None -> tyerror loc env NoActiveMemory (* FIXME error message *)
          | Some _ -> () in
        let do1 = function
          | GVvar x ->
            let x1 = lookup EcFol.mleft x in
            let x2 = lookup EcFol.mright x in
            f_eq x1 x2
          | GVglob gp ->
            let mp = trans_topmsymbol env gp in
            check_mem gp.pl_loc EcFol.mleft;
            check_mem gp.pl_loc EcFol.mright;
            let x1 = f_glob mp EcFol.mleft in
            let x2 = f_glob mp EcFol.mright in
            f_eq x1 x2 in
        let eqs = List.map do1 xs in
        EcFol.f_ands eqs

    | PFapp ({pl_desc = PFident ({ pl_desc = name; pl_loc = loc }, tvi)}, es) ->
        let tvi  = omap tvi (transtvi env ue) in  
        let es   = List.map (transf env) es in
        let esig = List.map EcFol.f_ty es in 
        let ops  = select_form_op env opsc name ue tvi esig in
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
        let f2 = transf env pf2 in
        let f3 = transf env pf3 in
          unify_or_fail env ue pf1.pl_loc ~expct:tbool   f1.f_ty;
          unify_or_fail env ue pf3.pl_loc ~expct:f2.f_ty f3.f_ty;
          f_if f1 f2 f3

    | PFlet (lp, pf1, f2) ->
        let (penv, p, pty) = transfpattern env ue lp in
        let f1 = transf env pf1 in
        let f2 = transf penv f2 in
          unify_or_fail env ue lp.pl_loc ~expct:f1.f_ty pty;
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

    | PFprob (gp, args, m, event) ->
        let fpath = trans_gamepath env gp in
        let fun_  = EcEnv.Fun.by_xpath fpath env in
        let fsig  = fun_.f_sig.fs_params, fun_.f_sig.fs_ret in
        if List.length args <> List.length (fst fsig) then
          tyerror f.pl_loc env (InvalidFunAppl FAE_WrongArgCount);
        let args =
          let doit1 arg { v_type = aty } =
            let aout = transf env arg in
              unify_or_fail env ue arg.pl_loc ~expct:aty aout.f_ty;
              aout
          in
            List.map2 doit1 args (fst fsig)
        in
        let memid = transmem env m in
        let env = EcEnv.Fun.prF fpath env in
        let event' = transf env event in
          unify_or_fail env ue event.pl_loc ~expct:tbool event'.f_ty;
          f_pr memid fpath args event'

    | PFhoareF (pre, gp, post) ->
        let fpath = trans_gamepath env gp in
        let penv, qenv = EcEnv.Fun.hoareF fpath env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
          unify_or_fail penv ue pre.pl_loc  ~expct:tbool pre' .f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
          f_hoareF pre' fpath post'

    | PFhoareS (pre, body, post) ->
        let symbols = ref Mstr.empty in
        let ue = UE.create (Some []) in
        let (env, stmt, _re, prelude, locals) =
          let env = EcEnv.Fun.enter "$stmt" env in
            (* FIXME: $stmt ? *)
            transbody ue symbols env tunit body
        in
        let su      = Tuni.subst (UE.close ue) in
        let locals  = List.map (fundef_check_decl  su env) locals in
        let prelude = List.map (fundef_check_iasgn su env) prelude in
        let clsubst = { EcTypes.e_subst_id with es_ty = su } in
        let stmt    = s_subst clsubst stmt in
        let (menv, env) = EcEnv.Fun.hoareS_anonym locals env in
        let pre'  = transf env pre in
        let post' = transf env post in
        unify_or_fail env ue pre.pl_loc  ~expct:tbool pre' .f_ty;
        unify_or_fail env ue post.pl_loc ~expct:tbool post'.f_ty;
        f_hoareS menv pre' (EcModules.stmt (List.flatten prelude @ stmt.s_node)) post'

    | PFBDhoareF (pre, gp, post, hcmp, bd) ->
        let fpath = trans_gamepath env gp in
        let penv, qenv = EcEnv.Fun.hoareF fpath env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
        let bd'   = transf env bd in
        let hcmp  = match hcmp with PFHle -> FHle | PFHeq -> FHeq | PFHge -> FHge in
          (* FIXME: check that there are not pvars in bd *)
          unify_or_fail penv ue pre .pl_loc ~expct:tbool pre' .f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
          unify_or_fail env  ue bd  .pl_loc ~expct:treal bd'  .f_ty;
          f_bdHoareF pre' fpath post' hcmp bd'

    | PFlsless gp ->
        let fpath = trans_gamepath env gp in
          f_losslessF fpath

    | PFBDhoareS (pre, body, post, hcmp, bd) ->
        let symbols = ref Mstr.empty in
        let ue      = UE.create (Some []) in
        let hcmp = 
          match hcmp with PFHle -> FHle | PFHeq -> FHeq | PFHge -> FHge
        in
        let (env, stmt, _re, prelude, locals) =
          let env = EcEnv.Fun.enter "$stmt" env in
            (* FIXME: $stmt ? *)
            transbody ue symbols env tunit body
        in
        let su      = Tuni.subst (UE.close ue) in
        let locals  = List.map (fundef_check_decl  su env) locals in
        let prelude = List.map (fundef_check_iasgn su env) prelude in
        let clsubst = { EcTypes.e_subst_id with es_ty = su } in
        let stmt    = s_subst clsubst stmt in
        let (menv, env) = EcEnv.Fun.hoareS_anonym locals env in
        let pre'  = transf env pre in
        let post' = transf env post in
        let bd'   = transf env bd in
          (* FIXME: check that there are not pvars in bd *)
          unify_or_fail env ue pre .pl_loc ~expct:tbool pre' .f_ty;
          unify_or_fail env ue post.pl_loc ~expct:tbool post'.f_ty;
          unify_or_fail env ue bd  .pl_loc ~expct:treal bd'  .f_ty;
          f_bdHoareS menv pre' (EcModules.stmt (List.flatten prelude @ stmt.s_node)) post' hcmp bd'

    | PFequivF (pre, (gp1, gp2), post) ->
        let fpath1 = trans_gamepath env gp1 in
        let fpath2 = trans_gamepath env gp2 in
        let penv, qenv = EcEnv.Fun.equivF fpath1 fpath2 env in
        let pre'  = transf penv pre in
        let post' = transf qenv post in
          unify_or_fail penv ue pre .pl_loc ~expct:tbool pre' .f_ty;
          unify_or_fail qenv ue post.pl_loc ~expct:tbool post'.f_ty;
          f_equivF pre' fpath1 fpath2 post'

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
          let restr = EcPath.Sm.of_list (List.map (trans_topmsymbol env) restr) in
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
    oiter tt (unify_or_fail env ue pf.pl_loc ~expct:f.f_ty); f

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
