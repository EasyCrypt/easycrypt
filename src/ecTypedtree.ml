(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcParsetree
open EcTypes
open EcDecl
open EcTypesmod

(* -------------------------------------------------------------------- *)
let dloc = Location.dummy               (* FIXME: TO BE REMOVED *)

(* -------------------------------------------------------------------- *)
type tyerror =
  | UnknownVariable          of qsymbol
  | UnknownFunction          of qsymbol
  | UnknownTypeName          of qsymbol
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
module UE = EcUnify.UniEnv

let select_op proba env name ue psig =
  let ops = EcEnv.Op.all name env in
  let len = List.length psig in
  let select (path, op) = 
    if is_pred op || (is_prob op && not proba) then None
    else if List.length op.op_dom <> len then None
    else 
      let subue, (dom,codom) = UE.freshensig ue op.op_params (op_sig op) in
      try
        EcUnify.unify env subue (Ttuple dom) (Ttuple psig);
        Some (path, op, codom, subue)
      with EcUnify.UnificationFailure _ -> None in
  List.pmap select ops

let select_pred env name ue psig =
  let ops = EcEnv.Op.all name env in
  let len = List.length psig in
  let select (path, op) = 
    if is_prob op then None 
    else if List.length op.op_dom <> len then None
    else 
      let subue, (dom,codom) = UE.freshensig ue op.op_params (op_sig op) in
      try
        EcUnify.unify env subue (Ttuple dom) (Ttuple psig);
        Some (path, op, codom, subue)
      with EcUnify.UnificationFailure _ -> None in
  List.pmap select ops
 
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
type epolicy = {
  epl_prob : bool;
}

let ep_det = { epl_prob = false; }

let ep_prob = { epl_prob = true}

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

let transexp (env : EcEnv.env) (policy : epolicy) (ue : EcUnify.unienv) e =

  let rec transexp (env : EcEnv.env) (policy : epolicy) (e : pexpr) =
    let loc = e.pl_loc in

    match e.pl_desc with
    | PEint  i -> (Eint  i, tint)

    | PEident { pl_desc = x } -> 
        begin match EcEnv.Ident.trylookup ~prob:policy.epl_prob x env with
        | Some (ty, kind) -> 
            begin match kind with
            | `Pvar  x -> Evar(x,ty), ty
            | `Local x -> Elocal(x,ty), ty
            | `Ctnt(p, op) ->
                let newue, ty = UE.freshen ue op.op_params ty in
                UE.restore ue newue;
                (Eapp (p, [], ty), ty)
            end
        | _ -> tyerror loc (UnknownVariable x)
        end

    | PEapp ({ pl_desc = name }, es) -> begin
      let es   = List.map (transexp env policy) es in
      let esig = snd (List.split es) in
      let ops  = select_op policy.epl_prob env name ue esig in

        match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror loc (UnknownOperatorForSig (name, esig))

        | [(xpath, _, codom, subue)] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            (Eapp (xpath, List.map fst es, codom), codom)
    end

    | PElet (p, pe1, pe2) ->
      let (penv, p, pty) = transpattern env ue p in
      let e1, ty1 = transexp  env policy pe1 in
      let e2, ty2 = transexp penv policy pe2 in
      (* FIXME loc should be p *)
      unify_error env ue loc pty ty1;
      Elet (p, e1, e2), ty2

    | PEtuple es ->
        let tes = List.map (transexp env policy) es in
        let es, tys = List.split tes in
          Etuple es, Ttuple tys

    | PEif (pc, pe1, pe2) ->
      let c, tyc = transexp env policy pc in
      let e1, ty1 = transexp env policy pe1 in
      let e2, ty2 = transexp env policy pe2 in
        unify_error env ue pc.pl_loc tyc tbool;
        unify_error env ue pe2.pl_loc ty2 ty1;
        Eif (c, e1, e2), ty1

    | PEflip -> 
        if not policy.epl_prob then tyerror e.pl_loc RandomExprNotAllowed;
        (Eflip, tbool)


    | PEbitstr pe ->
        if not policy.epl_prob then tyerror e.pl_loc RandomExprNotAllowed;
        let e, ety = transexp env policy pe in
        unify_error env ue pe.pl_loc ety tint;
        (Ebitstr e, tbitstring)

    | PEexcepted (re, pe) ->
        if not policy.epl_prob then tyerror e.pl_loc RandomExprNotAllowed;
        let re, rety = transexp env policy re in
        let  e,  ety = transexp env policy pe in
        unify_error env ue pe.pl_loc ety (tlist rety);
        (Eexcepted (re, e), rety)

    | PEinter (pe1, pe2) ->
        if not policy.epl_prob then tyerror e.pl_loc RandomExprNotAllowed;
        let e1, ty1 = transexp env policy pe1 in
        let e2, ty2 = transexp env policy pe2 in
        unify_error env ue pe1.pl_loc ty1 tint;
        unify_error env ue pe2.pl_loc ty2 tint;
        (Einter (e1, e2), tint)

  in
    transexp env policy e

let transexpcast (env : EcEnv.env) (policy : epolicy) (ue : EcUnify.unienv) t e =
  let e',t' = transexp env policy ue e in
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
              fs_uses = []; }

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
        Tym_functor (args, transsig (EcEnv.ModTy.bindall args env) i)

  | Pty_sig i ->
      let i = transsig env i in
        Tym_sig i

(* -------------------------------------------------------------------- *)
let tymod_included (_src : tymod) (_dst : tymod) =
  false                                 (* FIXME *)

(* -------------------------------------------------------------------- *)
let rec transmod (env : EcEnv.env) (x : EcIdent.t) (m : pmodule_expr) =
  match m with
  | Pm_ident ({ pl_desc = m }, args) -> begin
      let m    = EcEnv.Mod.lookup m env in
      let args = List.map (EcEnv.Mod.lookup^~ env) (unlocs args) in

        match snd m with
        | Tym_sig _ ->
            tyerror dloc ModApplToNonFunctor

        | Tym_functor (iargs, tyres) ->
          let (anames, atymods) = List.split iargs in

            (* Check module application *)
            if List.length iargs <> List.length args then
              tyerror dloc ModApplInvalidArity;
            List.iter2
              (fun iarg arg ->
                 if not (tymod_included arg iarg) then
                   tyerror dloc ModApplInvalidArgInterface)
              atymods (List.map snd args);

            (* EcSubstitute args. in result type *)
            let tyres =
              EcSubst.subst_modtype
                (EcSubst.create
                   (List.map2
                      (fun aname arg -> (aname, `Path (fst arg)))
                      anames args))
                (Tym_sig tyres)
            in
              { me_name       = x;
                me_body       = ME_Application (fst m, List.map fst args);
                me_components = lazy (assert false); (* FIXME *)
                me_sig        = tyres; }
  end

  | Pm_struct st ->
      transstruct env x st

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
      | `Module   m -> (x, `Module   m.me_sig)
      | `Variable v -> (x, `Variable (Some EcTypes.PVglob, v.v_type))
      | `Function f -> (x, `Function f.f_sig)
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
      | `Module   _ -> None
      | `Variable v -> Some (Tys_variable (EcIdent.name v.v_name, v.v_type))
      | `Function f -> Some (Tys_function f.f_sig) 
    in

    let sigitems = List.pmap tymod1 (List.map snd items) in

      match List.isempty stparams with
      | true  -> Tym_sig sigitems
      | false -> Tym_functor (stparams, sigitems)
      
  in
    { me_name       = x;
      me_body       = ME_Structure { ms_params = stparams;
                                     ms_body   = List.map snd items; };
      me_components = lazy (assert false); (* FIXME *)
      me_sig        = tymod; }

(* -------------------------------------------------------------------- *)
and transstruct1 (env : EcEnv.env) (st : pstructure_item) =
  match st with
  | Pst_mod ({ pl_desc = m }, me) ->
      let m = EcIdent.create m in
        [(m, `Module (transmod env m me))]

  | Pst_var (xs, ty) ->
      let ty = transty_nothing env ty in
        List.map
          (fun { pl_desc = x } ->
            let x = EcIdent.create x in
              (x, `Variable { v_name = x; v_type = ty; }))
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
          let e, ety = transexp env ep_prob ue pe in
          unify_error env ue pe.pl_loc ety ty;
          List.iter (fun (id,_) ->
            let p,_ = EcEnv.Var.lookup ([],(EcIdent.name id)) newenv in
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
            let re, ty = transexp env ep_det ue pe in
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
        { f_sig = { fs_name = decl.pfd_name.pl_desc;
                    fs_sig  = params, rty;
                    fs_uses = [];   (* FIXME *)
                  };
          f_locals = locals;
          f_body   = stmt;
          f_ret    = re
        } in 
      [(fid, `Function fun_)]
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
            let a, aty = transexp env ep_prob ue a in
              EcUnify.unify env ue aty ty; a)
          args (fst fsig.fs_sig)
      in
        (fpath, args, snd fsig.fs_sig)
  in

  match i with
  | PSasgn (lvalue, rvalue) -> begin
      let rvalue_as_fun () =
        match rvalue.pl_desc with
        | PEapp ({ pl_desc = name }, args) when  EcEnv.Fun.exists name env ->
            let (fpath, args, rty) = transcall name args in
              Some (`Call (fpath, args), rty)
        | _ -> None

      and rvalue_as_expr () =
        let e, ty = transexp env ep_prob ue rvalue in
          Some (`Expr e, ty)
      in

      let lvalue, lty = translvalue ue env lvalue in
      let rvalue, rty = oget (List.fpick [rvalue_as_fun; rvalue_as_expr]) in

        EcUnify.unify env ue lty rty;
        match rvalue with
        | `Call (fpath, args) -> Scall (Some lvalue, fpath, args)
        | `Expr e -> Sasgn (lvalue, e)
    end

  | PScall ({ pl_desc = name }, args) ->
      let (fpath, args, rty) = transcall name args in
        EcUnify.unify env ue tunit rty;
        Scall (None, fpath, args)

  | PSif (e, s1, s2) ->
      let e, ety = transexp env ep_det ue e in
      let s1 = transstmt ue env s1 in
      let s2 = transstmt ue env s2 in
  
        EcUnify.unify env ue ety tbool;
        Sif (e, s1, s2)

  | PSwhile (e, body) ->
      let e, ety = transexp env ep_det ue e in
      let body = transstmt ue env body in

        EcUnify.unify env ue ety tbool;
        Swhile (e, body)

  | PSassert e ->
     let e, ety = transexp env ep_det ue e in 
     (* FIXME : ep_det or ep_prob, ask Cesar *)

       EcUnify.unify env ue ety tbool;
       Sassert e

(* -------------------------------------------------------------------- *)
and translvalue ue (env : EcEnv.env) lvalue =
  match lvalue with
  | PLvSymbol { pl_desc = x } ->
      let xpath, { EcEnv.vb_type = xty } =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure _ -> tyerror dloc (UnknownVariable x)
      in
        (LvVar (xpath, xty), xty)

  | PLvTuple xs -> begin
      let trans1 { pl_desc = x } =
        try
          let (xpath, { EcEnv.vb_type = xty}) = EcEnv.Var.lookup x env in
            (xpath, xty)
        with EcEnv.LookupFailure _ -> tyerror dloc (UnknownVariable x)
      in
    
      let xs = List.map trans1 xs in
      let ty = Ttuple (List.map snd xs) in

      (LvTuple xs, ty)
  end

  | PLvMap ({ pl_desc = x; pl_loc = loc }, e) ->
      let codomty = UE.fresh_uid ue in
      let xpath, { EcEnv.vb_type = xty } =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure _ -> tyerror dloc (UnknownVariable x)
      and e, ety = transexp env ep_det ue e in
      let name =  ([],"set") in
      let esig = [xty; ety; codomty] in
      let ops = select_op false env name ue esig in
      match ops with
      | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
          tyerror loc (UnknownOperatorForSig (name, esig))
      | [(opath, _, _, subue)] ->
          EcUnify.UniEnv.restore ~src:subue ~dst:ue;
          (LvMap (opath, xpath, e, codomty), codomty)            

(* -------------------------------------------------------------------- *)
(** Translation of formula *)

open EcFol

type var_kind = 
  | Llocal of EcIdent.t * ty
  | Lprog  of EcTypes.prog_var * ty * Side.t
  | Lctnt  of EcPath.path * ty 

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

  module Ident = struct
    let trylookup_env fenv ue qs = 
      let env = current_env fenv in
      match EcEnv.Ident.trylookup ~pred:true qs env with 
      | None -> None
      | Some(_, `Local _) -> assert false
      | Some(ty, `Pvar x) ->  Some (Lprog (x, ty, fenv.fe_cur))
      | Some (ty, `Ctnt(p, op)) ->
          let newue, ty = UE.freshen ue op.op_params ty in
          UE.restore ue newue;
          Some (Lctnt (p, ty))

    let trylookup_logical fenv s =
      match EcIdent.Map.byname s fenv.fe_locals with
      | None -> None
      | Some (x, ty) -> Some (Llocal (x, snd ty))
      
    let trylookup fenv ue (ls,s as qs) = 
      if ls = [] then
        match trylookup_logical fenv s with
        | Some _ as r -> r
        | None -> trylookup_env fenv ue qs
      else trylookup_env fenv ue qs
    
  end  

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

let transformula fenv ue pf = 
  let rec transf fenv f = 
    match f.pl_desc with
    | PFint n -> f_int n
    | PFtuple args -> f_tuple (List.map (transf fenv) args)
    | PFident { pl_desc = x } -> 
        begin match Fenv.Ident.trylookup fenv ue x with
        | None ->  tyerror dloc (UnknownVariable x)
        | Some(Llocal(x,ty)) -> f_local x ty
        | Some(Lprog(x,ty,s)) -> f_pvar x ty s
        | Some(Lctnt(x,ty)) -> f_app x [] ty
        end
    | PFside(f,side) ->
        let fenv = Fenv.set_side fenv side in
        transf fenv f
    | PFapp({ pl_desc = qs; pl_loc = loc }, es) ->
        let es   = List.map (transf fenv) es in
        let esig = List.map EcFol.ty es in 
        let ops  = select_pred (Fenv.mono fenv) qs ue esig in
        begin match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            tyerror loc (UnknownOperatorForSig (qs, esig))
        | [(xpath, _, oty, subue)] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            f_app xpath es oty
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
  unify_error (Fenv.mono fenv) ue pf.pl_loc f.f_ty tbool;
  f 

