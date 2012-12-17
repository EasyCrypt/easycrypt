(* -------------------------------------------------------------------- *)
open EcUtils
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
  | DuplicatedLocals
  | ProbaExpressionForbidden
  | PatternForbiden
  | ModApplToNonFunctor
  | ModApplInvalidArity
  | ModApplInvalidArgInterface
  | PropExpected of pformula
  | TermExpected of pformula

exception TyError of Location.t * tyerror

let tyerror loc x = raise (TyError (loc, x))

(* -------------------------------------------------------------------- *)
let select_op ~proba env name ue psig =
  let ops = EcEnv.Op.all name env in
  let ops = List.filter (fun (_, op) -> op.op_prob || not proba) ops in
  let ops = List.filter (fun (_, op) -> not (op_ctnt op)) ops in
  let select (path, op) =
    if op_pr op then None 
    else
      let subue  = EcUnify.UniEnv.copy ue in
      let dom,codom = EcTypes.freshensig op.op_params (op_sig op) in
      let opsig = Ttuple dom in
      try
        EcUnify.unify env subue opsig (Ttuple psig);
        Some (path, op, codom, subue)
      with EcUnify.UnificationFailure _ -> None in
  List.pmap select ops

let select_pred env name ue psig =
  let ops = EcEnv.Op.all name env in
  let ops = List.filter (fun (_, op) -> not op.op_prob) ops in
  let ops = List.filter (fun (_, op) -> not (op_ctnt op)) ops in
  let select (path, op) =
    let subue  = EcUnify.UniEnv.copy ue in
    let dom = EcTypes.freshendom op.op_params (op_dom op) in
    let opsig = Ttuple dom in
    try
      EcUnify.unify env subue opsig (Ttuple psig);
      Some (path, op, op.op_codom, subue)
    with EcUnify.UnificationFailure _ -> None in
  List.pmap select ops

(* -------------------------------------------------------------------- *)
module TyPolicy = struct
  module Mstr = EcMaps.StringMap
      
  type t = {
      typ_decl   : EcIdent.t list; (* in reverse order *)
      typ_map    : EcIdent.t Mstr.t;
      typ_strict : bool (* true -> no new types variables *)
    }

  let empty = {
    typ_decl = [];
    typ_map = Mstr.empty;
    typ_strict = false
  }
   
  let decl tp = List.rev tp.typ_decl

  let relax tp = { tp with typ_strict = false }

  let strict tp = { tp with typ_strict = true } 

  let notv = strict empty 

  let get loc s tp = 
    try Mstr.find s tp.typ_map, tp
    with _ ->
      if tp.typ_strict then tyerror loc (UnboundTypeParameter s);
      let id = EcIdent.create s in
      let tp = { tp with 
                 typ_decl = id :: tp.typ_decl;
                 typ_map = Mstr.add s id tp.typ_map } in
      id, tp

  let init l = 
    let add tp s = 
      if Mstr.mem s tp.typ_map then assert false (* FIXME *)
      else 
        let id = EcIdent.create s in
        let tp = { tp with 
                   typ_decl = id :: tp.typ_decl;
                   typ_map = Mstr.add s id tp.typ_map } in
        tp in
    strict (List.fold_left add empty l)

  let init = function
    | None -> empty 
    | Some l -> init l

end

(* -------------------------------------------------------------------- *)
let rec transty (env : EcEnv.env) tv ty =
  match ty.pl_desc with
  | PTunivar -> EcTypes.mkunivar (), tv

  | PTvar s ->
      let v, tv = TyPolicy.get ty.pl_loc s.pl_desc tv in
        Tvar v, tv

  | PTtuple tys   -> 
      let tys, tv = transtys env tv tys in 
        Ttuple tys, tv

  | PTnamed { pl_desc = name } -> 
      begin match EcEnv.Ty.trylookup name env with
      | None -> tyerror ty.pl_loc (UnknownTypeName name)
      | Some (p, tydecl) ->
          if tydecl.tyd_params <> [] then
            tyerror ty.pl_loc
              (InvalidNumberOfTypeArgs (name, List.length tydecl.tyd_params, 0));
          Tconstr (p, []), tv 
      end

  | PTapp ({ pl_desc = name }, tyargs) -> 
      begin match EcEnv.Ty.trylookup name env with
      | None -> tyerror ty.pl_loc (UnknownTypeName name)
      | Some (p, tydecl) ->
          let nargs = List.length tyargs in
          let expected = List.length tydecl.tyd_params in
          if nargs <> expected then
            tyerror ty.pl_loc (InvalidNumberOfTypeArgs (name, expected, nargs));
          let tyargs, tv = transtys env tv tyargs in 
          Tconstr (p, tyargs), tv
      end

and transtys (env : EcEnv.env) tv tys = 
  let rtys, tv = 
    List.fold_left (fun (r, tv) ty -> 
      let ty, tv = transty env tv ty in ty::r, tv) ([], tv) tys
  in
    List.rev rtys, tv

(* -------------------------------------------------------------------- *)
let transty_notv env ty =
  fst (transty env TyPolicy.notv ty)

(* -------------------------------------------------------------------- *)
type epolicy = {
  epl_prob : bool;
}

let epolicy = { epl_prob = false; }

(* -------------------------------------------------------------------- *)
exception NonLinearPattern of EcParsetree.lpattern

let transpattern1 (env : EcEnv.env) (p : EcParsetree.lpattern) = 
  match p with
  | LPSymbol { pl_desc = x } ->
      let ty = mkunivar () in
      let x  = EcIdent.create x in
        (LSymbol x, ty)

  | LPTuple xs ->
      let xs = unlocs xs in
        if not (List.uniq xs) then
          raise (NonLinearPattern p)
        else
          let xs     = List.map EcIdent.create xs in
          let subtys = List.map (fun _ -> mkunivar ()) xs in
            (LTuple xs, Ttuple subtys)

let transpattern (env : EcEnv.env) (p : EcParsetree.lpattern) =
  match transpattern1 env p with
  | LSymbol x as p, ty ->
      EcEnv.Var.bind x ty env, p, ty
  | LTuple xs as p, (Ttuple lty as ty) ->
      EcEnv.Var.bindall (List.combine xs lty) env, p, ty
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let unify_error env ue loc ty1 ty2 = 
  try  EcUnify.unify env ue ty1 ty2 
  with EcUnify.UnificationFailure(t1,t2) ->
    let inst_uni = EcTypes.inst_uni (EcUnify.UniEnv.asmap ue) in
      tyerror loc (UnexpectedType (inst_uni ty1, inst_uni ty2, 
                                   inst_uni t1 , inst_uni t2 ))

let transexp (env : EcEnv.env) (policy : epolicy) (ue : EcUnify.unienv) e =

  let rec transexp (env : EcEnv.env) (policy : epolicy) (e : pexpr) =
    let loc = e.pl_loc in

    match e.pl_desc with
    | PEint  i -> (Eint  i, tint)

    | PEident { pl_desc = x } -> 
        begin match EcEnv.Ident.trylookup x env with
        | Some (xpath, Some ty, kind) -> 
            begin match kind with
            | `Var     -> (Evar (xpath, ty), ty)
            | `Ctnt op -> 
                let ty = EcTypes.freshen op.op_params ty in
                (Eapp (xpath, [], ty), ty)
            end
        | _ -> tyerror loc (UnknownVariable x)
        end

    | PEapp ({ pl_desc = name }, es) -> begin
      let es   = List.map (transexp env policy) es in
      let esig = snd (List.split es) in
      let ops  = select_op false env name ue esig in

        match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            let esig = inst_uni_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror loc (UnknownOperatorForSig (name, esig))

        | [(xpath, op, codom, subue)] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            (Eapp (xpath, List.map fst es, codom), codom)
    end

    | PElet (p, pe1, pe2) ->
      let (penv, p, pty) = transpattern env p in
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

    | PEflip -> (Eflip, tbool)

    | PEbitstr pe ->
        let e, ety = transexp env policy pe in
          unify_error env ue pe.pl_loc ety tint;
          (Ebitstr e, tbitstring)

    | PEexcepted (re, pe) ->
        let re, rety = transexp env policy re in
        let  e,  ety = transexp env policy pe in
          unify_error env ue pe.pl_loc ety (tlist rety);
          (Eexcepted (re, e), rety)

    | PEinter (pe1, pe2) ->
        let e1, ty1 = transexp env policy pe1 in
        let e2, ty2 = transexp env policy pe2 in
        unify_error env ue pe1.pl_loc ty1 tint;
        unify_error env ue pe2.pl_loc ty2 tint;
        (Einter (e1, e2), tint)

  in
    transexp env policy e               (* FIXME: close type *)

let transexpcast (env : EcEnv.env) (policy : epolicy) (ue : EcUnify.unienv) t e =
  let e',t' = transexp env policy ue e in
  try EcUnify.unify env ue t' t; e'
  with EcUnify.UnificationFailure(t1,t2) ->
    tyerror e.pl_loc (UnexpectedType (t',t, t1, t2))
  
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
        let type_ = transty_notv env x.pvd_type in
          Tys_variable (name, type_)

    | `FunctionDecl f ->
        let name   = f.pfd_name in
        let tyargs =
          List.map                      (* FIXME: continuation *)
            (fun (x, ty) -> (EcIdent.create x.pl_desc, transty_notv env ty))
            f.pfd_tyargs
        in
        let resty  = transty_notv env f.pfd_tyresult in
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
        tyerror dloc DuplicatedLocals;

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
let tymod_included (src : tymod) (dst : tymod) =
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
              EcSubst.ModType.apply
                (EcSubst.create
                   (List.map2
                      (fun aname arg -> `Module (aname, fst arg))
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
      | `Variable v -> (x, `Variable v.v_type)
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
      let ty,_ = transty env TyPolicy.notv ty in
        List.map
          (fun { pl_desc = x } ->
            let x = EcIdent.create x in
              (x, `Variable { v_name = x; v_type = ty; }))
          xs

  | Pst_fun (decl, body) -> begin
      (* Collect all local variables (arguments + locals) *)
      let locals =                      (* enforce arguments first *)
            (List.map (fun (x, ty) -> (x, ty, None)) decl.pfd_tyargs)
          @ (List.flatten
               (List.map
                  (fun (xs, ty, e) ->
                    List.map (fun x -> (x, ty, e)) xs)
                  body.pfb_locals))
      in
        (* Unicity check for names *)
        if not (List.uniq (List.map proj3_1 locals)) then
          tyerror dloc (DuplicatedLocals);

        (* Create general unification map to be used for the whole
         * typing process.
         *)
        let ue = EcUnify.UniEnv.create () in

        (* Create idents and type univars for locals, unifying these
         * last with the translation of user provided annotations.
         *)
        let locals =
          List.map
            (fun ({ pl_desc = x }, ty, e) ->
              let x    = EcIdent.create x in
              let ty, _  = transty env TyPolicy.notv ty in
              let tvar = mkunivar () in
                EcUnify.unify env ue tvar ty; (x, tvar, e))
            locals
        in

        (* Check variable assignments (expressions), unify their types
         * with variables related types.
         *)
        let locals =
          List.map
            (fun (x, ty, er) ->
              let er =
                omap er
                  (fun e ->
                    let e, ety = transexp env epolicy ue e in
                      EcUnify.unify env ue ty ety; e)
              in
                (x, ty, er))
            locals
        in

        (* Translate function body. *)
        let newenv =
          EcEnv.bindall
            (List.map (fun (x, ty, _) -> (x, `Variable ty)) locals)
            env
        in

        let _stmt = transstmt ue newenv body.pfb_body in (* FIXME: to be used *)

        let re, rty =
          match body.pfb_return with
          | None    -> (None, tunit)
          | Some re ->
              let re, ty = transexp newenv epolicy ue re in
                (Some re, ty)
        in
          (* FIXME: unify result type *)

        let fun_ = {
          f_sig = {
            fs_name = decl.pfd_name.pl_desc;
            fs_sig  = (List.map
                         (fun (x, ty, _) -> (x, ty))
                         (List.take (List.length decl.pfd_tyargs) locals),
                       rty);
            fs_uses = [];                 (* FIXME *)
          };

          f_locals = [];                (* FIXME *)
          f_body   = ();
        }

        in
          [(EcIdent.create decl.pfd_name.pl_desc, `Function fun_)]
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
            let a, aty = transexp env epolicy ue a in
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
        let e, ty = transexp env epolicy ue rvalue in
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
      let e, ety = transexp env epolicy ue e in
      let s1 = transstmt ue env s1 in
      let s2 = transstmt ue env s2 in
  
        EcUnify.unify env ue ety tbool;
        Sif (e, s1, s2)

  | PSwhile (e, body) ->
      let e, ety = transexp env epolicy ue e in
      let body = transstmt ue env body in

        EcUnify.unify env ue ety tbool;
        Swhile (e, body)

  | PSassert e ->
     let e, ety = transexp env epolicy ue e in

       EcUnify.unify env ue ety tbool;
       Sassert e

(* -------------------------------------------------------------------- *)
and translvalue ue (env : EcEnv.env) lvalue =
  match lvalue with
  | PLvSymbol { pl_desc = x } ->
      let xpath, xty =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure _ -> tyerror dloc (UnknownVariable x)
      in
        (LvVar (xpath, xty), xty)

  | PLvTuple xs -> begin
      let trans1 { pl_desc = x } =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure _ -> tyerror dloc (UnknownVariable x)
      in
    
      let xs = List.map trans1 xs in
      let ty = Ttuple (List.map snd xs) in

      (LvTuple xs, ty)
  end

  | PLvMap ({ pl_desc = x; pl_loc = loc }, e) ->
      let codomty = mkunivar () in
      let xpath, xty =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure _ -> tyerror dloc (UnknownVariable x)
      and e, ety = transexp env epolicy ue e in
      let name =  ([],"set") in
      let esig = [xty; ety; codomty] in
      let ops = select_op false env name ue esig in
      match ops with
      | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
          let esig = inst_uni_dom (EcUnify.UniEnv.asmap ue) esig in
          tyerror loc (UnknownOperatorForSig (name, esig))
      | [(opath, _, codom, subue)] ->
          EcUnify.UniEnv.restore ~src:subue ~dst:ue;
          (LvMap (opath, xpath, e, codomty), codomty)            

(* -------------------------------------------------------------------- *)
(** Translation of formula *)

open EcFol

type var_kind = 
  | Llocal of EcIdent.t * ty
  | Lprog  of EcPath.path * ty * Side.t
  | Lctnt  of EcPath.path * ty option

type op_kind = 
  | Lop of EcPath.path * operator
(*    | Lpred of EcPath.path * *)

module Fenv = struct

  type fenv = {
      fe_locals : (EcIdent.t * ty) EcIdent.Map.t; 
      fe_envs : EcEnv.env EcMaps.IntMap.t;
      fe_cur : int
    }

  let mono_fenv env = {
    fe_locals = EcIdent.Map.empty;
    fe_envs = EcMaps.IntMap.add 0 env EcMaps.IntMap.empty;
    fe_cur = 0;
  }

  let mono fenv = 
    try EcMaps.IntMap.find 0 fenv.fe_envs
    with _ -> assert false 

  let bind_local fenv x ty =
   { fenv with 
     fe_locals = EcIdent.Map.add x (x,ty) fenv.fe_locals }

  let bind_locals = List.fold_left2 bind_local 

  let current_env fenv = 
    try EcMaps.IntMap.find fenv.fe_cur fenv.fe_envs 
    with _ -> assert false (* FIXME *)

  let set_side fenv side = 
    if EcMaps.IntMap.mem side fenv.fe_envs then
      { fenv with fe_cur = side }
    else assert false (* FIXME *)

 
  module Ident = struct
    let trylookup_env fenv qs = 
      let env = current_env fenv in
      match EcEnv.Ident.trylookup qs env with
      | None -> None
      | Some (xpath, Some ty, `Var    ) -> Some (Lprog (xpath, ty, fenv.fe_cur))
      | Some (xpath, None, `Var    ) -> assert false 
      | Some (xpath, ty, `Ctnt op) -> 
          Some (Lctnt (xpath, omap ty (EcTypes.freshen op.op_params)))

    let trylookup_logical fenv s =
      match EcIdent.Map.byname s fenv.fe_locals with
      | None -> None
      | Some (x, ty) -> Some (Llocal (x, snd ty))
      
    let trylookup fenv (ls,s as qs) = 
      if ls = [] then
        match trylookup_logical fenv s with
        | Some _ as r -> r
        | None -> trylookup_env fenv qs
      else trylookup_env fenv qs
    
  end  

  module Op = struct
    let trylookup_op fenv qs = 
      match EcEnv.Op.trylookup qs (mono fenv) with
      | None -> None
      | Some(p,op) -> 
          if op.op_prob then None
          else Some(Lop(p,op))

    let trylookup fenv qs = 
      trylookup_op fenv qs 
    
  end
    

end
      
let transl fenv tp decl = 
  let transl1 (fenv,ld,tp) ({ pl_desc = x },pty) =
    let ty,tp = transty (Fenv.mono fenv) tp pty in
    let x = EcIdent.create x in
    Fenv.bind_local fenv x ty, (x,ty)::ld, tp in
  let transl fenv decl = List.fold_left transl1 (fenv,[],tp) decl in
  let fenv, ld, tp = transl fenv decl in
  fenv, List.rev ld, tp

let transfpattern fenv (p : EcParsetree.lpattern) =
  match transpattern1 (Fenv.mono fenv) p with
  | LSymbol x, ty ->
      (Fenv.bind_local fenv x ty, LSymbol x, ty)
  | LTuple xs, (Ttuple lty as ty) ->
      (Fenv.bind_locals fenv xs lty, LTuple xs, ty)
  | _ -> assert false


let transformula fenv tp ue pf = 

  let rec transf fenv tp f = 
    match f.pl_desc with
    | PFint n -> f_int n
    | PFtuple args -> f_tuple (List.map (transf fenv tp) args)
    | PFident { pl_desc = x } -> 
        begin match Fenv.Ident.trylookup fenv x with
        | None ->  tyerror dloc (UnknownVariable x)
        | Some(Llocal(x,ty)) -> f_local x ty
        | Some(Lprog(x,ty,s)) -> f_pvar x ty s
        | Some(Lctnt(x,oty)) -> f_app x [] oty
        end
    | PFside(f,side) ->
        let fenv = Fenv.set_side fenv side in
        transf fenv tp f
    | PFapp({ pl_desc = qs; pl_loc = loc }, es) ->
        let es   = List.map (transf fenv tp) es in
        let esig = List.map EcFol.ty es in 
        let ops  = select_pred (Fenv.mono fenv) qs ue esig in
        begin match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            tyerror loc (UnknownOperatorForSig (qs, esig))
        | [(xpath, op, oty, subue)] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            f_app xpath es oty
        end
    | PFif(pf1,f2,f3) ->
        let f1 = transf fenv tp pf1 in
        unify_error (Fenv.mono fenv) ue pf1.pl_loc f1.f_ty tbool;
        let f2 = transf fenv tp f2 in
        let f3 = transf fenv tp f3 in
        f_if f1 f2 f3
    | PFlet(lp,pf1,f2) ->
        let (penv, p, pty) = transfpattern fenv lp in
        let f1 = transf fenv tp pf1 in
        unify_error (Fenv.mono fenv) ue pf1.pl_loc f1.f_ty pty;
        let f2 = transf penv tp f2 in
        f_let p f1 f2 
    | PFforall(xs, pf) ->
        let fenv, xs, tp = transl fenv tp xs in
        let f = transf fenv tp pf in
        unify_error (Fenv.mono fenv) ue pf.pl_loc f.f_ty tbool;
        f_forall xs f
    | PFexists(xs, f1) ->
        let fenv, xs, tp = transl fenv tp xs in
        let f = transf fenv tp pf in
        unify_error (Fenv.mono fenv) ue pf.pl_loc f.f_ty tbool;
        f_exists xs f in
  let f = transf fenv tp pf in
  unify_error (Fenv.mono fenv) ue pf.pl_loc f.f_ty tbool;
  EcFol.Subst.uni (EcUnify.UniEnv.asmap ue) f, ue


