(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcParsetree
open EcTypes
open EcTypesexpr
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
  | UnexpectedType           of ty * ty
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
  let ops = List.filter (fun (_, op) -> not op.op_ctnt) ops in
  let select (path, op) =
    let subue  = EcUnify.UniEnv.copy ue in
    let tyvars = Parray.init op.op_params (fun _ -> mkunivar ()) in
    let dom    = List.map (EcTypes.full_inst_rel tyvars) (fst op.op_sig)
    and codom  = EcTypes.full_inst_rel tyvars (snd op.op_sig) in

    let opsig = Ttuple (Parray.of_list dom) in
      try
        EcUnify.unify env subue opsig (Ttuple (Parray.of_list psig));
        Some (path, op, codom, subue)
      with
      | EcUnify.UnificationFailure _ -> None

  in
    List.pmap select ops

(* -------------------------------------------------------------------- *)
type typolicy =
  | TyDecl  of symbol list
  | TyAnnot

let transty (env : EcEnv.env) (policy : typolicy) =
  let rec transty ty =
    let loc = ty.pl_loc in

    match ty.pl_desc with
      (* Base types *)
    | PTunit        -> Tbase Tunit
    | PTbool        -> Tbase Tbool
    | PTint         -> Tbase Tint
    | PTreal        -> Tbase Treal
    | PTbitstring   -> Tbase Tbitstring
    | PTunivar      -> EcTypes.mkunivar ()
    | PTtuple tys   -> Ttuple (Parray.fmap transty tys)

    | PTnamed name -> begin
      match EcEnv.Ty.trylookup name env with
        | None -> tyerror loc (UnknownTypeName name)
        | Some (p, tydecl) ->
          if tydecl.tyd_params <> 0 then
            tyerror loc (InvalidNumberOfTypeArgs (name, tydecl.tyd_params, 0));
          Tconstr (p, Parray.empty)
    end

    | PTapp (name, tyargs) -> begin
      match EcEnv.Ty.trylookup name env with
        | None -> tyerror loc (UnknownTypeName name)
        | Some (p, tydecl) ->
          let nargs = List.length tyargs in
            if nargs <> tydecl.tyd_params then
              tyerror loc (InvalidNumberOfTypeArgs (name, tydecl.tyd_params, nargs));
            let tyargs = Parray.fmap transty tyargs in
              Tconstr (p, tyargs)
    end

    | PTvar a -> begin
      match policy with
        | TyDecl tyvars -> begin
          match List.index a tyvars with
            | None   -> tyerror loc (UnboundTypeParameter a)
            | Some i -> Trel i
        end

        | TyAnnot ->
            invalid_arg "EcTypedtree.transty"
    end
  in
    fun ty -> transty ty

(* -------------------------------------------------------------------- *)
type epolicy = {
  epl_prob : bool;
}

let epolicy = { epl_prob = false; }

(* -------------------------------------------------------------------- *)
exception NonLinearPattern of EcParsetree.lpattern

let transpattern1 (env : EcEnv.env) (p : EcParsetree.lpattern) = 
  match p with
  | LPSymbol x ->
      let ty = mkunivar () in
      let x  = EcIdent.create x in
      (LSymbol x, ty)

  | LPTuple xs ->
      if not (List.uniq xs) then raise (NonLinearPattern p);
      let xs     = List.map EcIdent.create xs in
      let subtys = List.map (fun _ -> mkunivar ()) xs in
      (LTuple xs, Ttuple (Parray.of_list subtys))

let transpattern (env : EcEnv.env) (p : EcParsetree.lpattern) =
  match transpattern1 env p with
  | LSymbol x as p, ty ->
      (EcEnv.Var.bind x ty env, p, ty)
  | LTuple xs as p, (Ttuple lty as ty) ->
      (EcEnv.Var.bindall (List.combine xs (Parray.to_list lty)) env, p, ty)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let transexp (env : EcEnv.env) (policy : epolicy) (ue : EcUnify.unienv) e =
  let unify env ty1 ty2 =
    try  (EcUnify.unify env ue ty1 ty2); true
    with EcUnify.UnificationFailure _ -> false
  in

  let rec transexp (env : EcEnv.env) (policy : epolicy) (e : pexpr) =
    let loc = e.pl_loc in

    match e.pl_desc with
    | PEunit   -> (Eunit  , tunit ())
    | PEbool b -> (Ebool b, tbool ())
    | PEint  i -> (Eint  i, tint  ())

    | PEident x -> begin
      match EcEnv.Ident.trylookup x env with
      | None -> tyerror loc (UnknownVariable x)
      | Some (xpath, ty, kind) -> begin
          match kind with
          | `Var     -> (Evar (xpath, ty), ty)
          | `Ctnt op -> (Eapp (xpath, []), EcTypes.freshen op.op_params ty)
      end
    end

    | PEapp (name, es) -> begin
      let es   = List.map (transexp env policy) es in
      let esig = snd (List.split es) in
      let ops  = select_op false env name ue esig in

        match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            tyerror loc (UnknownOperatorForSig (name, esig))

        | [(xpath, op, codom, subue)] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            (Eapp (xpath, List.map fst es), codom)
    end

    | PElet (p, e1, e2) ->
      let (penv, p, pty) = transpattern env p in
      let e1, ty1 = transexp  env policy e1 in
      let e2, ty2 = transexp penv policy e2 in

        if not (unify env pty ty1) then
            tyerror loc (UnexpectedType (pty, ty1));
        (Elet (p, e1, e2), ty2)

    | PEtuple es ->
      let es, tys =
        Parray.split (Parray.fmap (transexp env policy) es)
      in
        (Etuple (Parray.to_list es), Ttuple tys)

    | PEif (c, e1, e2) ->
      let c, tyc = transexp env policy c in
        if not (unify env tyc (tbool ())) then
          tyerror loc (UnexpectedType (tyc, (tbool ())));
        let e1, ty1 = transexp env policy e1 in
        let e2, ty2 = transexp env policy e2 in
          if not (unify env ty1 ty2) then
            tyerror loc (UnexpectedType (ty1, ty2));
          (Eif (c, e1, e2), ty1)

    | PErnd re ->
      if not policy.epl_prob then
        tyerror loc ProbaExpressionForbidden;
      let re, ty = transrexp env policy re in
        (Ernd re, ty)

  and transrexp (env : EcEnv.env) (policy : epolicy) (e : prexpr) =
    let loc = e.pl_loc in

    match e.pl_desc with
    | PRbool -> (Rbool, tbool ())

    | PRbitstr e ->
        let e, ety = transexp env policy e in
          if not (unify env ety (tint ())) then
            tyerror loc (UnexpectedType (ety, (tint ())));
          (Rbitstr e, tbitstring ())

    | PRexcepted (re, e) ->
        let re, rety = transrexp env policy re in
        let  e,  ety = transexp  env policy  e in
          if not (unify env ety (tlist rety)) then
            tyerror loc (UnexpectedType (ety, (tlist rety)));
          (Rexcepted (re, e), rety)

    | PRinter (re1, re2) ->
        let re1, rty1 = transexp env policy re1 in
        let re2, rty2 = transexp env policy re2 in
          if not (unify env rty1 rty2) then
            tyerror loc (UnexpectedType (rty1, rty2));
          (Rinter (re1, re2), rty1)

    | PRapp (name, args) ->
        let _args, _asig =              (* FIXME *)
          List.split (List.map (transexp env epolicy) args)
        in
          assert false

  in
    transexp env policy e               (* FIXME: close type *)

(* -------------------------------------------------------------------- *)
exception DuplicatedSigItemName   of psignature
exception DuplicatedArgumentsName of pfunction_decl

let name_of_sigitem = function
  | `VariableDecl v -> v.pvd_name
  | `FunctionDecl f -> f.pfd_name

let rec transsig (env : EcEnv.env) (is : psignature) =
  let transsig1 = function
    | `VariableDecl x ->
        let name  = x.pvd_name in
        let type_ = transty env (TyDecl []) x.pvd_type in
          Tys_variable (name, type_)

    | `FunctionDecl f ->
        let name   = f.pfd_name in
        let tyargs =
          List.map                      (* FIXME: continuation *)
            (fun (x, ty) -> (EcIdent.create x, transty env (TyDecl []) ty))
            f.pfd_tyargs in
        let resty  = transty env (TyDecl []) f.pfd_tyresult in

          if not (List.uniq (List.map fst f.pfd_tyargs)) then
            raise (DuplicatedArgumentsName f);
          Tys_function
            { fs_name = name;
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
              (EcIdent.create x, snd (EcEnv.ModTy.lookup iname env)))
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
  | Pm_ident (m, args) -> begin
      let m    = EcEnv.Mod.lookup m env in
      let args = List.map (EcEnv.Mod.lookup^~ env) args in

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
      (fun (a, aty) -> (EcIdent.create a, snd (EcEnv.ModTy.lookup aty env)))
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
        (EcEnv.Mod.bindall stparams env, [])
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
  | Pst_mod (m, me) ->
      let m = EcIdent.create m in
        [(m, `Module (transmod env m me))]

  | Pst_var (xs, ty) ->
      let ty = transty env (TyDecl []) ty in
        List.map
          (fun x ->
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
            (fun (x, ty, e) ->
              let x    = EcIdent.create x in
              let ty   = transty env (TyDecl []) ty in
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
          | None    -> (None, tunit ())
          | Some re ->
              let re, ty = transexp newenv epolicy ue re in
                (Some re, ty)
        in
          (* FIXME: unify result type *)

        let fun_ = {
          f_sig = {
            fs_name = decl.pfd_name;
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
          [(EcIdent.create decl.pfd_name, `Function fun_)]
  end

  | Pst_alias _ -> assert false

(* -------------------------------------------------------------------- *)
and transstmt ue (env : EcEnv.env) (stmt : pstmt) =
  List.map (transinstr ue env) stmt

(* -------------------------------------------------------------------- *)
and transinstr ue (env : EcEnv.env) (i : pinstr) =
  match i with
  | PSasgn (lvalue, rvalue) -> begin
      let lvalue, lty = translvalue ue env lvalue in
      let stmt, ety =
        match rvalue with
        | `Expr e ->
            let (e, ety) = transexp env epolicy ue e in (* FIXME: policy *)
              (Sasgn (lvalue, e), ety)
        | _ -> assert false
      in
        EcUnify.unify env ue lty ety;
        stmt
  end

  | PScall (name, args) ->
    let fpath, fsig =
      try  EcEnv.Fun.lookup name env
      with EcEnv.LookupFailure -> tyerror dloc (UnknownFunction name)
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
        EcUnify.unify env ue (snd fsig.fs_sig) (tunit ());
        Scall (None, fpath, args)

  | PSif (e, s1, s2) ->
      let e, ety = transexp env epolicy ue e in
      let s1 = transstmt ue env s1 in
      let s2 = transstmt ue env s2 in
  
        EcUnify.unify env ue ety (tbool ());
        Sif (e, s1, s2)

  | PSwhile (e, body) ->
      let e, ety = transexp env epolicy ue e in
      let body = transstmt ue env body in

        EcUnify.unify env ue ety (tbool ());
        Swhile (e, body)

  | PSassert e ->
     let e, ety = transexp env epolicy ue e in

       EcUnify.unify env ue ety (tbool ());
       Sassert e

(* -------------------------------------------------------------------- *)
and translvalue ue (env : EcEnv.env) lvalue =
  match lvalue with
  | PLvSymbol x ->
      let xpath, xty =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure -> tyerror dloc (UnknownVariable x)
      in
        (LvVar (xpath, xty), xty)

  | PLvTuple xs -> begin
      let trans1 x =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure -> tyerror dloc (UnknownVariable x)
      in
    
      let xs = Parray.fmap trans1 xs in
      let ty = Ttuple (Parray.map snd xs) in

        (LvTuple xs, ty)
  end

  | PLvMap (x, e) ->
      let codomty = mkunivar () in
      let xpath, xty =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure -> tyerror dloc (UnknownVariable x)
      and e, ety = transexp env epolicy ue e in

        EcUnify.unify env ue xty (tmap ety codomty);
        (LvMap (xpath, e, codomty), codomty)

(* -------------------------------------------------------------------- *)
(** Translation of formula *)

open EcFol

type var_kind = 
  | Llocal of EcIdent.t * ty
  | Lprog  of EcPath.path * ty * Side.t
  | Lctnt  of EcPath.path * ty

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
      | Some (xpath, ty, `Var    ) -> Some (Lprog (xpath, ty, fenv.fe_cur))
      | Some (xpath, ty, `Ctnt op) -> Some (Lctnt (xpath, EcTypes.freshen op.op_params ty))

    let trylookup_logical fenv s =
      match EcIdent.Map.byname s fenv.fe_locals with
      | None -> None
      | Some(x,ty) -> Some(Llocal(x,ty))
      
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
      
let transbop = function
  | PPand -> Land
  | PPor -> Lor
  | PPimp -> Limp
  | PPiff -> Liff 

let transl fenv decl = 
  let transl1 (fenv,ld) (x,pty) =
    let ty = transty (Fenv.mono fenv) (TyDecl []) pty (* FIXME *) in
    let x = EcIdent.create x in
    Fenv.bind_local fenv x ty, (x,ty)::ld in
  let transl fenv decl = List.fold_left transl1 (fenv,[]) decl in
  let fenv, ld = transl fenv decl in
  fenv, List.rev ld

let transfpattern fenv (p : EcParsetree.lpattern) =
  match transpattern1 (Fenv.mono fenv) p with
  | LSymbol x, ty ->
      (Fenv.bind_local fenv x ty, LFPSymbol(x,ty), ty)
  | LTuple xs, (Ttuple lty as ty) ->
      let lty = Parray.to_list lty in 
      let pxs = List.map2 (fun x ty -> x,ty) xs lty in
      (Fenv.bind_locals fenv xs lty, LFPTuple pxs, ty)
  | _ -> assert false


let transformula fenv = 
  let ue = EcUnify.UniEnv.create () in

  let unify env ty1 ty2 =
    try  (EcUnify.unify (Fenv.mono env) ue ty1 ty2); true
    with EcUnify.UnificationFailure _ -> false
  in

  let fofbool fenv f ty = 
      if unify fenv ty (tbool ()) then fofbool f 
      else tyerror dloc (UnexpectedType (ty, tbool())) in

  let rec transf fenv f = 
    match f.pl_desc with
    | PFunit | PFint _ | PFtuple _ -> tyerror dloc (PropExpected f)
    | PFbool b -> EcFol.fofbool (fbool b) 
    | PFident x -> 
        begin match Fenv.Ident.trylookup fenv x with
        | None ->  tyerror dloc (UnknownVariable x)
        | Some(Llocal(x,ty)) -> fofbool fenv (flocal x ty) ty
        | Some(Lprog(x,ty,s)) -> fofbool fenv (fpvar x ty s) ty
        | Some(Lctnt(x,ty)) -> fofbool fenv (fapp x [] (Some ty)) ty
(*        | Some(Lpred(x)) -> fapp x [] None *)
        end
    | PFside(f,side) ->
        let fenv = Fenv.set_side fenv side in
        transf fenv f
    | PFnot f -> fnot (transf fenv f)
    | PFbinop(f1,op, f2) ->
        fbinop (transf fenv f1) (transbop op) (transf fenv f2)
    | PFapp(qs,es) ->
        let es   = List.map (transe fenv) es in
        let esig = snd (List.split es) in
        (* Ce code va pas il faut que les lookup depende de esig *)
        let ops  = select_op false (Fenv.mono fenv) qs ue esig in
        begin match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            tyerror f.pl_loc (UnknownOperatorForSig (qs, esig))
        | [(xpath, op, codom, subue)] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            fofbool fenv (fapp xpath (List.map fst es) (Some codom)) codom
        end
    | PFif(f1,f2,f3) ->
        let f1 = transf fenv f1 in
        let f2 = transf fenv f2 in
        let f3 = transf fenv f3 in
        fif f1 f2 f3
    | PFlet(lp,e1,f2) ->
        let (penv, p, pty) = transfpattern fenv lp in
        let e1, ty1 = transe fenv e1 in
        if not (unify fenv pty ty1) then
          tyerror dloc (UnexpectedType (pty, ty1));
        let f2 = transf penv f2 in
        flet p e1 f2 
    | PFforall(xs,f1) ->
        let fenv, xs = transl fenv xs in
        let f = transf fenv f1 in
        fforall xs f
    | PFexists(xs,f1) ->
        let fenv, xs = transl fenv xs in
        let f = transf fenv f1 in
        fexists xs f
  and transe fenv e =
    match e.pl_desc with
    | PFunit -> Funit  , tunit ()
    | PFint i -> Fint i, tint ()
    | PFtuple es -> 
        let ets = List.map (transe fenv) es in
        let es,ts = List.split ets in
        Ftuple es, Ttuple (Parray.of_list ts)
    | PFbool b -> fbool b, tbool()
    | PFident x -> 
        begin match Fenv.Ident.trylookup fenv x with
        | None ->  tyerror dloc (UnknownVariable x)
        | Some(Llocal(x,ty)) -> flocal x ty, ty
        | Some(Lprog(x,ty,s)) -> fpvar x ty s, ty
        | Some(Lctnt(x,ty)) -> fapp x [] (Some ty), ty (* FIXME *)
(*        | Some(Lpred(x)) -> fapp x [] None *)
        end
    | PFside(f,side) ->
        let fenv = Fenv.set_side fenv side in
        transe fenv f
    | PFnot f -> (* FIXME *)
        let e,ty = transe fenv f in
        let tbool = tbool () in
        if not (unify fenv ty tbool) then
          tyerror dloc (UnexpectedType (ty, tbool));
        let op = assert false in (*FIXME get the not on bool *)
        fapp op [e] (Some tbool), tbool
    | PFbinop(f1,op,f2) -> (* FIXME *)
        assert false 
    | PFapp(qs,es) ->
        let es   = List.map (transe fenv) es in
        let esig = snd (List.split es) in
        let ops  = select_op false (Fenv.mono fenv) qs ue esig in
        begin match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            tyerror e.pl_loc (UnknownOperatorForSig (qs, esig))
        | [(xpath, op, codom, subue)] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            fapp xpath (List.map fst es) (Some codom), codom
        end
    | PFif(f1,f2,f3) ->
        let f1 = transf fenv f1 in
        let f2,ty2 = transe fenv f2 in
        let f3,ty3 = transe fenv f3 in
        if not (unify fenv ty2 ty3) then
          tyerror e.pl_loc (UnexpectedType (ty2,ty3));
        fif f1 f2 f3, ty2
    | PFlet(lp,e1,f2) ->
        let (penv, p, pty) = transfpattern fenv lp in
        let e1, ty1 = transe fenv e1 in
        if not (unify fenv pty ty1) then
          tyerror e.pl_loc (UnexpectedType (pty, ty1));
        let e2, ty2 = transe penv f2 in
        flet p e1 e2, ty2 
    | PFforall _ | PFexists _ -> tyerror e.pl_loc (TermExpected e) in
  fun f ->
    let f = transf fenv f in
    EcFol.Subst.uni (EcUnify.UniEnv.asmap ue) f
