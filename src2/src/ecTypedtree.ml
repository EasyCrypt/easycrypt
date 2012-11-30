(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcParsetree
open EcTypes
open EcTypesexpr
open EcTypesmod

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

exception TyError of tyerror

let tyerror x = raise (TyError x)

(* -------------------------------------------------------------------- *)
type typolicy =
  | TyDecl  of symbol list
  | TyAnnot of EcUidgen.uidmap

let transty (env : EcEnv.env) (policy : typolicy) =
  let rec transty ty =
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
        | None -> tyerror (UnknownTypeName name)
        | Some (p, tydecl) ->
          if tydecl.tyd_params <> 0 then
            tyerror (InvalidNumberOfTypeArgs (name, tydecl.tyd_params, 0));
          Tconstr (p, Parray.empty)
    end

    | PTapp (name, tyargs) -> begin
      match EcEnv.Ty.trylookup name env with
        | None -> tyerror (UnknownTypeName name)
        | Some (p, tydecl) ->
          let nargs = List.length tyargs in
            if nargs <> tydecl.tyd_params then
              tyerror (InvalidNumberOfTypeArgs (name, tydecl.tyd_params, nargs));
            let tyargs = Parray.fmap transty tyargs in
              Tconstr (p, tyargs)
    end

    | PTvar a -> begin
      match policy with
        | TyDecl tyvars -> begin
          match List.index a tyvars with
            | None   -> tyerror (UnboundTypeParameter a)
            | Some i -> Trel (a, i)
        end

        | TyAnnot uidmap -> Tvar (a, (EcUidgen.forsym uidmap a))
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

let transpattern (env : EcEnv.env) (p : EcParsetree.lpattern) =
  match p with
  | LPSymbol x ->
      let ty = mkunivar () in
      let x  = EcIdent.create x in
        (EcEnv.Var.bind x ty env, LSymbol x, ty)

  | LPTuple xs ->
      if not (List.uniq xs) then
        raise (NonLinearPattern p);

      let xs     = List.map EcIdent.create xs in
      let subtys = List.map (fun _ -> mkunivar ()) xs in

        (EcEnv.Var.bindall (List.combine xs subtys) env,
         LTuple xs,
         Ttuple (Parray.of_list subtys))

(* -------------------------------------------------------------------- *)
let transexp (env : EcEnv.env) (policy : epolicy) (e : pexpr) =
  let uidmap = ref EcUidgen.Muid.empty in

  let unify env ty1 ty2 =
    try  uidmap := (EcUnify.unify env !uidmap ty1 ty2); true
    with EcUnify.UnificationFailure _ -> false
  in

  let rec transexp (env : EcEnv.env) (policy : epolicy) (e : pexpr) =
    match e.pl_desc with
    | PEunit   -> (Eunit  , tunit ())
    | PEbool b -> (Ebool b, tbool ())
    | PEint  i -> (Eint  i, tint  ())

    | PEident x -> begin
      match EcEnv.Ident.trylookup x env with
      | None -> tyerror (UnknownVariable x)
      | Some (xpath, ty, kind) ->
        let e =
          match kind with
          | `Var  -> Evar (xpath, ty)
          | `Ctnt -> Eapp (xpath, [])
        in
          (e, ty)               (* FIXME: no need to freshen type ? *)
    end

    | PEapp (name, es) -> begin
      let es   = List.map (transexp env policy) es in
      let esig = snd (List.split es) in
        match EcEnv.Op.trylookup name env with
          | None -> tyerror (UnknownOperatorForSig (name, esig))
          | Some (p, op) ->
            let dom, codom =
              let optyvars =
                Parray.init op.op_params (fun _ -> mkunivar ())
              in
                (List.map (EcTypes.full_inst_rel optyvars) (fst op.op_sig),
                 EcTypes.full_inst_rel optyvars (snd op.op_sig))
            in
              if not (List.all2 (unify env) esig dom) then
                tyerror ApplInvalidArity; (* FIXME *)
              (Eapp (p, List.map fst es), codom)
    end

    | PElet (p, e1, e2) ->
      let (penv, p, pty) = transpattern env p in
      let e1, ty1 = transexp  env policy e1 in
      let e2, ty2 = transexp penv policy e2 in

        if not (unify env pty ty1) then
            tyerror (UnexpectedType (pty, ty1));
        (Elet (p, e1, e2), ty2)

    | PEtuple es ->
      let es, tys =
        Parray.split (Parray.fmap (transexp env policy) es)
      in
        (Etuple (Parray.to_list es), Ttuple tys)

    | PEif (c, e1, e2) ->
      let c, tyc = transexp env policy c in
        if not (unify env tyc (tbool ())) then
          tyerror (UnexpectedType (tyc, (tbool ())));
        let e1, ty1 = transexp env policy e1 in
        let e2, ty2 = transexp env policy e2 in
          if not (unify env ty1 ty2) then
            tyerror (UnexpectedType (ty1, ty2));
          (Eif (c, e1, e2), ty1)

    | PErnd re ->
      if not policy.epl_prob then
        tyerror ProbaExpressionForbidden;
      let re, ty = transrexp env policy re in
        (Ernd re, ty)

  and transrexp (env : EcEnv.env) (policy : epolicy) (e : prexpr) =
    match e.pl_desc with
    | PRbool -> (Rbool, tbool ())

    | PRbitstr e ->
        let e, ety = transexp env policy e in
          if not (unify env ety (tint ())) then
            tyerror (UnexpectedType (ety, (tint ())));
          (Rbitstr e, tbitstring ())

    | PRexcepted (re, e) ->
        let re, rety = transrexp env policy re in
        let  e,  ety = transexp  env policy  e in
          if not (unify env ety (tlist rety)) then
            tyerror (UnexpectedType (ety, (tlist rety)));
          (Rexcepted (re, e), rety)

    | PRinter (re1, re2) ->
        let re1, rty1 = transexp env policy re1 in
        let re2, rty2 = transexp env policy re2 in
          if not (unify env rty1 rty2) then
            tyerror (UnexpectedType (rty1, rty2));
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
        tyerror DuplicatedLocals;

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
            tyerror ModApplToNonFunctor

        | Tym_functor (iargs, tyres) ->
          let (anames, atymods) = List.split iargs in

            (* Check module application *)
            if List.length iargs <> List.length args then
              tyerror ModApplInvalidArity;
            List.iter2
              (fun iarg arg ->
                 if not (tymod_included arg iarg) then
                   tyerror ModApplInvalidArgInterface)
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

  | Pst_fun (decl, body) ->
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
          tyerror (DuplicatedLocals);

        (* Create general unification map to be used for the whole
         * typing process.
         *)
        let uidmap = ref (EcUidgen.Muid.empty) in

        (* Create idents and type univars for locals, unifying these
         * last with the translation of user provided annotations.
         *)
        let locals =
          List.map
            (fun (x, ty, e) ->
              let x    = EcIdent.create x in
              let ty   = transty env (TyDecl []) ty in
              let tvar = mkunivar () in
                uidmap := EcUnify.unify env !uidmap tvar ty;
                (x, tvar, e))
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
                    let e, ety = transexp env epolicy e in
                      uidmap := EcUnify.unify env !uidmap ty ety; e)
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

        let _body = transstmt uidmap newenv body.pfb_body in
          assert false                  (* FIXME *)

(* -------------------------------------------------------------------- *)
and transstmt uidmap (env : EcEnv.env) (stmt : pstmt) =
  List.map (transinstr uidmap env) stmt

(* -------------------------------------------------------------------- *)
and transinstr uidmap (env : EcEnv.env) (i : pinstr) =
  match i with
  | PSasgn (lvalue, rvalue) -> begin
      let lvalue, lty = translvalue uidmap env lvalue in
      let stmt, ety =
        match rvalue with
        | `Expr e ->
            let (e, ety) = transexp env epolicy e in (* FIXME: policy *)
              (Sasgn (lvalue, e), ety)
        | _ -> assert false
      in
        uidmap := EcUnify.unify env !uidmap lty ety;
        stmt
  end

  | PScall (name, args) ->
    let fpath, fsig =
      try  EcEnv.Fun.lookup name env
      with EcEnv.LookupFailure -> tyerror (UnknownFunction name)
    in
      if List.length args <> List.length (fst fsig.fs_sig) then
        tyerror ApplInvalidArity;

      let args =
        List.map2
          (fun a (_, ty) ->
            let a, aty = transexp env epolicy a in
              uidmap := EcUnify.unify env !uidmap aty ty; a)
          args (fst fsig.fs_sig)
      in
        uidmap := EcUnify.unify env !uidmap (snd fsig.fs_sig) (tunit ());
        Scall (None, fpath, args)

  | PSif (e, s1, s2) ->
      let e, ety = transexp env epolicy e in
      let s1 = transstmt uidmap env s1 in
      let s2 = transstmt uidmap env s2 in
  
        uidmap := EcUnify.unify env !uidmap ety (tbool ());
        Sif (e, s1, s2)

  | PSwhile (e, body) ->
      let e, ety = transexp env epolicy e in
      let body = transstmt uidmap env body in

        uidmap := EcUnify.unify env !uidmap ety (tbool ());
        Swhile (e, body)

  | PSassert e ->
     let e, ety = transexp env epolicy e in

       uidmap := EcUnify.unify env !uidmap ety (tbool ());
       Sassert e

(* -------------------------------------------------------------------- *)
and translvalue uidmap (env : EcEnv.env) lvalue =
  match lvalue with
  | PLvSymbol x ->
      let xpath, xty =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure -> tyerror (UnknownVariable x)
      in
        (LvVar (xpath, xty), xty)

  | PLvTuple xs -> begin
      let trans1 x =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure -> tyerror (UnknownVariable x)
      in
    
      let xs = Parray.fmap trans1 xs in
      let ty = Ttuple (Parray.map snd xs) in

        (LvTuple xs, ty)
  end

  | PLvMap (x, e) ->
      let codomty = mkunivar () in
      let xpath, xty =
        try  EcEnv.Var.lookup x env
        with EcEnv.LookupFailure -> tyerror (UnknownVariable x)
      and e, ety = transexp env epolicy e in

        uidmap := EcUnify.unify env !uidmap xty (tmap ety codomty);
        (LvMap (xpath, e, codomty), codomty)
