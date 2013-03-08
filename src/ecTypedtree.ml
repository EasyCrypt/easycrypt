(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
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

module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
let dloc = EcLocation.dummy               (* FIXME: TO BE REMOVED *)

(* -------------------------------------------------------------------- *)
type tyerror =
  | UnknownVariable          of qsymbol
  | UnknownFunction          of qsymbol
  | UnknownTypeName          of qsymbol
  | UnknownTyModName         of qsymbol
  | UnknownMemory            of symbol
  | AbstractMemoryWanted     of symbol
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

exception TyError of tyerror

module PE = EcPrinting.EcDebugPP (* FIXME *)

let pp_typerror fmt = function
    | UnknownVariable name
        -> Format.fprintf fmt "Unknown variable: %a" pp_qsymbol name
  
    | UnknownFunction name
        -> Format.fprintf fmt "Unknown function: %a" pp_qsymbol name
  
    | UnknownTypeName name
        -> Format.fprintf fmt "Unknown type name: %a" pp_qsymbol name

    | UnknownModName name
        -> Format.fprintf fmt "Unknown module name: %a" pp_qsymbol name
  
    | UnknownTyModName name
        -> Format.fprintf fmt "Unknown module type name: %a" pp_qsymbol name

    | UnknownMemory name
        -> Format.fprintf fmt "Unknown memory name: %a" pp_symbol name

    | AbstractMemoryWanted name
        -> Format.fprintf fmt "This memory should be abstract: %a" pp_symbol name

    | UnknownOperatorForSig (name, tys)
        -> Format.fprintf fmt "Cannot find operator %a with signature %a" 
            pp_qsymbol name
            PE.pp_dom tys
  
    | InvalidNumberOfTypeArgs (name, n, i)
        -> Format.fprintf fmt 
            "The type %a is applied to %i paramaters while %i is excepted"
            pp_qsymbol name i n
  
    | ApplInvalidArity
        -> Format.fprintf fmt "Wrong number of arguments"
  
    | UnboundTypeParameter name
        -> Format.fprintf fmt "Unbound type parameter: %s" name
  
    | OpNotOverloadedForSig (name, _)   (* FIXME / DUPLICATED *)
        -> Format.fprintf fmt "Cannot find operator %a" pp_qsymbol name
  
    | UnexpectedType (ty1, ty2, t1, t2)
        ->
          let pp_type = PE.pp_type ~vmap:(EcUidgen.NameGen.create()) in
            Format.fprintf fmt "@[the expression has type %a@\n" pp_type ty1;
            Format.fprintf fmt "It is expected to have type %a.@\n" pp_type ty2;
            Format.fprintf fmt "Can not unify %a and %a@]" pp_type t1 pp_type t2
  
    | NonLinearPattern _
        -> Format.fprintf fmt "Non-linear pattern"
  
    | DuplicatedLocals None
        -> Format.fprintf fmt "DuplicatedLocals"

    | DuplicatedLocals (Some s)
        -> Format.fprintf fmt "A symbol %s already declared at %s"
            s.pl_desc (EcLocation.tostring s.pl_loc)
    | ProbaExpressionForbidden
        -> Format.fprintf fmt "ProbaExpressionForbidden"
  
    | PatternForbiden
        -> Format.fprintf fmt "PatternForbiden"
  
    | ModApplToNonFunctor
        -> Format.fprintf fmt "ModApplToNonFunctor"
  
    | ModApplInvalidArity
        -> Format.fprintf fmt "Wrong number of module parameters"
  
    | ModApplInvalidArgInterface
        -> Format.fprintf fmt "ModApplInvalidArgInterface"

    | TypeVariableNotAllowed 
        -> Format.fprintf fmt "Type variable not allowed"

    | UnificationVariableNotAllowed 
        -> Format.fprintf fmt "unification variable not allowed"

    | RandomExprNotAllowed 
        -> Format.fprintf fmt "random expression not allowed"

    | UnNamedTypeVariable 
        -> Format.fprintf fmt "unnamed type variable"

    | UnusedTypeVariable 
        -> Format.fprintf fmt "unused type variable" 
  
let _ = EcPexception.register (fun fmt exn -> 
  match exn with
  | TyError e -> Format.fprintf fmt "%a" pp_typerror e
  | _ -> raise exn)

let tyerror loc x = EcLocation.locate_error loc (TyError x)

(* -------------------------------------------------------------------- *)
let e_inuse =
  let rec inuse (map : Sm.t) (e : tyexpr) =
    match e.tye_node with
    | Evar p -> begin
        match p.pv_kind with
        | PVglob -> Sm.add p.pv_name map
        | _      -> map
      end
    | _ -> e_fold inuse map e
  in
    fun e -> inuse Sm.empty e
  
(* -------------------------------------------------------------------- *)
let (i_inuse, s_inuse) =
  let addflags p e map =
     Mm.change
       (fun flags -> Some (List.fold_left UM.add (odfl UM.empty flags) e))
       p map
  in

  let rec lv_inuse (map : use_flags Mm.t) (lv : lvalue) =
    match lv with
    | LvVar (p,_) ->
        addflags p.pv_name [`Write] map

    | LvTuple ps ->
        List.fold_left
          (fun map (p, _) -> addflags p.pv_name [`Write] map)
          map ps

    | LvMap (_, p, e, _) ->
      (* Maps are not modified in place but feed to a mutator
         operator that returns the augmented map and assigning the
         result to [p]. Hence the [`Read | `Write] flag. *)
      let map = addflags p.pv_name [`Read; `Write] map in
      let map = se_inuse map e in
        map

  and i_inuse (map : use_flags Mm.t) (i : instr) =
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
      let map = addflags p [`Call] map in
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

  and s_inuse (map : use_flags Mm.t) (s : stmt) =
    List.fold_left i_inuse map s.s_node

  and se_inuse (map : use_flags Mm.t) (e : tyexpr) =
    Sm.fold (fun p map -> addflags p [`Read] map) (e_inuse e) map

  in
    (i_inuse Mm.empty, s_inuse Mm.empty)

(* -------------------------------------------------------------------- *)
module UE = EcUnify.UniEnv

(* Politique de nommage :
   les variables locales masquent les autres noms courts.
*)
  
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
         try tvar (UE.get_var ue s.pl_desc)
         with _ -> tyerror s.pl_loc (UnboundTypeParameter s.pl_desc)
       else tyerror s.pl_loc TypeVariableNotAllowed;

  | PTtuple tys   -> 
      ttuple (transtys tp env ue tys)

  | PTnamed { pl_desc = name } -> 
      begin match EcEnv.Ty.lookup_opt name env with
      | None -> tyerror ty.pl_loc (UnknownTypeName name)
      | Some (p, tydecl) ->
          if tydecl.tyd_params <> [] then
            tyerror ty.pl_loc
              (InvalidNumberOfTypeArgs(name,List.length tydecl.tyd_params, 0));
          tconstr p []
      end
  | PTfun(ty1,ty2) ->
      tfun (transty tp env ue ty1) (transty tp env ue ty2) 
        
  | PTapp ({ pl_desc = name }, tyargs) -> 
      begin match EcEnv.Ty.lookup_opt name env with
      | None -> tyerror ty.pl_loc (UnknownTypeName name)
      | Some (p, tydecl) ->
          let nargs = List.length tyargs in
          let expected = List.length tydecl.tyd_params in
          if nargs <> expected then
            tyerror ty.pl_loc (InvalidNumberOfTypeArgs (name, expected, nargs));
          let tyargs = transtys tp env ue tyargs in 
          tconstr p tyargs
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
        (LTuple xs, ttuple subtys)

let transpattern env ue (p : EcParsetree.lpattern) =
  match transpattern1 env ue p with
  | LSymbol x as p, ty ->
      EcEnv.Var.bind_local x ty env, p, ty

  | LTuple xs as p, ({ty_node = Ttuple lty} as ty) ->
      EcEnv.Var.bind_locals (List.combine xs lty) env, p, ty

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

    | PEapp ({pl_desc = PEident({ pl_desc = name; pl_loc = loc }, tvi)}, es) ->
        let tvi = transtvi env ue tvi in  
        let es   = List.map (transexp env) es in
        let esig = snd (List.split es) in
        let ops  = select_op env name ue tvi esig in
        begin match ops with
        | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
            let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
            tyerror loc (UnknownOperatorForSig (name, esig))
              
        | [op, ty, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            let codom = ty_fun_app env ue ty esig in
            (e_app op (List.map fst es) codom, codom)
        end

    | PEapp(pe,pes) ->
        let e,ty = transexp env pe in
        let es = List.map (transexp env) pes in
        let esig = snd (List.split es) in
        let codom = ty_fun_app env ue ty esig in
        (e_app e (List.map fst es) codom, codom)

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
          (e_tuple es, ttuple tys)

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

let rec stmt_mapty onty s =
  EcModules.stmt (List.map (instr_mapty onty) s.s_node)

and instr_mapty onty i =
  match i.i_node with
  | Sasgn(x,e) ->
      asgn(lvalue_mapty onty x, Esubst.mapty onty e)

  | Srnd(x,e) ->
      rnd (lvalue_mapty onty x, Esubst.mapty onty e)

  | Scall(x,f,args) ->
      call (omap x (lvalue_mapty onty), f, 
            List.map (Esubst.mapty onty) args)

  | Sif(e,s1,s2) -> 
      if_ (Esubst.mapty onty e, stmt_mapty onty s1, stmt_mapty onty s2)

  | Swhile(e,s) ->
      while_ (Esubst.mapty onty e, stmt_mapty onty s)

  | Sassert e -> assert_ (Esubst.mapty onty e)

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
  | None   -> tyerror name.pl_loc (UnknownModName (unloc name))
  | Some x -> x

(* -------------------------------------------------------------------- *)
let lookup_module_type (env : EcEnv.env) (name : pqsymbol) =
  match EcEnv.ModTy.lookup_opt (unloc name) env with
  | None   -> tyerror name.pl_loc (UnknownTyModName (unloc name))
  | Some x -> x

(* -------------------------------------------------------------------- *)
let transmodtype (env : EcEnv.env) (modty : pmodule_type) =
  lookup_module_type env modty

(* -------------------------------------------------------------------- *)
let rec transmodsig (env : EcEnv.env) (name : symbol) (modty : pmodule_sig) =
  let Pmty_struct modty = modty in

  let margs =
    List.map (fun (x, i) ->
      (EcIdent.create (unloc x), fst (transmodtype env i)))
      modty.pmsig_params
  in

  let env = EcEnv.Mod.enter name margs env in

    { mt_params = margs;
      mt_body   = transmodsig_body env modty.pmsig_body;
      mt_mforb  = Sp.empty; }           (* FIXME *)

(* -------------------------------------------------------------------- *)
and transmodsig_body (env : EcEnv.env) (is : pmodule_sig_struct_body) =
  let transsig1 = function
    | `VariableDecl x ->
        let name  = x.pvd_name.pl_desc in
        let type_ = transty_nothing env x.pvd_type in
          Tys_variable (name, type_)

    | `FunctionDecl f ->
        let name   = f.pfd_name in
        let tyargs =
          List.map                      (* FIXME: continuation *)
            (fun (x, ty) -> (x.pl_desc, transty_nothing env ty))
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

let tymod_cnv_failure e =
  raise (TymodCnvFailure e)

let tysig_item_name = function
  | Tys_variable (x, _) -> x
  | Tys_function f      -> f.fs_name

let tysig_item_kind = function
  | Tys_variable _ -> `Variable
  | Tys_function _ -> `Function

let rec check_tymod_cnv mode (env : EcEnv.env) tin tout =
  (* Check parameters for compatibility. Parameters names may be
   * different, hence, substitute in [tin.tym_params] types the names
   * of [tout.tym_params] *)
  
  if List.length tin.mt_params <> List.length tout.mt_params then
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
      EcSubst.empty tin.mt_params tout.mt_params
  in
    (* Check for body inclusion (w.r.t the parameters names substitution).
     * This includes:
     * - Variables / functions inclusion with equal signatures +
     *   included use modifiers.
     * - Inclusion of forbidden names set *)

  let tin  = EcSubst.subst_modsig_body bsubst tin.mt_body
  and tout = tout.mt_body in

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
       * instantiating an abstract module with an implementation. *)

      let arg_compatible (aname1, aty1) (aname2, aty2) =
        aname1 = aname2 && EcEnv.equal_type env aty1 aty2
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
let add_local known_ids s = 
  match Mstr.find_opt s.pl_desc !known_ids with
    | None -> 
      known_ids := Mstr.add s.pl_desc s !known_ids;
      s.pl_desc
    | Some s' -> tyerror s.pl_loc (DuplicatedLocals (Some s')) 

let rec transmod (env : EcEnv.env) (x : symbol) (m : pmodule_expr) =
  match m with
  | Pm_ident ({ pl_desc = m }, args) -> begin
      let (mname, mty) = EcEnv.Mod.lookup m env in
      let args = List.map (EcEnv.Mod.lookup^~ env) (unlocs args) in
      let atymods = mty.me_sig.mt_params in

      (* Check module application *)
      if List.length atymods <> List.length args then
        tyerror dloc ModApplInvalidArity;

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
            mt_params = [];
            mt_body   = EcSubst.subst_modsig_body bsubst mty.me_sig.mt_body;
            mt_mforb  = Sp.empty;       (* FIXME *)
          };
          me_uses  = Sp.empty;          (* FIXME *)
          me_types = if args = [] then mty.me_types else []; }
  end

  | Pm_struct st ->
      transstruct env x st

(* -------------------------------------------------------------------- *)
and transstruct (env : EcEnv.env) (x : symbol) (st : pstructure) =
  (* Check parameters types *)
  let stparams =
    List.map                          (* FIXME: exn *)
      (fun (a, aty) ->
         (EcIdent.create a.pl_desc, fst (transmodtype env aty)))
      st.ps_params
  in

  (* Check structure items, extending environment initially with
   * structure arguments, and then with previously checked items.
   *)
  let (_, items) =
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
            (EcEnv.bindall (List.map tydecl1 newitems) env,
             List.rev_append acc newitems))
        (env, []) st.ps_body
  in

  (* Generate structure signature *)
  let tymod =
    let tymod1 = function
      | MI_Module   _ -> None           (* FIXME: what ? *)
      | MI_Variable v -> Some (Tys_variable (v.v_name, v.v_type))
      | MI_Function f -> Some (Tys_function f.f_sig) 
    in

    let sigitems = List.pmap tymod1 (List.map snd items) in
      { mt_params = stparams;
        mt_body   = sigitems;
        mt_mforb  = Sp.empty; };    (* FIXME *)
  in

  (* Check that generated signature is structurally included in
   * associated type mode. *)
  let types = List.map (transmodtype env) st.ps_signature in
    List.iter (check_tymod_sub env tymod) (List.map snd types);

  (* Construct structure representation *)
    { me_name  = x;
      me_body  = ME_Structure { ms_params = stparams;
                                ms_body   = List.map snd items; };
      me_comps = List.map snd items;
      me_uses  = Sp.empty;              (* FIXME *)
      me_sig   = tymod;
      me_types = List.map fst types; }

(* -------------------------------------------------------------------- *)
and transstruct1 (env : EcEnv.env) (st : pstructure_item) =
  match st with
  | Pst_mod ({ pl_desc = m }, me) ->
      let me = transmod env m me in
        [(m, MI_Module me)]

  | Pst_var (xs, ty) ->
      let ty = transty_nothing env ty in
        List.map
          (fun { pl_desc = x } ->
            (x, MI_Variable { v_name = x; v_type = ty; }))
          xs

  | Pst_fun (decl, body) -> begin
      let fid = decl.pfd_name.pl_desc in
      let ue = UE.create (Some []) in
      let known_ids = ref Mstr.empty in
      (* let add_local s =  *)
      (*   match Mstr.find_opt s.pl_desc !known_ids with *)
      (*   | None ->  *)
      (*       known_ids := Mstr.add s.pl_desc s !known_ids; *)
      (*       s.pl_desc *)
      (*   | Some s' -> tyerror s.pl_loc (DuplicatedLocals (Some s')) in *)
      (* First we add the parameters *)
      let add_param (s,ty) = add_local known_ids s, transty tp_uni env ue ty in
      let params = List.map add_param decl.pfd_tyargs in
      let params_ = 
        List.map (fun (id,ty) -> (id, `Variable (PVloc, ty))) params in
      let env = EcEnv.bindall params_ env in


      let rty = transty tp_uni env ue decl.pfd_tyresult in
      let stmt, re, locals, _env = transbody known_ids ue env body rty in

      let subst_uni = Tuni.subst (UE.close ue) in
      let check_type ty = 
        let ty = subst_uni ty in
        assert (EcUidgen.Suid.is_empty (Tuni.fv ty)); (* FIXME error message *)
        ty in
      let check_decl (id,ty) = id, check_type ty in
      let params = List.map check_decl params in
      let locals = List.rev_map check_decl locals in
      let rty = check_type rty in
      let stmt = stmt_mapty subst_uni stmt in
      let re = omap re (Esubst.mapty subst_uni) in
      let fun_ = 
        { f_name   = fid;
          f_sig    = {
            fs_name = decl.pfd_name.pl_desc;
            fs_sig  = (params, rty);
            fs_uses = Mp.empty;   (* FIXME *)
          };
          f_def = Some {
            f_locals = locals;
            f_body   = stmt;
            f_ret    = re;
          };
        } in 
      [(fid, MI_Function fun_)]
  end

  | Pst_alias _ -> assert false

and transbody known_ids ue env body rty = 
  let init = ref [] in
  let locals = ref [] in
  let add_local ty s = (add_local known_ids s, `Variable (PVloc, ty)) in
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
          oget (EcEnv.Var.lookup_progvar_opt ([], id) newenv) in
        init := asgn (LvVar(p,ty) , e) :: !init) locs);
    newenv 
  in
  let env = List.fold_left add_locals env body.pfb_locals in
  let stmt = transstmt ue env body.pfb_body in 
  let stmt = EcModules.stmt ((List.rev !init) @ stmt.s_node) in
  let re =
    match body.pfb_return with
      | None    -> 
        (* FIXME error message or location *)
        unify_error env ue EcLocation.dummy rty tunit; None
      | Some pe ->
        let re, ty = transexp env ue pe in
        unify_error env ue pe.pl_loc ty rty; Some re 
  in
    (stmt, re, !locals, env)

(* -------------------------------------------------------------------- *)
and transstmt ue (env : EcEnv.env) (stmt : pstmt) =
  EcModules.stmt (List.map (transinstr ue env) stmt)

(* -------------------------------------------------------------------- *)
and transinstr ue (env : EcEnv.env) (i : pinstr) =
  let transcall name args =
    let fpath, fdef =
      try
        EcEnv.Fun.lookup name env
      with EcEnv.LookupFailure _ ->
        tyerror dloc (UnknownFunction name)

    in
      if List.length args <> List.length (fst fdef.f_sig.fs_sig) then
        tyerror dloc ApplInvalidArity;
  
      let args =
        List.map2
          (fun a (_, ty) ->
            let a, aty = transexp env ue a in
              EcUnify.unify env ue aty ty; a)
          args (fst fdef.f_sig.fs_sig)
      in
        (fpath, args, snd fdef.f_sig.fs_sig)
  in

  match i with
  | PSasgn (lvalue, rvalue) -> 
      let lvalue, lty = translvalue ue env lvalue in
      let rvalue, rty = transexp env ue rvalue in
      EcUnify.unify env ue lty rty;
      asgn (lvalue, rvalue)

  | PSrnd(lvalue, rvalue) -> 
      let lvalue, lty = translvalue ue env lvalue in
      let rvalue, rty = transexp env ue rvalue in
      EcUnify.unify env ue (tdistr lty) rty;
      rnd(lvalue, rvalue)

  | PScall (None, { pl_desc = name }, args) ->
      let (fpath, args, rty) = transcall name args in
      EcUnify.unify env ue tunit rty;
      call (None, fpath, args)

  | PScall (Some lvalue, { pl_desc = name }, args) ->
      let lvalue, lty = translvalue ue env lvalue in
      let (fpath, args, rty) = transcall name args in
      EcUnify.unify env ue lty rty;
      call (Some lvalue, fpath, args)

  | PSif (e, s1, s2) ->
      let e, ety = transexp env ue e in
      let s1 = transstmt ue env s1 in
      let s2 = transstmt ue env s2 in
  
        EcUnify.unify env ue ety tbool;
        if_ (e, s1, s2)

  | PSwhile (e, body) ->
      let e, ety = transexp env ue e in
      let body = transstmt ue env body in

        EcUnify.unify env ue ety tbool;
        while_ (e, body)

  | PSassert e ->
     let e, ety = transexp env ue e in 
       EcUnify.unify env ue ety tbool;
       assert_ e

(* -------------------------------------------------------------------- *)
and trans_pv env { pl_desc = x; pl_loc = loc } = 
  match EcEnv.Var.lookup_progvar_opt x env with
  | None -> tyerror loc (UnknownVariable x)
  | Some(pv,xty) -> pv, xty 

and translvalue ue (env : EcEnv.env) lvalue =
  match lvalue with
  | PLvSymbol x ->
      let pty = trans_pv env x in
      LvVar pty, snd pty

  | PLvTuple xs -> 
      let xs = List.map (trans_pv env) xs in
      let ty = ttuple (List.map snd xs) in
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
      | [ ({tye_node = Eop (p,tys) }, _, subue)] ->
          EcUnify.UniEnv.restore ~src:subue ~dst:ue;
          (LvMap ((p,tys), pv, e, codomty), codomty) 
      | _ ->        (* FIXME: better error message *)
          let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
          tyerror x.pl_loc (UnknownOperatorForSig (name, esig))

(* -------------------------------------------------------------------- *)
let rec trans_msymbol (env : EcEnv.env) (msymb : pmsymbol) =
  let mod_qname =
    match List.rev_map fst msymb with
    | [] -> assert false
    | x :: qn ->
        { pl_desc = (List.rev_map unloc qn, unloc x);
          pl_loc  = x.pl_loc; }
  in

  let (mod_path, mod_expr) =
    match EcEnv.Mod.sp_lookup_opt mod_qname.pl_desc env with
    | None ->
        tyerror mod_qname.pl_loc
          (UnknownModName mod_qname.pl_desc)
    | Some me -> me in

  let mod_expr   = mod_expr.EcEnv.sp_target
  and mod_params =
       mod_expr.EcEnv.sp_target.me_sig.mt_params
    :: mod_expr.EcEnv.sp_params
  and mod_args   =
       List.rev_append
         (List.map snd msymb)
         (List.create
            (EcPath.p_size (EcPath.path_of_mpath mod_path)
               - List.length msymb)
            [])
  in

  let mod_args =
    List.map
      (fun args ->
        List.map
          (fun { pl_desc = arg } -> trans_msymbol env arg)
          args)
      mod_args
  in
    List.iter2
      (fun param arg ->
         if List.length param <> List.length arg then
           tyerror dloc ModApplInvalidArity;
         List.iter2
           (fun (_, p) (_, a) ->
              if not (EcEnv.ModTy.has_mod_type env a p) then
                tyerror dloc ModApplInvalidArgInterface)
           param arg)
      mod_params mod_args;

    let aout =
      EcPath.mpath
        mod_path.EcPath.m_path
        mod_path.EcPath.m_kind
        (List.map (List.map fst) mod_args)
    in
      (aout, if   mod_expr.me_sig.mt_params = []
             then mod_expr.me_types
             else [])

(* -------------------------------------------------------------------- *)
and trans_gamepath (env : EcEnv.env) gp =
  let modsymb = List.map (unloc -| fst) (fst (unloc gp))
  and funsymb = unloc (snd (unloc gp)) in
  let _, _ =
    match EcEnv.Fun.sp_lookup_opt (modsymb, funsymb) env with
    | None -> tyerror gp.pl_loc (UnknownFunction (modsymb, funsymb))
    | Some (p, me) -> (p, me)
  in

  let fpath = fst (trans_msymbol env (fst (unloc gp))) in
  let fpath = EcPath.mqname fpath EcPath.PKother funsymb [] in

    fpath

(* -------------------------------------------------------------------- *)
let transfpattern env ue (p : EcParsetree.lpattern) =
  match transpattern1 env ue p with
  | LSymbol x, ty ->
      (EcEnv.Var.bind_local x ty env, LSymbol x, ty)
  | LTuple xs, ({ty_node = Ttuple lty } as ty) ->
      (EcEnv.Var.bind_locals (List.combine xs lty) env, LTuple xs, ty)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let transform env ue pf tt =
  let rec transf env f = 
    match f.pl_desc with
    | PFint n ->
        f_int n

    | PFtuple args ->
        f_tuple (List.map (transf env) args)

    | PFident ({ pl_desc = name;pl_loc = loc }, tvi) -> 
        let tvi = transtvi env ue tvi in
        let ops = select_sided_op env name ue tvi [] in
        begin match ops with
        | [] | _ :: _ :: _ -> (* FIXME: better error message *)
            tyerror loc (UnknownOperatorForSig (name, []))
        | [op, subue] ->
            EcUnify.UniEnv.restore ~src:subue ~dst:ue;
            op
        end

    | PFside (f, side) -> begin
        let me =
          match EcEnv.Memory.lookup (unloc side) env with
          | None -> tyerror side.pl_loc (UnknownMemory (unloc side))
          | Some me -> EcEnv.Memory.actmem_name me
        in
          transf (EcEnv.Memory.set_active me env) f
      end

    | PFapp ({pl_desc = PFident({ pl_desc = name; pl_loc = loc }, tvi)}, es) ->
        let tvi  = transtvi env ue tvi in  
        let es   = List.map (transf env) es in
        let esig = List.map EcFol.ty es in 
        let ops  = select_sided_op env name ue tvi esig in
          begin match ops with
          | [] | _ :: _ :: _ ->        (* FIXME: better error message *)
              let esig = Tuni.subst_dom (EcUnify.UniEnv.asmap ue) esig in
                tyerror loc (UnknownOperatorForSig (name, esig))
  
          | [op, subue] ->
              EcUnify.UniEnv.restore ~src:subue ~dst:ue;
              let codom = ty_fun_app env ue op.f_ty esig in
                f_app op es codom
          end

    | PFapp (e, es) ->
        let es   = List.map (transf env) es in
        let esig = List.map EcFol.ty es in 
        let op  = transf env e in
        let codom = ty_fun_app env ue op.f_ty esig in
        f_app op es codom

    | PFif (pf1, f2, f3) ->
        let f1 = transf env pf1 in
        unify_error env ue pf1.pl_loc f1.f_ty tbool;
        let f2 = transf env f2 in
        let f3 = transf env f3 in
        f_if f1 f2 f3

    | PFlet (lp, pf1, f2) ->
        let (penv, p, pty) = transfpattern env ue lp in
        let f1 = transf env pf1 in
        unify_error env ue pf1.pl_loc f1.f_ty pty;
        let f2 = transf penv f2 in
        f_let p f1 f2 

    | PFforall (xs, pf) ->
        let env, xs = trans_fbind env ue xs in
        let f = transf env pf in
        unify_error env ue pf.pl_loc f.f_ty tbool;
        f_forall xs f

    | PFexists (xs, f1) ->
        let env, xs = trans_fbind env ue xs in
        let f = transf env f1 in
        unify_error env ue pf.pl_loc f.f_ty tbool;
        f_exists xs f

    | PFprob (gp, args, m, event) ->
        let fpath = trans_gamepath env gp in
        let fun_  = EcEnv.Fun.by_mpath fpath env in
        let fsig  = fun_.f_sig.fs_sig in

        if List.length args <> List.length (fst fsig) then
          tyerror f.pl_loc ApplInvalidArity;

        let args =
          let doit1 arg (_, aty) =
            let aout = transf env arg in
              unify_error env ue arg.pl_loc aout.f_ty aty;
              aout
          in
            List.map2 doit1 args (fst fsig)
        in

        let memid =
          match EcEnv.Memory.lookup (unloc m) env with
          | None ->
              tyerror m.pl_loc (UnknownMemory (unloc m))

          | Some (EcEnv.AMConcrete _) ->
              tyerror m.pl_loc (AbstractMemoryWanted (unloc m))

          | Some (EcEnv.AMAbstract mid) ->
              mid
        in

        let event =
          let (_, env) = EcEnv.Fun.enter true memid fpath env in
            transf env event
        in

        let resty = snd fun_.f_sig.fs_sig in
          f_pr memid fpath args (EcIdent.create "$res", resty) event

    | PFhoareF (pre, gp, post) ->
        let fpath = trans_gamepath env gp in

        let pre =
          let (_, env) = EcEnv.Fun.enter false EcFol.mpre fpath env in
            transf env pre
        and post =
          let (_, env) = EcEnv.Fun.enter true EcFol.mpost fpath env in
            transf env post
        in

          f_hoareF pre fpath post

    | PFequivF (pre, (gp1, gp2), post) ->
        let fpath1 = trans_gamepath env gp1 in
        let fpath2 = trans_gamepath env gp2 in

        let p1 = EcPath.path_of_mpath fpath1
        and p2 = EcPath.path_of_mpath fpath2 in

        let pre =
          let mem1 = EcEnv.Fun.memenv false EcFol.mleft  p1 env in
          let mem2 = EcEnv.Fun.memenv false EcFol.mright p2 env in
          let env  = EcEnv.Memory.push_all [(fpath1, mem1); (fpath2, mem2)] env in
            transf env pre in

        let post =
          let mem1 = EcEnv.Fun.memenv true EcFol.mleft  p1 env in
          let mem2 = EcEnv.Fun.memenv true EcFol.mright p2 env in
          let env  = EcEnv.Memory.push_all [(fpath1, mem1); (fpath2, mem2)] env in
            transf env post in

          f_equivF pre fpath1 fpath2 post

    (* test *)
    | PFhoare (pre,body,post) ->
      (* Cesar says: what should I assume about local variables in pre/post? *)
      let known_ids = ref Mstr.empty in
      let ue = UE.create (Some []) in (* I ignore this *)
      (* FIXME: assuming no return statement, bad error message *)
      let stmt, _re, locals, env = transbody known_ids ue env body tunit in
(*
      let env' = Fenv.mono_env env in
      let env = {env' with Fenv.fe_locals=env.Fenv.fe_locals } in
*)
      let _pre = transf env pre in
      let _post = transf env post in
      let _f_def = {f_locals=locals; f_body=stmt; f_ret=None } in
      (* f_hoare  pre f_def post *)
      f_true (* missing memory *)      

  and trans_fbind env ue decl = 
    let trans1 env ({ pl_desc = x }, pgty) =
      let x = EcIdent.create x in
        match pgty with
        | PGTY_Type ty -> 
            let ty = transty tp_relax env ue ty in
              (EcEnv.Var.bind_local x ty env, (x, GTty ty))
  
        | PGTY_ModTy mi ->
            let (mi, _) = transmodtype env mi in
              (EcEnv.Mod.bind_local x mi env, (x, GTmodty mi))
  
        | PGTY_Mem ->
            (EcEnv.Memory.push (EcEnv.AMAbstract x) env, (x, GTmem))
    in
      List.map_fold trans1 env decl

  and select_sided_op env ((qs, x) as name) ue tvi psig =
    let locals =
      if   qs = []
      then EcEnv.Var.lookup_local_opt x env
      else None
    in
      match locals with
      | Some (id, ty) ->
          if tvi <> None then assert false;
          [ (f_local id ty, ue) ]

      | None -> begin
          let me  = EcEnv.Memory.get_active env in
          let pvs = select_pv env me name ue tvi psig in
          let ops = EcUnify.select_op true tvi env name ue psig in

          let prepare_pv (pv, ty, ue)  =
            (f_pvar pv ty (odfl EcFol.mstd me), ue)
          and prepare_op ((op, tys), ty, ue) =
            (f_op op tys ty, ue)
          in
            (List.map prepare_pv pvs) @ (List.map prepare_op ops)
        end
  in

  let f = transf env pf in
    unify_error env ue pf.pl_loc f.f_ty tt; f
      
(* -------------------------------------------------------------------- *)
let transformula env ue pf = 
  transform env ue pf tbool
