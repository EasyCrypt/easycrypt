(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcDecl
open EcTypesmod
open EcWhy3

module IM  = EcIdent.Map
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type lookup_failure = [
  | `Path    of EcPath.path
  | `QSymbol of qsymbol
]

exception LookupFailure of lookup_failure

let try_lf (f : unit -> 'a) =
  try Some (f ()) with LookupFailure _ -> None

(* -------------------------------------------------------------------- *)
type comp_th =
  { cth_path : EcPath.path;
    cth_w3   : EcWhy3.rebinding;
    cth_item : theory } 

let theory_of_comp_th th = th.cth_item

(* -------------------------------------------------------------------- *)
type preenv = {
  env_scope  : EcPath.path;
  env_root   : premc;
  env_comps  : (EcPath.path * premc) Mid.t;
  env_w3     : EcWhy3.env;
  env_rb     : EcWhy3.rebinding;        (* in reverse order *)
  env_item   : theory_item list         (* in reverse order *)
}

and premc = {
  mc_variables  : (EcPath.path * EcTypes.ty)        IM.t;
  mc_functions  : (EcPath.path * EcTypesmod.funsig) IM.t;
  mc_modules    : (EcPath.path * EcTypesmod.tymod)  IM.t;
  mc_modtypes   : (EcPath.path * EcTypesmod.tymod)  IM.t;
  mc_typedecls  : (EcPath.path * EcDecl.tydecl)     IM.t;
  mc_operators  : (EcPath.path * EcDecl.operator)   IM.t;
  mc_axioms     : (EcPath.path * EcDecl.axiom)      IM.t;
  mc_theories   : (EcPath.path * EcTypesmod.theory) IM.t;
  mc_components : unit IM.t;
}

type env = preenv
type mcomponents = premc

(* -------------------------------------------------------------------- *)
let emcomponents = {
  mc_variables  = EcIdent.Map.empty;
  mc_functions  = EcIdent.Map.empty;
  mc_modules    = EcIdent.Map.empty;
  mc_modtypes   = EcIdent.Map.empty;
  mc_typedecls  = EcIdent.Map.empty;
  mc_operators  = EcIdent.Map.empty;
  mc_axioms     = EcIdent.Map.empty;
  mc_theories   = EcIdent.Map.empty;
  mc_components = EcIdent.Map.empty;
}

(* -------------------------------------------------------------------- *)
let empty =
  let path = EcPath.Pident EcPath.id_top
  and name = EcPath.id_top in
  let env  =
    { env_scope = path;
      env_root  = { emcomponents with mc_components = IM.add name () IM.empty };
      env_comps = Mid.add name (path, emcomponents) Mid.empty;
      env_w3    = EcWhy3.empty;
      env_rb    = [];
      env_item  = [];
    }
  in 
    env

(* -------------------------------------------------------------------- *)
let preenv (env : preenv) : env = env

(* -------------------------------------------------------------------- *)
let root (env : env) = env.env_scope

(* -------------------------------------------------------------------- *)
module type S = sig
  type t

  val bind              : EcIdent.t -> t -> env -> env
  val bindall           : (EcIdent.t * t) list -> env -> env
  val lookup_by_path    : EcPath.path -> env -> t        (* full path *)
  val trylookup_by_path : EcPath.path -> env -> t option (* full path *)
  val lookup            : qsymbol -> env -> EcPath.path * t
  val trylookup         : qsymbol -> env -> (EcPath.path * t) option
  val exists            : qsymbol -> env -> bool
end

(* -------------------------------------------------------------------- *)
module MC = struct
  (* ------------------------------------------------------------------ *)
  let lookup_mc_by_path =
    let rec lookup1 (env : env) (mc : mcomponents) (x : EcIdent.t) =
      match IM.byident x mc.mc_components with
      | None   -> None
      | Some _ -> omap (Mid.find_opt x env.env_comps) snd
    in
  
    let rec lookup env mc = function
      | Pident x      -> lookup1 env mc x
      | Pqname (p, x) -> obind (lookup env mc p) ((lookup1 env)^~ x)
    in
      fun env mc path -> lookup env mc path
  
  let lookup_by_path proj (path : EcPath.path) (env : env) = 
    let mc =
      match path with
      | Pident _      -> Some env.env_root
      | Pqname (p, _) -> lookup_mc_by_path env env.env_root p
    in
  
    let bname = EcPath.basename path in
    let obj   = obind mc (fun mc -> IM.byident bname (proj mc)) in
  
      match obj with
      | None        -> raise (LookupFailure (`Path path))
      | Some (p, x) ->
          assert (p = path); x

  (* ------------------------------------------------------------------ *)
  let rec lookup_mc (env : env) (qn : symbols) (mc : mcomponents) =
    match qn with
    | [] -> Some mc
    | name :: qn -> begin
      match IM.byname name mc.mc_components with
      | None -> None
      | Some (x, _) ->
          obind
            (Mid.find_opt x env.env_comps)
            (fun (_, mc) -> lookup_mc env qn mc)
    end

  let lookup proj ((qn, x) : qsymbol) (env : env) =
    match
      obind
        (lookup_mc env qn env.env_root)
        (fun mc -> IM.byname x (proj mc))
    with
    | None   -> raise (LookupFailure (`QSymbol (qn, x)))
    | Some x -> snd x

  let lookupall proj ((qn, x) : qsymbol) (env : env) =
    odfl []
      (omap
         (lookup_mc env qn env.env_root)
         (fun mc -> List.map snd (IM.allbyname x (proj mc))))

  (* ------------------------------------------------------------------ *)
  let mc_bind_variable path ty mc =
    let x = EcPath.basename path in
      { mc with
          mc_variables = IM.add x (path, ty) mc.mc_variables; }

  let mc_bind_function path fsig mc =
    let x = EcPath.basename path in
      { mc with
          mc_functions = IM.add x (path, fsig) mc.mc_functions; }

  let mc_bind_module path tymod mc =
    let x = EcPath.basename path in
      { mc with
          mc_modules = IM.add x (path, tymod) mc.mc_modules; }

  let mc_bind_modtype path tymod mc =
    let x = EcPath.basename path in
      { mc with
          mc_modtypes = IM.add x (path, tymod) mc.mc_modtypes; }

  let mc_bind_typedecl path tydecl mc =
    let x = EcPath.basename path in
      { mc with
          mc_typedecls = IM.add x (path, tydecl) mc.mc_typedecls; }

  let mc_bind_op path op mc =
    let x = EcPath.basename path in
      { mc with
          mc_operators = IM.add x (path, op) mc.mc_operators; }

  let mc_bind_ax path ax mc =
    let x = EcPath.basename path in
      { mc with
          mc_axioms = IM.add x (path, ax) mc.mc_axioms; }

  let mc_bind_theory path th mc =
    let x = EcPath.basename path in
      { mc with
          mc_theories = IM.add x (path, th) mc.mc_theories; }

  let mc_bind_comp path mc =
    let x = EcPath.basename path in
      { mc with mc_components = IM.add x () mc.mc_components }

  let rec mc_of_module (_env : env) (_ : tymod) =
    emcomponents                        (* FIXME *)

  (* ------------------------------------------------------------------ *)
  let bind env binder name obj =
    let path   = EcPath.Pqname (env.env_scope, name) in
    let comps  =
      Mid.change
        (fun o -> omap o (snd_map (binder path obj)))
        (EcPath.basename env.env_scope)
        env.env_comps
    in
      { env with
          env_root  = binder path obj env.env_root;
          env_comps = comps; }

  (* -------------------------------------------------------------------- *)
  let import env binder path obj =
    { env with
        env_root = binder path obj env.env_root; }

  (* -------------------------------------------------------------------- *)
  let bind_mc env name comps =
    let path = EcPath.Pqname (env.env_scope, name) in
    let env  =
      { env with
        env_root  = mc_bind_comp path env.env_root;
        env_comps = 
          Mid.change
            (fun o -> omap o (snd_map (mc_bind_comp path)))
            (EcPath.basename env.env_scope)
            env.env_comps; }
    in
    { env with                        (* FIXME: dup *)
        env_comps = Mid.add name (path, comps) env.env_comps }

  (* ------------------------------------------------------------------ *)
  let rec bind_variable x ty env =
    bind env mc_bind_variable x ty

  and bind_function x fsig env =
    bind env mc_bind_function x fsig

  and bind_module x tymod env =
    let comps = mc_of_module env tymod in
    let env   = bind env mc_bind_module x tymod in
    let env   = bind_mc env x comps in
      env

  and bind_modtype x tymod env =
    bind env mc_bind_modtype x tymod

  and bind_typedecl x tydecl env =
    bind env mc_bind_typedecl x tydecl

  and bind_op x op env =
    bind env mc_bind_op x op

  and bind_ax x ax env =
    bind env mc_bind_ax x ax

  and bind_theory x th env =
    let env, comps = mc_of_theory env env.env_scope x th in
    let env = bind env mc_bind_theory x th in
    let env = bind_mc env x comps in
      env

  and mc_of_theory =
    let rec mc_of_theory_item path (env, mc) = function 
      | Th_type     (id, td) -> env, mc_bind_typedecl (EcPath.Pqname (path, id)) td mc
      | Th_operator (id, op) -> env, mc_bind_op (EcPath.Pqname (path, id)) op mc
      | Th_axiom    (id, ax) -> env, mc_bind_ax (EcPath.Pqname (path, id)) ax mc
      | Th_modtype  (id, tm) -> env, mc_bind_modtype (EcPath.Pqname (path, id)) tm mc
      | Th_module   m        -> env, mc_bind_module (EcPath.Pqname (path, m.me_name)) m.me_sig mc
      | Th_export   _        -> env, mc
      | Th_theory   (id, th) ->
          let env, submc =
            List.fold_left
              (mc_of_theory_item (EcPath.Pqname (path, id)))
              (env, emcomponents) th
          and subpath = EcPath.Pqname (path, id) in
  
          let env =
            let comps = env.env_comps in
            let comps = Mid.add id (subpath, submc) comps in
              { env with env_comps = comps }
          in
            (env, mc_bind_comp subpath (mc_bind_theory subpath th mc))
    in
      fun (env : env) (path : EcPath.path) (name : EcIdent.t) (theory : theory) ->
        List.fold_left
          (mc_of_theory_item (EcPath.Pqname (path, name)))
          (env, emcomponents)
          theory
end

(* -------------------------------------------------------------------- *)
let enter_id (name : EcIdent.t) (env : env) =
  let path = EcPath.Pqname (env.env_scope, name) in
  let env  = MC.bind_mc env name emcomponents in
    { env with
        env_scope = path;
        env_w3    = env.env_w3;
        env_rb    = [];
        env_item  = []; }

(* -------------------------------------------------------------------- *)
let enter (name : symbol) (env : env) =
  let name = EcIdent.create name in
  let env  = enter_id name env in
    (name, env)

(* -------------------------------------------------------------------- *)
module type Projector = sig
  type t

  val project : mcomponents -> (EcPath.path * t) EcIdent.Map.t
  val bind    : EcIdent.t -> t -> env -> env
end

(* -------------------------------------------------------------------- *)
module BaseS(P : Projector) : S with type t = P.t = struct
  type t = P.t

  let bind = P.bind

  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys

  let lookup_by_path = 
    MC.lookup_by_path P.project

  let lookup =
    MC.lookup P.project

  let trylookup_by_path path env = 
    try_lf (fun () -> lookup_by_path path env)

  let trylookup x env =
    try_lf (fun () -> lookup x env)

  let exists x env = (trylookup x env <> None)
end

(* -------------------------------------------------------------------- *)
module Var = struct
  include BaseS(struct
    type t = EcTypes.ty

    let project mc = mc.mc_variables
    let bind = MC.bind_variable
  end)
end

(* -------------------------------------------------------------------- *)
module Fun = struct
  include BaseS(struct
    type t = funsig

    let project mc = mc.mc_functions
    let bind = MC.bind_function
  end)
end

(* -------------------------------------------------------------------- *)
module Ty = struct
  include BaseS(struct
    type t = tydecl

    let project mc = mc.mc_typedecls
    let bind id t env = 
      let env = MC.bind_typedecl id t env in
      let w3, r = 
        EcWhy3.add_ty env.env_w3 (EcPath.extend (Some env.env_scope) id) t in
      { env with
        env_w3 = w3;
        env_rb = r::env.env_rb;
        env_item = Th_type(id,t) :: env.env_item }
  end)

  let rebind = MC.bind_typedecl

  let defined (name : EcPath.path) (env : env) =
    match trylookup_by_path name env with
    | Some { tyd_type = Some _ } -> true
    | _ -> false

  let unfold (name : EcPath.path) (args : EcTypes.ty list) (env : env) =
    match trylookup_by_path name env with
    | Some ({ tyd_type = Some body} as tyd) ->
        EcTypes.inst_var (EcTypes.init_substvar tyd.tyd_params args) body
    | _ -> raise (LookupFailure (`Path name))
end

(* -------------------------------------------------------------------- *)
module Op = struct
  include BaseS(struct
    type t = operator

    let project mc = mc.mc_operators

    let bind id op env = 
      let env = MC.bind_op id op env in
      let w3, r = 
        EcWhy3.add_op env.env_w3 (EcPath.extend (Some env.env_scope) id) op
      in
        { env with
            env_w3 = w3;
            env_rb = List.ocons r env.env_rb;
            env_item = Th_operator(id,op) :: env.env_item }
  end)

  let rebind = MC.bind_op

  let all (qname : qsymbol) (env : env) =
    MC.lookupall (fun mc -> mc.mc_operators) qname env
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  include BaseS(struct
    type t = axiom

    let project mc = mc.mc_axioms
    let bind id ax env = 
      let env = MC.bind_ax id ax env in
      let w3, r = 
        EcWhy3.add_ax env.env_w3 (EcPath.extend (Some env.env_scope) id) ax in
      { env with
        env_w3 = w3;
        env_rb = r :: env.env_rb;
        env_item = Th_axiom(id,ax) :: env.env_item }

  end)
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  (* FIXME *)
  type t = module_expr

  let project mc = mc.mc_modules

  let bind_s = MC.bind_module

  let bindall_s xtys env =
    List.fold_left
      (fun env (x, ty) -> bind_s x ty env)
      env xtys
    
  let bind id m env = 
    assert (EcIdent.id_equal id m.me_name);
    let env = MC.bind_module id m.me_sig env in
    { env with
      env_item = Th_module m :: env.env_item }
      
  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys

  let lookup_by_path = 
    MC.lookup_by_path project

  let lookup =
    MC.lookup project

  let trylookup_by_path path env = 
    try_lf (fun () -> lookup_by_path path env)

  let trylookup x env =
    try_lf (fun () -> lookup x env)

  let exists x env = (trylookup x env <> None)  
end

(* -------------------------------------------------------------------- *)
module ModTy = struct
  include BaseS(struct
    type t = tymod

    let project mc = mc.mc_modtypes
    let bind id mt env = 
      let env = MC.bind_modtype id mt env in
      { env with
        env_item = Th_modtype(id,mt) :: env.env_item }
  end)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  type t = comp_th 

  (* ------------------------------------------------------------------ *)
  let enter = enter

  (* ------------------------------------------------------------------ *)
  let bind id cth env = 
    assert (EcPath.p_equal 
              (EcPath.extend (Some env.env_scope) id) 
              cth.cth_path);

    let env = MC.bind_theory id cth.cth_item env in
      let theory =
        Th_theory (EcPath.basename cth.cth_path, cth.cth_item)
      in
        { env with
            env_w3   = EcWhy3.rebind env.env_w3 cth.cth_w3;
            env_rb   = List.rev_append cth.cth_w3 env.env_rb;
            env_item = theory :: env.env_item; }

  (* ------------------------------------------------------------------ *)
  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys
      
  (* ------------------------------------------------------------------ *)
  let lookup_by_path =
    MC.lookup_by_path (fun mc -> mc.mc_theories)
      
  (* ------------------------------------------------------------------ *)
  let lookup =
    MC.lookup (fun mc -> mc.mc_theories)
      
  (* ------------------------------------------------------------------ *)
  let trylookup_by_path path env = 
    try_lf (fun () -> lookup_by_path path env)
      
  (* ------------------------------------------------------------------ *)
  let trylookup x env =
    try_lf (fun () -> lookup x env)

  (* ------------------------------------------------------------------ *)
  let exists x env = (trylookup x env <> None)

  (* ------------------------------------------------------------------ *)
  let import (path : EcPath.path) (env : env) =
    let rec import (env : env) (th : theory) =
      let xpath x = EcPath.Pqname (path, x) in
      let rec import_th_item (env : env) = function
        | Th_type (x, ty) ->
            MC.import env MC.mc_bind_typedecl (xpath x) ty

        | Th_operator (x, op) ->
            MC.import env MC.mc_bind_op (xpath x) op

        | Th_axiom (x, ax) ->
            MC.import env MC.mc_bind_ax (xpath x) ax

        | Th_modtype (x, ty) ->
            MC.import env MC.mc_bind_modtype (xpath x) ty

        | Th_module m -> 
            MC.import env MC.mc_bind_module (xpath m.me_name) m.me_sig

        | Th_export p ->
            import env (lookup_by_path p env)

        | Th_theory (x, th) ->
            let env = MC.import env MC.mc_bind_theory (xpath x) th in
              { env with env_root = MC.mc_bind_comp (xpath x) env.env_root }
      in
        List.fold_left import_th_item env th

    in
      import env (lookup_by_path path env)

  (* ------------------------------------------------------------------ *)
  let export (path : EcPath.path) (env : env) =
    { env with
        env_item = Th_export path :: env.env_item }

  (* ------------------------------------------------------------------ *)
  let close env = 
    { cth_path = env.env_scope;
      cth_w3   = List.rev env.env_rb;
      cth_item = List.rev env.env_item }

  (* ------------------------------------------------------------------ *)
  let require x th env =
    let rootnm    = EcPath.rootname env.env_scope in
    let thpath    = EcPath.Pqname (EcPath.Pident rootnm, x) in
    let env, thmc = MC.mc_of_theory env (EcPath.Pident rootnm) x th in

    let topmc = snd (Mid.find rootnm env.env_comps) in
    let topmc = {
      topmc with
        mc_theories   = IM.add x (thpath, th) topmc.mc_theories;
        mc_components = IM.add x () topmc.mc_components; }
    in

    let root = {
      env.env_root with
        mc_components = IM.add x () env.env_root.mc_components }
    in

    let comps = env.env_comps in
    let comps = Mid.add rootnm (EcPath.Pident rootnm, topmc) comps in
    let comps = Mid.add x (thpath, thmc) comps in

      { env with env_root  = root; env_comps = comps; }
end

(* -------------------------------------------------------------------- *)
module Ident = struct
  type idlookup_t = [`Var | `Ctnt of operator]

  let trylookup (name : qsymbol) (env : env) =
    let for_var () =
      match Var.trylookup name env with
      | None -> None
      | Some (p, ty) -> Some (p, Some ty, (`Var :> idlookup_t))

    and for_op () =
      match Op.trylookup name env with
      | None -> None
      | Some (_, op) when not (op_ctnt op) -> None
      | Some (p, op) -> Some (p, op.op_codom, (`Ctnt op :> idlookup_t))
    in
      List.fpick [for_var; for_op]

  let lookup (name : qsymbol) (env : env) =
    match trylookup name env with
    | None   -> raise (LookupFailure (`QSymbol name))
    | Some x -> x
end

(* -------------------------------------------------------------------- *)
let import_w3 env th rd = 
  let lth, rbi = EcWhy3.import_w3 env.env_w3 env.env_scope th rd in
  let env = { env with env_w3 = EcWhy3.rebind env.env_w3 [rbi];
              env_rb = rbi :: env.env_rb;
              env_item = List.rev_append lth env.env_item
            } in
  let add env = function
    | Th_type (id,ty) -> Ty.rebind id ty env
    | Th_operator   (id,op) -> Op.rebind id op env 
    | _ -> assert false in
  List.fold_left add env lth 

let import_w3_dir env dir name rd =
  let th = EcWhy3.get_w3_th dir name in
  import_w3 env th rd 

(* -------------------------------------------------------------------- *)
let initial = 
  let env0 = empty in
  let env = enter_id EcPath.id_pervasive env0 in
  let bool_rn = [
    ["bool"] , EcWhy3.RDts, EcPath.basename EcPath.p_bool;
    ["True"] , EcWhy3.RDls, EcPath.basename EcPath.p_true;
    ["False"], EcWhy3.RDls, EcPath.basename EcPath.p_false ] in
  let env = import_w3 env Why3.Theory.bool_theory bool_rn in
  let opb_rn = [
    ["andb"] , EcWhy3.RDls, EcPath.basename EcPath.p_and;
    ["orb"]  , EcWhy3.RDls, EcPath.basename EcPath.p_or;
    ["implb"], EcWhy3.RDls, EcPath.basename EcPath.p_imp;
    ["notb"] , EcWhy3.RDls, EcPath.basename EcPath.p_not ] in 
  let env = import_w3_dir env ["bool"] "Bool" opb_rn in
  let builtin_rn = [
    ["int"] , EcWhy3.RDts, EcPath.basename EcPath.p_int;
    ["real"], EcWhy3.RDts, EcPath.basename EcPath.p_real ] in
  let env = import_w3 env Why3.Theory.builtin_theory builtin_rn in
  let cth = Theory.close env in
  let env1 = Theory.bind EcPath.id_pervasive cth env0 in
  let env1 = Theory.import EcPath.p_pervasive env1 in
  env1

let p_eq = fst (Op.lookup ([], "infix =") initial) 

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of EcTypes.ty
  | `Function  of funsig
  | `Module    of tymod
  | `ModType   of tymod
]

let bind1 ((x, eb) : EcIdent.t * ebinding) (env : env) =
  match eb with
  | `Variable ty -> Var   .bind x ty env
  | `Function f  -> Fun   .bind x f  env
  | `Module   m  -> Mod   .bind_s x m  env
  | `ModType  i  -> ModTy .bind x i  env

let bindall (items : (EcIdent.t * ebinding) list) (env : env) =
  List.fold_left ((^~) bind1) env items  
