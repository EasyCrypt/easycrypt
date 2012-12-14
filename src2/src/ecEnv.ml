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
type preenv = {
  env_scope  : EcPath.path;
  env_root   : premc;
  env_comps  : (EcPath.path * premc) Mid.t
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
let enter (name : symbol) (env : env) =
  let name = EcIdent.create name in
  let path = EcPath.Pqname (env.env_scope, name) in

  let env =
    { env_scope = path;
      env_root  = begin
        let comps = env.env_root.mc_components in
        let comps = IM.add name () comps in
          { env.env_root with mc_components = comps }
      end;
      env_comps = Mid.add name (path, emcomponents) env.env_comps }
  in
    (name, env)

(* -------------------------------------------------------------------- *)
let empty name =
  let name  = EcIdent.create name in
  let env   =
    { env_scope = Pident name;
      env_root  = { emcomponents with
                      mc_components = IM.add name () IM.empty };
      env_comps = Mid.add name (Pident name, emcomponents) Mid.empty }
  in
    (name, env)

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

  let mc_of_theory_item path (env, mc) = function 
    | Th_type     (id, td) -> env, mc_bind_typedecl (EcPath.Pqname (path, id)) td mc
    | Th_operator (id, op) -> env, mc_bind_op (EcPath.Pqname (path, id)) op mc
    | Th_axiom    (id, ax) -> env, mc_bind_ax (EcPath.Pqname (path, id)) ax mc
    | Th_modtype  (id, tm) -> env, mc_bind_modtype (EcPath.Pqname (path, id)) tm mc
    | Th_module   m        -> env, mc_bind_module (EcPath.Pqname (path, m.me_name)) m.me_sig mc
    | Th_theory   (id, th) -> env, mc_bind_theory (EcPath.Pqname (path, id)) th mc

  let mc_of_theory (env : env) (name : EcIdent.t) (theory : theory) =
    List.fold_left
      (mc_of_theory_item (EcPath.Pqname (env.env_scope, name)))
      (env, emcomponents)
      theory

  (* ------------------------------------------------------------------ *)
  let bind env binder name obj =
    let path   = EcPath.Pqname (env.env_scope, name) in
    let xcomps = EcPath.basename env.env_scope in

    { env with
      env_root  = binder path obj env.env_root;
      env_comps = 
      Mid.change (fun o -> omap o (snd_map (binder path obj)))
        xcomps env.env_comps ; }


  (* -------------------------------------------------------------------- *)
  let bind_mc env name comps =
    let path = EcPath.Pqname (env.env_scope, name) in
    let env  =
      { env with
        env_root  = mc_bind_comp path env.env_root;
        env_comps = 
        Mid.change (fun o -> omap o  (snd_map (mc_bind_comp path)))
          name env.env_comps; }
    in
    { env with                        (* FIXME: dup *)
      env_comps = Mid.add name (path, comps) env.env_comps }

  (* ------------------------------------------------------------------ *)
  let bind_variable x ty env =
    bind env mc_bind_variable x ty

  let bind_function x fsig env =
    bind env mc_bind_function x fsig

  let bind_module x tymod env =
    let comps = mc_of_module env tymod in
    let env   = bind env mc_bind_module x tymod in
    let env   = bind_mc env x comps in
      env

  let bind_modtype x tymod env =
    bind env mc_bind_modtype x tymod

  let bind_typedecl x tydecl env =
    bind env mc_bind_typedecl x tydecl

  let bind_op x op env =
    bind env mc_bind_op x op

  let bind_ax x ax env =
    bind env mc_bind_ax x ax

  let bind_theory x th env =
    let env, comps = mc_of_theory env x th in
    let env = bind env mc_bind_theory x th in
    let env = bind_mc env x comps in
      env
end

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
    let bind = MC.bind_typedecl
  end)

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
    let bind = MC.bind_op
  end)

  let all (qname : qsymbol) (env : env) =
    MC.lookupall (fun mc -> mc.mc_operators) qname env
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  include BaseS(struct
    type t = axiom

    let project mc = mc.mc_axioms
    let bind = MC.bind_ax
  end)
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  include BaseS(struct
    type t = tymod

    let project mc = mc.mc_modules
    let bind = MC.bind_module
  end)
end

(* -------------------------------------------------------------------- *)
module ModTy = struct
  include BaseS(struct
    type t = tymod

    let project mc = mc.mc_modtypes
    let bind = MC.bind_modtype
  end)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  include BaseS(struct
    type t = theory

    let project mc = mc.mc_theories
    let bind = MC.bind_theory
  end)

  (* FIXME *)
  let import (qs : qsymbol) (env : env) =
    env
(*
    let path, _ = lookup qs env in
    let mc1 = env.env_root in
    let mc2 = Lazy.force (MC.lookup_by_path (fun mc -> mc.mc_components)
                            (EcPath.Pident (EcPath.basename path)) env) in
    let mc = 
      { mc_variables  = IM.merge mc1.mc_variables mc2.mc_variables;
        mc_functions  = IM.merge mc1.mc_functions mc2.mc_functions;
        mc_modules    = IM.merge mc1.mc_modules mc2.mc_modules;
        mc_modtypes   = IM.merge mc1.mc_modtypes mc2.mc_modtypes;
        mc_typedecls  = IM.merge mc1.mc_typedecls mc2.mc_typedecls;
        mc_operators  = IM.merge mc1.mc_operators mc2.mc_operators;
        mc_axioms     = IM.merge mc1.mc_axioms mc2.mc_axioms;
        mc_theories   = IM.merge mc1.mc_theories mc2.mc_theories;
        mc_components = IM.merge mc1.mc_components mc2.mc_components;
        mc_history    = (path, MC_Import path) :: mc1.mc_history } in
    { env with env_root = mc }
*)
end

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of EcTypes.ty
  | `Function  of funsig
  | `Operator  of operator
  | `Module    of tymod
  | `ModType   of tymod
  | `TypeDecl  of tydecl
  | `Theory    of theory
]

let bind1 ((x, eb) : EcIdent.t * ebinding) (env : env) =
  match eb with
  | `Variable ty -> Var   .bind x ty env
  | `Function f  -> Fun   .bind x f  env
  | `Operator o  -> Op    .bind x o  env
  | `Module   m  -> Mod   .bind x m  env
  | `ModType  i  -> ModTy .bind x i  env
  | `TypeDecl t  -> Ty    .bind x t  env
  | `Theory   t  -> Theory.bind x t  env

let bindall (items : (EcIdent.t * ebinding) list) (env : env) =
  List.fold_left ((^~) bind1) env items

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
