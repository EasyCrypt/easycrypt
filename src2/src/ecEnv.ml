(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcTypesmod

(* -------------------------------------------------------------------- *)
type scope = EcPath.path option

let in_scope (s : scope) (x : EcIdent.t) =
  match s with
  | None   -> Pident x
  | Some s -> Pqname (s, x)

type env = {
  env_scope : EcPath.path option;
  env_root  : mcomponents;
}

and mcomponents = {
  mc_variables  : (EcPath.path * EcTypes.ty)           EcIdent.Map.t;
  mc_functions  : (EcPath.path * EcTypesmod.funsig)    EcIdent.Map.t;
  mc_modules    : (EcPath.path * EcTypesmod.tymod)     EcIdent.Map.t;
  mc_modtypes   : (EcPath.path * EcTypesmod.tymod)     EcIdent.Map.t;
  mc_typedecls  : (EcPath.path * EcTypesmod.tydecl)    EcIdent.Map.t;
  mc_operators  : (EcPath.path * EcTypesmod.operator)  EcIdent.Map.t;
  mc_axioms     : (EcPath.path * EcTypesmod.axiom)     EcIdent.Map.t;
  mc_theories   : (EcPath.path * EcTypesmod.theory)    EcIdent.Map.t;
  mc_components : (EcPath.path * mcomponents Lazy.t)   EcIdent.Map.t;
}

(* -------------------------------------------------------------------- *)
let empty =
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

  in
    { env_scope = None;
      env_root  = emcomponents; }

(* -------------------------------------------------------------------- *)
let root (env : env) = env.env_scope

(* -------------------------------------------------------------------- *)
let enter (name : symbol) (env : env) =
  let name = EcIdent.create name in
  let path =
    match env.env_scope with
    | None   -> EcPath.Pident name
    | Some p -> EcPath.Pqname (p, name)
  in
    (name, { env with env_scope = Some path })

(* -------------------------------------------------------------------- *)
exception LookupFailure

let try_lf (f : unit -> 'a) =
  try Some (f ()) with LookupFailure _ -> None

(* -------------------------------------------------------------------- *)
module type S = sig
  type t

  val bind      : EcIdent.t -> t -> env -> env
  val bindall   : (EcIdent.t * t) list -> env -> env
  val lookup    : qsymbol -> env -> EcPath.path * t
  val trylookup : qsymbol -> env -> (EcPath.path * t) option
end

(* -------------------------------------------------------------------- *)
module MC = struct
  module IM = EcIdent.Map

  let mc_of_module (_env : env) (_ : tymod) =
    lazy (failwith "")

  let bind_variable (scope, x) ty _env mc =
    { mc with
        mc_variables = IM.add x (in_scope scope x, ty) mc.mc_variables; }

  let bind_function (scope, x) fsig _env mc =
    { mc with
        mc_functions = IM.add x (in_scope scope x, fsig) mc.mc_functions; }

  let bind_module (scope, x) tymod env mc =
    let comps = mc_of_module env tymod in
      { mc with
          mc_modules    = IM.add x (in_scope scope x, tymod) mc.mc_modules;
          mc_components = IM.add x (in_scope scope x, comps) mc.mc_components; }

  let bind_modtype (scope, x) tymod env mc =
    { mc with
        mc_modtypes = IM.add x (in_scope scope x, tymod) mc.mc_modtypes; }

  let bind_typedecl (scope, x) tydecl env mc =
    { mc with
        mc_typedecls = IM.add x (in_scope scope x, tydecl) mc.mc_typedecls; }

  let bind_op (scope, x) tydecl env mc =
    { mc with
        mc_operators = IM.add x (in_scope scope x, tydecl) mc.mc_operators; }

  let bind_ax (scope, x) opdecl env mc =
    { mc with
        mc_axioms = IM.add x (in_scope scope x, opdecl) mc.mc_axioms; }

  let bind_theory (scope, x) th env mc =
    { mc with
        mc_theories = IM.add x (in_scope scope x, th) mc.mc_theories; }

  let lookup_mc1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_components

  let lookup_variable1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_variables

  let lookup_function1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_functions

  let lookup_module1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_modules

  let lookup_modtype1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_modtypes

  let lookup_typedecl1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_typedecls

  let lookup_op1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_operators

  let lookup_ax1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_axioms

  let lookup_theory1 (name : symbol) (mc : mcomponents) =
    IM.byname name mc.mc_theories

  let rec lookup_mc (qn : symbols) (mc : mcomponents) =
    match qn with
    | []         -> Some mc
    | name :: qn ->
        obind
          (lookup_mc1 name mc)
          (fun (_, mc) -> lookup_mc qn (Lazy.force mc))
end

(* -------------------------------------------------------------------- *)
let bind f x v env =
  { env with env_root = f (env.env_scope, x) v env env.env_root }

(* -------------------------------------------------------------------- *)
let lookup_mcomponents ((scope, id) : qsymbol) (env : env) =
  obind
    (MC.lookup_mc scope env.env_root)
    (MC.lookup_mc1 id)

(* -------------------------------------------------------------------- *)
module Var = struct
  type t = EcTypes.ty

  let bind x ty env =
    bind MC.bind_variable x ty env

  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_variable1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
end

(* -------------------------------------------------------------------- *)
module Fun = struct
  type  t = funsig

  let bind x fsig env =
    bind MC.bind_function x fsig env

  let bindall xtys env =
    List.fold_left
      (fun env (x, ty) -> bind x ty env)
      env xtys

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
      (MC.lookup_function1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
end

(* -------------------------------------------------------------------- *)
module Ty = struct
  type t = tydecl

  let bind x tydecl env =
    bind MC.bind_typedecl x tydecl env

  let bindall xtys env =
    List.fold_left
      (fun env (x, tydecl) -> bind x tydecl env)
      env xtys

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_typedecl1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)

  let defined (name : EcPath.path) (env : env) = (* FIXME: lookup for paths *)
    match trylookup (EcPath.toqsymbol name) env with
    | None -> false
    | Some (_, tydecl) -> tydecl.tyd_type <> None

  let unfold (name : EcPath.path) (args : EcTypes.ty Parray.t) (env : env) =
    match trylookup (EcPath.toqsymbol name) env with (* FIXME: lookup for paths *)
    | None
    | Some (_, { tyd_type = None }) -> assert false
    | Some (_, ({ tyd_type = Some body } as tyd)) ->
        assert (tyd.tyd_params = Parray.length args);
        EcTypes.full_inst_rel args body
end

(* -------------------------------------------------------------------- *)
module Op = struct
  type t = operator

  let bind x operator env =
    bind MC.bind_op x operator env

  let bindall ops env =
    List.fold_left
      (fun env (x, tydecl) -> bind x tydecl env)
      env ops

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_op1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  type t = axiom

  let bind x axiom env =
    bind MC.bind_ax x axiom env

  let bindall axs env =
    List.fold_left
      (fun env (x, ax) -> bind x ax env)
      env axs

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_ax1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
end




(* -------------------------------------------------------------------- *)
module Mod = struct
  type t = tymod

  let bind x tymod env =
    bind MC.bind_module x tymod env

  let bindall xtys env =
    List.fold_left
      (fun env (x, tymod) -> bind x tymod env)
      env xtys

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_module1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
end

(* -------------------------------------------------------------------- *)
module ModTy = struct
  type t = tymod

  let bind x tymod env =
    bind MC.bind_modtype x tymod env

  let bindall xtys env =
    List.fold_left
      (fun env (x, tymod) -> bind x tymod env)
      env xtys

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_modtype1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  type t = theory

  let bind x th env =
    bind MC.bind_theory x th env

  let bindall xtys env =
    List.fold_left
      (fun env (x, tymod) -> bind x tymod env)
      env xtys

  let lookup ((scope, id) : qsymbol) (env : env) =
    match
      obind
        (MC.lookup_mc scope env.env_root)
        (MC.lookup_theory1 id)
    with
    | None   -> raise LookupFailure
    | Some x -> x

  let trylookup x env = try_lf (fun () -> lookup x env)
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
  let trylookup (name : qsymbol) (env : env) =
    let for_var () =
      match Var.trylookup name env with
      | None -> None
      | Some (p, ty) -> Some (p, ty, (`Var :> [`Var | `Ctnt]))

    and for_op () =
      match Op.trylookup name env with
      | None -> None
      | Some (_, op) when not op.op_ctnt -> None
      | Some (p, op) -> Some (p, snd op.op_sig, (`Ctnt :> [`Var | `Ctnt]))
    in
      List.fpick [for_var; for_op]

  let lookup (name : qsymbol) (env : env) =
    match trylookup name env with
    | None   -> raise LookupFailure
    | Some x -> x
end
