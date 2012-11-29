(* -------------------------------------------------------------------- *)
open Utils
open Symbols
open Path
open Typesmod

(* -------------------------------------------------------------------- *)
type scope = Path.path option

let in_scope (s : scope) (x : Ident.t) =
  match s with
  | None   -> Pident x
  | Some s -> Pqname (s, x)

type env = {
  env_scope : Path.path option;
  env_root  : mcomponents;
}

and mcomponents = {
  mc_variables  : (Path.path * Types.ty)           Ident.Map.t;
  mc_functions  : (Path.path * Typesmod.funsig)    Ident.Map.t;
  mc_modules    : (Path.path * Typesmod.tymod)     Ident.Map.t;
  mc_modtypes   : (Path.path * Typesmod.tymod)     Ident.Map.t;
  mc_typedecls  : (Path.path * Typesmod.tydecl)    Ident.Map.t;
  mc_operators  : (Path.path * Typesmod.operator)  Ident.Map.t;
  mc_components : (Path.path * mcomponents Lazy.t) Ident.Map.t;
}

(* -------------------------------------------------------------------- *)
let empty =
  let emcomponents = {
    mc_variables  = Ident.Map.empty;
    mc_functions  = Ident.Map.empty;
    mc_modules    = Ident.Map.empty;
    mc_modtypes   = Ident.Map.empty;
    mc_typedecls  = Ident.Map.empty;
    mc_operators  = Ident.Map.empty;
    mc_components = Ident.Map.empty;
  }

  in
    { env_scope = None;
      env_root  = emcomponents; }

(* -------------------------------------------------------------------- *)
exception LookupFailure

let try_lf (f : unit -> 'a) =
  try Some (f ()) with LookupFailure _ -> None

(* -------------------------------------------------------------------- *)
module type S = sig
  type t

  val bind      : Ident.t -> t -> env -> env
  val bindall   : (Ident.t * t) list -> env -> env
  val lookup    : qsymbol -> env -> Path.path * t
  val trylookup : qsymbol -> env -> (Path.path * t) option
end

(* -------------------------------------------------------------------- *)
module MC = struct
  module IM = Ident.Map

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
  type t = Types.ty

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
type ebinding = [
  | `Variable  of Types.ty
  | `Function  of funsig
  | `Module    of tymod
]

let bind1 ((x, eb) : Ident.t * ebinding) (env : env) =
  match eb with
  | `Variable ty -> Var.bind x ty env
  | `Function f  -> Fun.bind x f  env
  | `Module   m  -> Mod.bind x m  env

let bindall (items : (Ident.t * ebinding) list) (env : env) =
  List.fold_left ((^~) bind1) env items
