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
  mc_components : (Path.path * mcomponents Lazy.t) Ident.Map.t;
}

exception LookupFailure

(* -------------------------------------------------------------------- *)
let empty =
  let emcomponents = {
    mc_variables  = Ident.Map.empty;
    mc_functions  = Ident.Map.empty;
    mc_modules    = Ident.Map.empty;
    mc_components = Ident.Map.empty;
  }

  in
    { env_scope = None;
      env_root  = emcomponents; }

(* -------------------------------------------------------------------- *)
module MC = struct
  let mc_of_module (_env : env) (_ : tymod) =
    lazy (failwith "")

  let bind_variable (scope, x) ty _env mc =
    { mc with
        mc_variables = Ident.Map.add x (in_scope scope x, ty) mc.mc_variables; }

  let bind_function (scope, x) fsig _env mc =
    { mc with
        mc_functions = Ident.Map.add x (in_scope scope x, fsig) mc.mc_functions; }

  let bind_module (scope, x) tymod env mc =
    let comps = mc_of_module env tymod in
      { mc with
          mc_modules    = Ident.Map.add x (in_scope scope x, tymod) mc.mc_modules;
          mc_components = Ident.Map.add x (in_scope scope x, comps) mc.mc_components; }

  let lookup_mc1 (name : symbol) (mc : mcomponents) =
    Ident.Map.byname name mc.mc_components

  let lookup_variable1 (name : symbol) (mc : mcomponents) =
    Ident.Map.byname name mc.mc_variables

  let lookup_function1 (name : symbol) (mc : mcomponents) =
    Ident.Map.byname name mc.mc_functions

  let lookup_module1 (name : symbol) (mc : mcomponents) =
    Ident.Map.byname name mc.mc_modules

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
let bind_variable x ty env =
  bind MC.bind_variable x ty env

let bind_variables xtys env =
  List.fold_left
    (fun env (x, ty) -> bind_variable x ty env)
    env xtys

(* -------------------------------------------------------------------- *)
let bind_function x fsig env =
  bind MC.bind_function x fsig env

let bind_functions xtys env =
  List.fold_left
    (fun env (x, ty) -> bind_function x ty env)
    env xtys

(* -------------------------------------------------------------------- *)
let bind_module x tymod env =
  bind MC.bind_module x tymod env

let bind_modules xtys env =
  List.fold_left
    (fun env (x, tymod) -> bind_module x tymod env)
    env xtys

(* -------------------------------------------------------------------- *)
let lookup_mcomponents ((scope, id) : qsymbol) (env : env) =
  obind
    (MC.lookup_mc scope env.env_root)
    (MC.lookup_mc1 id)

(* -------------------------------------------------------------------- *)
let lookup_variable ((scope, id) : qsymbol) (env : env) =
  match
    obind
      (MC.lookup_mc scope env.env_root)
      (MC.lookup_variable1 id)
  with
  | None   -> raise LookupFailure
  | Some x -> x

(* -------------------------------------------------------------------- *)
let lookup_function ((scope, id) : qsymbol) (env : env) =
  match
    obind
      (MC.lookup_mc scope env.env_root)
      (MC.lookup_function1 id)
  with
  | None   -> raise LookupFailure
  | Some x -> x

(* -------------------------------------------------------------------- *)
let lookup_module ((scope, id) : qsymbol) (env : env) =
  match
    obind
      (MC.lookup_mc scope env.env_root)
      (MC.lookup_module1 id)
  with
  | None   -> raise LookupFailure
  | Some x -> x

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of Types.ty
  | `Function  of funsig
  | `Module    of tymod
]

let bind1 ((x, eb) : Ident.t * ebinding) (env : env) =
  match eb with
  | `Variable ty -> bind_variable x ty env
  | `Function f  -> bind_function x f  env
  | `Module   m  -> bind_module   x m  env

let bindall (items : (Ident.t * ebinding) list) (env : env) =
  List.fold_left ((^~) bind1) env items
