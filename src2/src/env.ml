(* -------------------------------------------------------------------- *)
open Symbols

(* -------------------------------------------------------------------- *)
type env = {
  env_values  : Types.ty SymMap.t;
  env_modules : Typesmod.tymod SymMap.t
}

type ebinding = [
  | `Value  of Types.ty
  | `Module of Typesmod.tymod
]

(* -------------------------------------------------------------------- *)
let empty = {
  env_values  = SymMap.empty;
  env_modules = SymMap.empty;
}

let bind (x : symbol) (eb : ebinding) (env : env) =
  match eb with
    | `Value  ty  -> { env with env_values  = SymMap.add x ty  env.env_values }
    | `Module mty -> { env with env_modules = SymMap.add x mty env.env_modules }

let bindall ebindings env =
  List.fold_left
    (fun env (x, eb) -> bind x eb env) env ebindings

(* -------------------------------------------------------------------- *)
let bind_value x ty env = bind x (`Value ty) env

let bind_values xtys env =
  List.fold_left (fun env (x, ty) -> bind_value x ty env) env xtys

(* -------------------------------------------------------------------- *)
let bind_module x tymod env = bind x (`Module tymod) env

let bind_modules xmods env =
  List.fold_left (fun env (x, tymod) -> bind_module x tymod env) env xmods

(* -------------------------------------------------------------------- *)
let lookup_module (id : qsymbol) (env : env) =
  assert false

let lookup_value (id : qsymbol) (env : env) =
  assert false
