(* -------------------------------------------------------------------- *)
open Ptree

(* -------------------------------------------------------------------- *)
module Ident : sig
  type ident

  val create : string -> ident

  val name : ident -> string
end = struct
  type ident = symbol * int

  let create (x : string) : ident =
    (x, 0)

  let name ((x, _) : ident) : string =
    x
end

(* -------------------------------------------------------------------- *)
type ident = Ident.ident

(* -------------------------------------------------------------------- *)
type aword =
  | W of int

(* -------------------------------------------------------------------- *)
type atype =
  | W of int
  | Signed
  | Unsigned

(* -------------------------------------------------------------------- *)
type aarg =
  ident * aword

(* -------------------------------------------------------------------- *)
type aargs =
  aarg list

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty : env

  val lookup : env -> symbol -> (ident * atype) option

  val push : env -> symbol -> atype -> env * ident
end = struct
  type env = {
    vars : (symbol, ident * atype) Map.t;
  }

  let empty : env =
    { vars = Map.empty; }

  let lookup (env : env) (x : symbol) =
    Map.find_opt x env.vars

  let push (env : env) (x : symbol) (ty : atype) =
    let idx = Ident.create x in
    let env = { vars = Map.add x (idx, ty) env.vars } in
    (env, idx)
end

(* -------------------------------------------------------------------- *)
type env = Env.env

(* -------------------------------------------------------------------- *)
let tt_pword (_ : env) (W ty : pword) : atype =
  W ty

(* -------------------------------------------------------------------- *)
let rec tt_expr (env : env) ?(check : atype option) (e : pexpr) =
  match e with
  | PEParens _e ->
      tt_expr env ?check e

  | PEInt _i ->
      assert false

  | _ ->
     assert false

(* -------------------------------------------------------------------- *)
let tt_arg (env : env) ((x, W ty) : parg) : env * aarg =
  let env, idx = Env.push env x (W ty) in
  (env, (idx, W ty))

(* -------------------------------------------------------------------- *)
let tt_args (env : env) (args : pargs) : env * aargs =
  List.fold_left_map tt_arg env args

(* -------------------------------------------------------------------- *)
let tt_def (env : env) (p : pdef) =
  let _env, _args = tt_args env p.args in
  let _body = tt_expr env ~check:(tt_pword env p.rty) p.body in
  assert false

(* -------------------------------------------------------------------- *)
let tt_program (env : env) (p : pprogram) =
  List.fold_left_map tt_def env p
