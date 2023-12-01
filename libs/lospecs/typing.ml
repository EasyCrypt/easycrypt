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
  | Word of int
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
  Word ty

(* -------------------------------------------------------------------- *)
let tt_arg (env : env) ((x, W ty) : parg) : env * aarg =
  let env, idx = Env.push env x (Word ty) in
  (env, (idx, W ty))

(* -------------------------------------------------------------------- *)
let tt_args (env : env) (args : pargs) : env * aargs =
  List.fold_left_map tt_arg env args

(* -------------------------------------------------------------------- *)
(* Get type of expr, fail if different from check (if check is given)   *)
let rec tt_expr (env : env) ?(check : atype option) (e : pexpr) : env * atype =
  match e with
  | PEParens _e ->
      tt_expr env ?check _e

  (* defaults to unsigned *)
  | PEInt _i ->
      (env, Unsigned)

  (* will need to add typecast compatibility check, unnecessary for now *)
  (* TODO: Make types compatible across files*)
  | PECast (t, _e) -> let t = (match t with 
                                | Ptree.Word x -> Word x
                                | Ptree.Unsigned -> Unsigned
                                | Ptree.Signed -> Signed)
                 in  (match check with
                      | Some _t -> if t = _t then (env, t) else failwith "Bad typecast"
                      | None -> (env, t)  )

  (* to be changed later when introducing more types, such as function types *)
  (* for now, anonymous functions have type equal to their return type *)
  | PEFun (_args, _e) -> let _env, _args = tt_args env _args in  
                            tt_expr _env ?check _e
  | PELet ((v, _e1), _e2) -> let _env, _ = (let _, _t = tt_expr env _e1 
                                            in Env.push env v _t)
                             in tt_expr _env ?check _e2
  (* TODO: add bounds checking? maybe change slice notation to allow for easier parsing 
           when beginning is variable but length is fixed *)
  (* slice is also short circuiting all checks right now *)
  | PESlice (_ev, (_eib, _eie, _eis)) -> let _, _tv = tt_expr env _ev in
                                       let _, _tib = tt_expr env _eib in
                                       let _, _tie = tt_expr env _eie in
                                       (match _eis with 
                                       | Some _eis -> let _, _tis = tt_expr env _eis 
                                                      in (env, _tv) (* temp solution *)
                                       | None -> (env, _tv)   )  
                     
  (* needs function types to actually make sense for now just gets an unsigned integer *)
  (* TODO: Implement function types so this makes sense *)
  | PEApp (_fn, _el) -> (env, Unsigned)

  | _ ->
      assert false

(* -------------------------------------------------------------------- *)
let tt_def_arg (env : env) ((x, W ty) : parg) : env * aarg =
  let env, idx = Env.push env x (Word ty) in
  (env, (idx, W ty))

(* -------------------------------------------------------------------- *)
let tt_def_args (env : env) (args : pargs) : env * aargs =
  List.fold_left_map tt_def_arg env args

(* -------------------------------------------------------------------- *)
let tt_def (env : env) (p : pdef) : env * (symbol * atype) =
  let _env, _args = tt_def_args env p.args in
  let _benv, _btype = tt_expr env ~check:(tt_pword env p.rty) p.body in
  (_benv, (p.name, _btype))

(* -------------------------------------------------------------------- *)
let tt_program (env : env) (p : pprogram) : env * (symbol * atype) list =
  List.fold_left_map tt_def env p
