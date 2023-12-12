(* -------------------------------------------------------------------- *)
open Ptree

(* -------------------------------------------------------------------- *)
let as_seq1 (type t) (xs : t list) : t =
  match xs with [ x ] -> x | _ -> assert false

(* -------------------------------------------------------------------- *)
let as_seq2 (type t) (xs : t list) : t * t =
  match xs with [ x; y ] -> (x, y) | _ -> assert false

(* -------------------------------------------------------------------- *)
module Ident : sig
  type ident

  val create : string -> ident
  val name : ident -> string
  val id : ident -> int
end = struct
  type ident = symbol * int

  let create (x : string) : ident = (x, Oo.id (object end))
  let name ((x, _) : ident) : string = x
  let id ((_, i) : ident) : int = i
end

(* -------------------------------------------------------------------- *)
type ident = Ident.ident

(* -------------------------------------------------------------------- *)
type aword = [ `W of int ] [@@deriving show]

(* -------------------------------------------------------------------- *)
type atype = [ aword | `Signed | `Unsigned ] [@@deriving show]

(* -------------------------------------------------------------------- *)
type aarg = ident * aword

(* -------------------------------------------------------------------- *)
type aargs = aarg list

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty : env
  val lookup : env -> symbol -> (ident * atype) option
  val push : env -> symbol -> atype -> env * ident
  val export : env -> (symbol, ident * atype) Map.t
end = struct
  type env = { vars : (symbol, ident * atype) Map.t }

  let empty : env = { vars = Map.empty }
  let lookup (env : env) (x : symbol) = Map.find_opt x env.vars

  let push (env : env) (x : symbol) (ty : atype) =
    let idx = Ident.create x in
    let env = { vars = Map.add x (idx, ty) env.vars } in
    (env, idx)

  let export (env : env) : (symbol, ident * atype) Map.t = env.vars
end

(* -------------------------------------------------------------------- *)
type env = Env.env

(* -------------------------------------------------------------------- *)
let tt_pword (_ : env) (`W ty : pword) : atype = `W ty

(* -------------------------------------------------------------------- *)
exception TypingError of string

(* -------------------------------------------------------------------- *)
let mk_tyerror_r f msg =
  let buf = Buffer.create 0 in
  let fbuf = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush fbuf ();
      f (TypingError (Buffer.contents buf)))
    fbuf msg

(* -------------------------------------------------------------------- *)
let mk_tyerror msg = mk_tyerror_r identity msg

(* -------------------------------------------------------------------- *)
let tyerror msg = mk_tyerror_r (fun e -> raise e) msg

(* -------------------------------------------------------------------- *)
let tt_type (t : ptype) : atype = (t :> atype)

(* -------------------------------------------------------------------- *)
let check_cast ~(from : atype) ~(to_ : atype) =
  match (from, to_) with
  | `W _, (`Unsigned | `Signed) -> ()
  | _, _ when from = to_ -> ()
  | _, _ -> tyerror "invalid cast"

(* -------------------------------------------------------------------- *)
let can_promote ~(from : atype) ~(to_ : atype) =
  match (from, to_) with
  | (`Unsigned | `Signed), `W _ -> true
  | _, _ -> from = to_

(* -------------------------------------------------------------------- *)
let atype_as_aword (t : atype) : aword =
  match t with #aword as t -> t | _ -> tyerror "word type expected"

(* -------------------------------------------------------------------- *)
let tt_type_parameters ~(expected : int) (tp : pword list option) =
  match tp with
  | None -> tyerror "missing type parameters annotation"
  | Some tp ->
      let tplen = List.length tp in
      if expected <> tplen then
        tyerror "invalid number of type parameters: %d / %d" tplen expected;
      (tp :> aword list)

(* -------------------------------------------------------------------- *)
let check_arguments_count ~(expected : int) (args : pexpr list) =
  if List.length args <> expected then tyerror "invalid number of arguments";
  args

(* -------------------------------------------------------------------- *)
let as_int_constant (e : pexpr) : int =
  match e with PEInt i -> i | _ -> tyerror "integer constant expected"

(* -------------------------------------------------------------------- *)
let destruct_fun (e : pexpr) : pargs * pexpr =
  let rec doit (acc : pargs) (e : pexpr) =
    match e with
    | PEFun (args, e) -> doit (List.rev_append args acc) e
    | _ -> (List.rev acc, e)
  in
  doit [] e

(* -------------------------------------------------------------------- *)
(* Get type of expr, fail if different from check (if check is given)   *)
let rec tt_expr_ (env : env) (e : pexpr) : atype =
  match e with
  | PEParens e -> tt_expr env e
  | PEInt i -> `Unsigned
  | PECast (t, e) ->
      let tt = tt_type t in
      let te = tt_expr env e in

      check_cast ~from:te ~to_:tt;
      tt
  (* FIXME: to be changed later when introducing more types, such as
     function types for now, anonymous functions have type equal to
     their return type *)
  | PEFun (args, body) ->
      let ebody, args = tt_args env args in
      tt_expr ebody body
  | PEVar v ->
      Option.get_exn
        (Option.map snd (Env.lookup env v))
        (mk_tyerror "unknown variable: %s" v)
  | PELet ((v, e1), e2) ->
      let ebody, _ = Env.push env v (tt_expr env e1) in
      tt_expr ebody e2
  (* TODO: add bounds checking? maybe change slice notation to allow for easier parsing *)
  (*       when beginning is variable but length is fixed                               *)
  (* slice is also short circuiting all checks right now                                *)
  (* [a:b] = [a:b:1].     [a:b:c] = starting from a, get c bits b times                 *)
  (* If resulting word length is fixed then return Word of that size                    *)
  (* Otherwise return type of thing being sliced                                        *)
  | PESlice (ev, (eib, eic, eil)) ->
      let _ = tt_expr env ev in
      (* This should be a word *)
      let _ = tt_expr env ~check:`Unsigned eib in
      let c = as_int_constant eic in
      let l = Option.default 1 (Option.map as_int_constant eil) in

      `W (c * l)
  | PEApp ((("and" | "or" | "add" | "sub"), w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let _ = tt_exprs env ~expected:[ `W w; `W w ] args in
      `W w
  | PEApp (("mult", w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let _ = tt_exprs env ~expected:[ `W w; `W w ] args in
      `W (2 * w)
  | PEApp ((("sla" | "sll" | "sra" | "srl"), w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let _ = tt_exprs env ~expected:[ `W w; `W w ] args in
      `W w
  | PEApp (("concat", w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let targs = List.map (tt_expr env ~check:(`W w)) args in
      `W (w * List.length targs)
  | PEApp (("repeat", w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let e, n = as_seq2 (check_arguments_count ~expected:2 args) in
      let n = as_int_constant n in
      let _ = tt_expr env ~check:(`W w) e in
      `W (w * n)
  | PEApp ((("SatToUW" | "SatToSW"), w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let e, n = as_seq2 (check_arguments_count ~expected:2 args) in
      let _ = as_int_constant n in
      let _ = tt_expr env ~check:(`W w) e in
      `W w
  | PEApp (("map", w), args) ->
      let `W w, `W n = as_seq2 (tt_type_parameters ~expected:2 w) in

      if List.is_empty args then tyerror "invalid number of arguments";

      let f, args = (List.hd args, List.tl args) in
      let _ = List.map (tt_expr ~check:(`W (w * n)) env) args in

      let fargs, f = destruct_fun f in

      let env, targs = tt_args env fargs in
      let targs = List.map snd targs in

      if targs <> List.make (List.length args) (`W w) then
        tyerror "invalid argument types / count";

      let m =
        match tt_expr env f with
        | `W m -> m
        | _ -> tyerror "function should return a word"
      in

      `W (m * n)
  | PEApp ((name, _), _) -> tyerror "Unknown combinator: %s" name

(* -------------------------------------------------------------------- *)
and tt_expr (env : env) ?(check : atype option) (p : pexpr) =
  let t = tt_expr_ env p in

  Option.may
    (fun t' ->
      if not (can_promote ~from:t ~to_:t') then
        tyerror "invalid type: %a / %a" pp_atype t pp_atype t')
    check;
  Option.default t check

(* -------------------------------------------------------------------- *)
and tt_arg (env : env) ((x, `W ty) : parg) : env * aarg =
  let env, idx = Env.push env x (`W ty) in
  (env, (idx, `W ty))

(* -------------------------------------------------------------------- *)
and tt_args (env : env) (args : pargs) : env * aargs =
  List.fold_left_map tt_arg env args

(* -------------------------------------------------------------------- *)
and tt_exprs (env : env) ~(expected : atype list) (es : pexpr list) =
  let eslen = List.length es in
  let exlen = List.length expected in

  if eslen <> exlen then tyerror "invalid tuple size: %d / %d" exlen eslen;
  List.map2 (fun e t -> tt_expr env ~check:t e) es expected

(* -------------------------------------------------------------------- *)
let tt_def (env : env) (p : pdef) : symbol * atype =
  Format.eprintf "%s@." p.name;
  let env, args = tt_args env p.args in
  let type_ = tt_expr env ~check:(tt_pword env p.rty) p.body in
  (p.name, type_)

(* -------------------------------------------------------------------- *)
let tt_program (env : env) (p : pprogram) : (symbol * atype) list =
  List.map (tt_def env) p
