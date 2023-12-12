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
type aexpr_ =
  | ECast of aexpr * atype
  | EVar of ident
  | EInt of int
  | ESlide of aexpr * (aexpr * int * int)
  | EMap of (aword * aword) * (aargs * aexpr)
  | EConcat of aword * aexpr list
  | ERepeat of aword * (aexpr * int)
  | EShift of [ `L | `R ] * [ `L | `A ] * aexpr * int
  | ESat of [ `U | `S ] * aexpr * int
  | ELet of (ident * aexpr) * aexpr
  | EAdd of aword * (aexpr * aexpr)
  | ESub of aword * (aexpr * aexpr)
  | EOr of aword * (aexpr * aexpr)
  | EAnd of aword * (aexpr * aexpr)
  | EMul of aword * (aexpr * aexpr)

and aexpr = { node : aexpr_; type_ : atype }

(* -------------------------------------------------------------------- *)
type adef = { arguments : aargs; body : aexpr; rettype : aword }

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
let rec tt_expr_ (env : env) (e : pexpr) : aexpr =
  match e with
  | PEParens e -> tt_expr env e
  | PEInt i -> { node = EInt i; type_ = `Unsigned; }
  | PECast (t, e) ->
      let tt = tt_type t in
      let { node = ne; type_= te} = tt_expr env e in

      check_cast ~from:te ~to_:tt;
      { node = ECast ({ node = ne; type_ = te}, tt); type_ = tt; }
  (* functions are, for now, type equivalent to their return type *)
  | PEFun (args, body) ->
      let ebody, args = tt_args env args in
      tt_expr ebody body
  | PEVar v ->
      let (vid, vt) = Option.get_exn
        (Env.lookup env v)
        (mk_tyerror "unknown variable: %s" v) in
      { node = EVar vid; type_ = vt; }
  | PELet ((v, e1), e2) ->
      let { node = nld; type_ =  tld; } as nld_ = tt_expr env e1 in
      let ebody, _ = Env.push env v tld in
      let { node = nlb; type_ =  tlb; } as nlb_ = tt_expr ebody e2 in
      let vid = Option.get_exn
      (Option.map fst (Env.lookup env v))
      (mk_tyerror "unknown variable: %s" v) in
      { node = ELet ((vid, nld_), nlb_); type_ = tlb; }
  (* Slices only accept eic and eil being fixed integers            *)
  | PESlice (ev, (eib, eic, eil)) ->
      let { node = ne; type_ = te; } as ne_ = tt_expr env ev in
      (* This should be a word *)
      let { node = neb; type_ = teb;} as neb_ = tt_expr env ~check:`Unsigned eib in
      let c = as_int_constant eic in
      let l = Option.default 1 (Option.map as_int_constant eil) in
      { node = ESlide (ne_,(neb_,c,l)); type_ = `W (c * l);} (* might be typo in AST, Slide -> Slice, check *)
  | PEApp ((("and" | "or" | "add" | "sub") as op, w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let (na1, na2) = as_seq2 (tt_exprs env ~expected:[ `W w; `W w ] args) in
      { node = (match op with
        | "and" -> EAnd (`W w, (na1, na2))
        | "or"  -> EOr  (`W w, (na1, na2))
        | "add" -> EAdd (`W w, (na1, na2))
        | "sub" -> ESub (`W w, (na1, na2)));
        type_ = `W w; }
  | PEApp (("mult", w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let (na1, na2) = as_seq2 (tt_exprs env ~expected:[ `W w; `W w ] args) in
      { node = EMul (`W (2 * w), (na1, na2)); type_ = `W (2 * w); }
  (* Implementing as implied by AST: Fixed shifts only *)
  | PEApp ((("sla" | "sll" | "sra" | "srl") as op, w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let (e1, e2) = as_seq2 args in
      let na = tt_expr env ~check:(`W w) e1 in
      let c = as_int_constant e2 in
      { node = (match op with 
        | "sla" -> EShift (`L,`A, na, c)
        | "sll" -> EShift (`L,`L, na, c)
        | "sra" -> EShift (`R,`A, na, c)
        | "srl" -> EShift (`R,`L, na, c));
        type_ = `W w; }
  | PEApp (("concat", w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let targs = List.map (tt_expr env ~check:(`W w)) args in
      let wsz = `W (w * List.length targs) in
      { node = EConcat (wsz, targs); type_ = wsz; }
  | PEApp (("repeat", w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let e, n = as_seq2 (check_arguments_count ~expected:2 args) in
      let n = as_int_constant n in
      let ne = tt_expr env ~check:(`W w) e in
      { node = ERepeat (`W (w * n),(ne,n)); type_ = `W (w * n); }
  | PEApp ((("SatToUW" | "SatToSW") as op, w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let e, n = as_seq2 (check_arguments_count ~expected:2 args) in
      let n = as_int_constant n in
      let ne = tt_expr env ~check:(`W w) e in
      { 
        node = (match op with
        | "SatToUW" -> ESat (`U, ne, n)
        | "SatToSW" -> ESat (`S, ne, n));
        type_ = `W w; 
      }
  | PEApp (("map", w), args) -> failwith "Not yet done"
  (*
      let `W w, `W n = as_seq2 (tt_type_parameters ~expected:2 w) in

      if List.is_empty args then tyerror "invalid number of arguments";

      let f, args = (List.hd args, List.tl args) in
      let _ = List.map (tt_expr ~check:(`W (w * n)) env) args in

      let fargs, f = destruct_fun f in

      let env, targs = tt_args env fargs in
      let targs = List.map snd targs in

      if targs <> List.make (List.length args) (`W w) then
        tyerror "invalid argument types / count";

      let (nf, tf) = tt_expr env f in
      let m =
        match tf with
        | `W m -> m
        | _ -> tyerror "function should return a word"
      in

      (EMap ((`W w, `W n) , ( ,nf)), `W (m * n))
      *)
  | PEApp ((name, _), _) -> tyerror "Unknown combinator: %s" name

(* -------------------------------------------------------------------- *)
and tt_expr (env : env) ?(check : atype option) (p : pexpr) : aexpr =
    let {node = n_; type_ = t;} = tt_expr_ env p in

  Option.may
    (fun t' ->
      if not (can_promote ~from:t ~to_:t') then
        tyerror "invalid type: %a / %a" pp_atype t pp_atype t')
    check;
  {node = n_; type_ = Option.default t check; }

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
let tt_def (env : env) (p : pdef) : symbol * adef =
  Format.eprintf "%s@." p.name;
  let env, args = tt_args env p.args in
  let bod = tt_expr env ~check:(tt_pword env p.rty) p.body in
  (p.name, { arguments = args; body = bod; rettype = p.rty; })

(* -------------------------------------------------------------------- *)
let tt_program (env : env) (p : pprogram) : (symbol * adef) list =
  List.map (tt_def env) p
