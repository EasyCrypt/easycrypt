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
  type ident [@@deriving yojson]

  val create : string -> ident
  val name : ident -> string
  val id : ident -> int
end = struct
  type ident = symbol * int
  [@@deriving yojson]

  let create (x : string) : ident = (x, Oo.id (object end))
  let name ((x, _) : ident) : string = x
  let id ((_, i) : ident) : int = i
end

(* -------------------------------------------------------------------- *)
type ident = Ident.ident [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type aword = [ `W of int ] [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type atype = [ aword | `Signed | `Unsigned ] [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type aarg = ident * aword [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type aargs = aarg list [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type lr = [`L | `R] [@@deriving yojson]
type la = [`L | `A] [@@deriving yojson]
type us = [`U | `S] [@@deriving yojson]
type hl = [`H | `L] [@@deriving yojson]
type hld = [hl | `D] [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type aexpr_ =
  | ECast of aexpr * atype
  | EVar of ident
  | EInt of int
  | ESlice of aexpr * (aexpr * int * int)
  | EApp of ident * aexpr list
  | EMap of (aword * aword) * (aargs * aexpr) * aexpr list
  | EConcat of aword * aexpr list
  | ERepeat of aword * (aexpr * int)
  | EShift of lr * la * aexpr * aexpr 
  | ESat of us * aword * aexpr
  | ELet of (ident * aargs option * aexpr) * aexpr
  | ENot of aword * aexpr
  | EIncr of aword * aexpr
  | EAdd of aword * bool * (aexpr * aexpr)
  | ESub of aword * (aexpr * aexpr)
  | EOr of aword * (aexpr * aexpr)
  | EAnd of aword * (aexpr * aexpr)
  | EMul of us * hld * aword * (aexpr * aexpr)
[@@deriving yojson]

and aexpr = { node : aexpr_; type_ : atype } [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type adef = { arguments : aargs; body : aexpr; rettype : aword } [@@deriving yojson]

(* -------------------------------------------------------------------- *)
let get_size (`W w : aword) : int =
  w

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  type sig_ = aword list option * atype

  val empty : env
  val lookup : env -> symbol -> (ident * sig_) option
  val push : env -> symbol -> sig_ -> env * ident
  val export : env -> (symbol, ident * sig_) Map.t
end = struct
  type sig_ = aword list option * atype

  type env = { vars : (symbol, ident * sig_) Map.t }

  let empty : env = { vars = Map.empty }

  let lookup (env : env) (x : symbol) = Map.find_opt x env.vars

  let push (env : env) (x : symbol) (sig_ : sig_) =
    let idx = Ident.create x in
    let env = { vars = Map.add x (idx, sig_) env.vars } in
    (env, idx)

  let export (env : env) : (symbol, ident * sig_) Map.t = env.vars
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
type sig_ = {
  s_name : string;
  s_ntyparams : int;
  s_argsty : aword list -> aword list;
  s_retty : aword list -> aword;
  s_mk : aword list -> aexpr list -> aexpr_;
}

(* -------------------------------------------------------------------- *)
module Sigs : sig
  val sla : sig_
  val sra : sig_
  val sll : sig_
  val srl : sig_
  val usat : sig_
  val ssat : sig_
  val not : sig_
  val incr : sig_
  val add : sig_
  val addc : sig_
  val sub : sig_
  val and_ : sig_
  val or_ : sig_
  val umul : sig_
  val umullo : sig_
  val umulhi : sig_
  val smul : sig_
  val smullo : sig_
  val smulhi : sig_
end = struct
  let mk1 (f : aexpr -> aexpr_) (a : aexpr list) =
    f (as_seq1 a)

  let mk2 (f : aexpr -> aexpr -> aexpr_) (a : aexpr list) =
    let x, y = as_seq2 a in f x y

  let uniop ?(ret = fun x -> x) ~(name : string) mk = {
    s_name = name;
    s_ntyparams = 1;
    s_argsty = (fun ws -> [as_seq1 ws]);
    s_retty = (fun ws -> `W (ret (get_size (as_seq1 ws))));
    s_mk = fun ws -> mk1 (mk ws);
  }
  
  let binop ?(ret = fun x -> x) ~(name : string) mk = {
    s_name = name;
    s_ntyparams = 1;
    s_argsty = (fun ws -> List.make 2 (as_seq1 ws));
    s_retty = (fun ws -> `W (ret (get_size (as_seq1 ws))));
    s_mk = fun ws -> mk2 (mk ws);
  }

  let castop ~(name : string) (k : us) = {
    s_name = name;
    s_ntyparams = 2;
    s_argsty = (fun ws -> [fst (as_seq2 ws)]);
    s_retty = (fun ws -> snd (as_seq2 ws));
    s_mk = (fun ws -> mk1 (fun x -> ESat (k, fst (as_seq2 ws), x)));
  }

  let shiftop ~(name : string) (d : lr) (k : la) = {
    s_name = name;
    s_ntyparams = 1;
    s_argsty = (fun ws -> [as_seq1 ws; `W 16]);
    s_retty = (fun ws -> as_seq1 ws);
    s_mk = (fun _ -> mk2 (fun x y -> EShift (`L, `A, x, y)));
  }

  let mulop ?ret ~(name : string) (s : us) (k : hld) =
    let mk = fun ws x y ->
      let w = as_seq1 ws in
      EMul (s, k, w, (x, y))
    in
    binop ?ret ~name mk

  let sla : sig_ =
    shiftop ~name:"sla" `L `A

  let sra : sig_ =
    shiftop ~name:"sra" `R `A

  let sll : sig_ =
    shiftop ~name:"sll" `L `L

  let srl : sig_ =
    shiftop ~name:"srl" `R `L
    
  let usat : sig_ =
    castop ~name:"usat" `U

  let ssat : sig_ =
    castop ~name:"ssat" `S

  let not : sig_ =
    let mk = fun ws x -> ENot (as_seq1 ws, x) in
    uniop ~name:"not" mk

  let incr : sig_ =
    let mk = fun ws x -> EIncr (as_seq1 ws, x) in
    uniop ~name:"incr" mk

  let add : sig_ =
    let mk = fun ws x y -> EAdd (as_seq1 ws, false, (x, y)) in
    binop ~name:"add" mk

  let addc : sig_ =
    let mk = fun ws x y -> EAdd (as_seq1 ws, true, (x, y)) in
    binop ~ret:(fun n -> n + 1) ~name:"addc" mk

  let sub : sig_ =
    let mk = fun ws x y -> ESub (as_seq1 ws, (x, y)) in
    binop ~name:"sub" mk

  let and_ : sig_ =
    let mk = fun ws x y -> EAnd (as_seq1 ws, (x, y)) in
    binop ~name:"and" mk

  let or_ : sig_ =
    let mk = fun ws x y -> EOr (as_seq1 ws, (x, y)) in
    binop ~name:"or" mk

  let umul : sig_ =
    mulop ~ret:(fun n -> 2 * n) ~name:"umul" `U `D

  let umulhi : sig_ =
    mulop ~name:"umulhi" `U `H
  
  let umullo : sig_ =
    mulop ~name:"umullo" `U `L  

  let smul : sig_ =
    mulop ~ret:(fun n -> 2 * n) ~name:"smul" `S `D

  let smulhi : sig_ =
    mulop ~name:"smulhi" `S `H

  let smullo : sig_ =
    mulop ~name:"smullo" `S `L  
end

(* -------------------------------------------------------------------- *)
let sigs : sig_ list = [
  Sigs.sla;
  Sigs.sra;
  Sigs.sll;
  Sigs.srl;
  Sigs.usat;
  Sigs.ssat;
  Sigs.not;
  Sigs.incr;
  Sigs.add;
  Sigs.addc;
  Sigs.sub;
  Sigs.and_;
  Sigs.or_;
  Sigs.umul;
  Sigs.umullo;
  Sigs.umulhi;
  Sigs.smul;
  Sigs.smullo;
  Sigs.smulhi;  
]

(* -------------------------------------------------------------------- *)
let get_sig_of_name (name : string) : sig_ option =
  List.find_opt (fun x -> x.s_name = name) sigs

(* -------------------------------------------------------------------- *)
let rec tt_expr_ (env : env) (e : pexpr) : aargs option * aexpr =
  match e with
  | PEParens e ->
      (None, tt_expr env e)

  | PEInt i ->
      let e = { node = EInt i; type_ = `Unsigned; } in
      (None, e)

  | PEFun (fargs, f) -> 
      let benv, args = tt_args env fargs in
      (Some args, tt_expr benv f)
  
  | PEFName (v, None) -> begin
    let (vid, (targs, vt)) = Option.get_exn
      (Env.lookup env v)
      (mk_tyerror "unknown variable: %s" v) in

    match targs with
    | None ->
      (None, { node = EVar vid; type_ = vt; })

    | Some targs ->
      let ftargs =
        List.map (fun ty -> (Ident.create "_", ty)) targs in
      let args =
        List.map
          (fun (x, ty) -> { node = EVar x; type_ = (ty :> atype) })
          ftargs in
      (Some ftargs, { node = EApp (vid, args); type_ = vt; })
    end

  | PEFName (v, Some ws) ->
      let sig_ = Option.get (get_sig_of_name v) in
      let args = sig_.s_argsty ws in
      let retty = sig_.s_retty ws in
      let args = List.map (fun ty -> (Ident.create "_", ty)) args in

      let eargs =
        List.map (fun (x, ty) ->
          { node = EVar x; type_ = (ty :> atype); }
        ) args
      in
      let node = sig_.s_mk ws eargs in
      (Some args, { node; type_ = (retty :> atype); })

  | PELet ((v, args, e1), e2) ->
      let args, e1 =
        let env, args =
          args
            |> Option.map (tt_args env)
            |> Option.map (fun (e, a) -> (e, Some a))
            |> Option.default (env, None) in
        let e1 = tt_expr env e1 in
        (args, e1)
      in

      let ebody, vid =
        let targs = Option.map (List.map snd) args in
        Env.push env v (targs, e1.type_) in

      let e2 = tt_expr ebody e2 in

      let node = ELet ((vid, args, e1), e2) in
      let type_ = e2.type_ in

      (None, { node; type_; })

  | PESlice (ev, (start, len, scale)) ->
      let ev = tt_expr env ev in
      let start = tt_expr env start in
      let len = Option.default 1 (Option.map as_int_constant len) in
      let scale = Option.default 1 (Option.map as_int_constant scale) in
      let node = ESlice (ev, (start, len, scale))
      and type_ = `W (len * scale) in
      (None, { node; type_; })

  | PEApp ((f, None), args) ->
    let (vid, (targs, vt)) = Option.get_exn
      (Env.lookup env f)
      (mk_tyerror "unknown symbol: %s" f) in

    let targs =
      Option.get_exn
        targs
        (mk_tyerror "this symbol cannot be applied") in

    if List.length args <> List.length targs then
      tyerror "invalid argument count";
  
    let bds, args = List.fold_left_map (fun bds (a, ety) ->
        match a with
        | None ->
          let x = Ident.create "_" in
          let a = { node = EVar x; type_ = (ety :> atype); }  in
          ((x, ety) :: bds, a)
        | Some a ->
          (bds, tt_expr env ~check:(ety :> atype) a)
      ) [] (List.combine args targs)
    in
  
    let bds = if List.is_empty bds then None else Some (List.rev bds) in
    let node = EApp (vid, args) in
  
    (bds, { node; type_ = vt; })
    
  | PEApp (("concat", w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let args = List.map Option.get args in
      let targs = List.map (tt_expr env ~check:(`W w)) args in
      let wsz = `W (w * List.length targs) in
      (None, { node = EConcat (wsz, targs); type_ = wsz; })

  | PEApp (("repeat", w), args) ->
      let (`W w) = as_seq1 (tt_type_parameters ~expected:1 w) in
      let args = List.map Option.get args in
      let e, n = as_seq2 (check_arguments_count ~expected:2 args) in
      let n = as_int_constant n in
      let ne = tt_expr env ~check:(`W w) e in
      (None, { node = ERepeat (`W (w * n),(ne,n)); type_ = `W (w * n); })

  | PEApp (("map", w), args) ->
    let `W w, `W n = as_seq2 (tt_type_parameters ~expected:2 w) in
    let args = List.map Option.get args in

    if List.is_empty args then tyerror "invalid number of arguments";

    let f, args = (List.hd args, List.tl args) in
    let nargs = List.map (tt_expr ~check:(`W (w * n)) env) args in

    let ftargs, ftbody = tt_expr_ env f in

    let ftargs =
      Option.get_exn
        ftargs
        (mk_tyerror "this expression must be higher-order") in

    let targs = List.map snd ftargs in

    if targs <> List.make (List.length args) (`W w) then
      tyerror "invalid argument types / count";

    let m =
      match ftbody.type_ with
      | `W m -> m
      | _ -> tyerror "function should return a word"
    in

    let node = EMap ((`W w, `W n), (ftargs, ftbody), nargs)
    and type_ = `W (m * n) in
    (None, { node; type_; })

  | PEApp ((f, Some w), args) ->
      let sig_ = Option.get (get_sig_of_name f) in
      tt_fname_app env sig_ w args

(* -------------------------------------------------------------------- *)
and tt_fname_app
  (env : env)
  (sig_ : sig_)
  (ws : pword list)
  (args : pexpr option list)
=
  let ws =
    tt_type_parameters ~expected:sig_.s_ntyparams (Some ws) in

  let targs = sig_.s_argsty ws in

  if List.length args <> List.length targs then
    tyerror "invalid argument count: %s" sig_.s_name;

  let bds, args = List.fold_left_map (fun bds (a, ety) ->
      match a with
      | None ->
        let x = Ident.create "_" in
        let a = { node = EVar x; type_ = (ety :> atype); }  in
        ((x, ety) :: bds, a)
      | Some a ->
        (bds, tt_expr env ~check:(ety :> atype) a)
    ) [] (List.combine args targs)
  in

  let bds = if List.is_empty bds then None else Some (List.rev bds) in

  let node = sig_.s_mk ws args in
  let type_ = (sig_.s_retty ws :> atype) in

  (bds, { node; type_; })

(* -------------------------------------------------------------------- *)
and tt_expr (env : env) ?(check : atype option) (p : pexpr) : aexpr =
  let (args, {node = n_; type_ = t;}) = tt_expr_ env p in
  if not (Option.is_none args) then
    tyerror "high-order functions not allowed here";
  { node = n_; type_ = Option.default t check; }

(* -------------------------------------------------------------------- *)
and tt_arg (env : env) ((x, `W ty) : parg) : env * aarg =
  let env, idx = Env.push env x (None, `W ty) in
  (env, (idx, `W ty))

(* -------------------------------------------------------------------- *)
and tt_args (env : env) (args : pargs) : env * aargs =
  List.fold_left_map tt_arg env args

(* -------------------------------------------------------------------- *)
and tt_exprs (env : env) ~(expected : atype list) (es : pexpr list) : aexpr list =
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
