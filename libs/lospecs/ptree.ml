(* -------------------------------------------------------------------- *)
(* Typing hint: env[symbol] *)
type symbol = string [@@deriving show]
type pword = [ `W of int ] [@@deriving show]
type ptype = [ `Unsigned | `Signed | pword ] [@@deriving show]
type parg = symbol * pword [@@deriving show]
type pargs = parg list [@@deriving show]
type pfname = symbol * pword list option [@@deriving show]

type pexpr =
  | PEParens of pexpr (* type: typeof(pexpr) *)
  | PEVar of symbol
  | PEInt of int (* type: int *)
  | PECast of ptype * pexpr (* type: ptype (check if convertible) *)
  | PEFun of
      pargs * pexpr (* type: add ret type to env (calculate on the fly?) *)
  | PELet of (symbol * pexpr) * pexpr
    (* typeof: second pexpr with symbol added to env as type of first expr *)
  | PESlice of pexpr * (pexpr * pexpr * pexpr option)
    (* type: same type as first expr *)
  | PEApp of
      pfname
      * pexpr list (* if args match fun type then fun ret else type error *)
[@@deriving show]

type pdef = { name : symbol; args : pargs; rty : pword; body : pexpr }
[@@deriving show]

type pprogram = pdef list [@@deriving show]
