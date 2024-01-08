(* -------------------------------------------------------------------- *)
(* Typing hint: env[symbol] *)
type symbol = string [@@deriving yojson]
type pword = [ `W of int ] [@@deriving yojson]
type ptype = [ `Unsigned | `Signed | pword ] [@@deriving yojson]
type parg = symbol * pword [@@deriving yojson]
type pargs = parg list [@@deriving yojson]
type pfname = symbol * pword list option [@@deriving yojson]

type pexpr =
  | PEParens of pexpr 
  | PEFName of pfname
  | PEInt of int
  | PEFun of pargs * pexpr
  | PELet of (symbol * pargs option * pexpr) * pexpr
  | PESlice of pexpr * (pexpr * pexpr option * pexpr option)
  | PEApp of pfname * pexpr option list
[@@deriving yojson]

type pdef = { name : symbol; args : pargs; rty : pword; body : pexpr }
[@@deriving yojson]

type pprogram = pdef list [@@deriving yojson]
