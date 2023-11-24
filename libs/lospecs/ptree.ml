(* -------------------------------------------------------------------- *)
type symbol =
  string

type pword =
  W of int

type ptype =
  | Unsigned
  | Signed
  | Word of int

type parg =
  symbol * pword

type pargs =
  parg list

type pfname =
  symbol * pword list option

type pexpr =
  | PEParens of pexpr
  | PEInt    of int
  | PECast   of ptype * pexpr
  | PEFun    of pargs * pexpr
  | PELet    of (symbol * pexpr) * pexpr
  | PESlice  of pexpr * (pexpr * pexpr * pexpr option)
  | PEApp    of pfname * pexpr list

type pdef = {
  name : symbol;
  args : pargs;
  rty  : pword;
  body : pexpr;
}

type pprogram =
  pdef list
