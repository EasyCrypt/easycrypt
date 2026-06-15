(* -------------------------------------------------------------------- *)
type range = {
  rg_fname : string;
  rg_begin : int * int;
  rg_end   : int * int;
}

type 'a loced = { range : range; data : 'a; }

(* -------------------------------------------------------------------- *)
(* Source ranges and located-value helpers. *)
module Lc : sig
  val of_positions : Lexing.position -> Lexing.position -> range
  val of_lexbuf    : Lexing.lexbuf -> range
  val merge        : range -> range -> range
  val unloc        : 'a loced -> 'a
  val mk           : range -> 'a -> 'a loced
  val map          : ('a -> 'b) -> 'a loced -> 'b loced
end

(* -------------------------------------------------------------------- *)
exception ParseError of range

(* -------------------------------------------------------------------- *)
type symbol = string
type word = [ `W of int ]
type type_ = [ `Unsigned | `Signed | word ]

(* -------------------------------------------------------------------- *)
type psymbol = symbol loced
type pword = word loced
type ptype = type_ loced
type parg = psymbol * pword
type pargs = parg list
type pfname = (psymbol * pword list option) loced

(* -------------------------------------------------------------------- *)
type pexpr_ =
  | PEParens of pexpr
  | PEFName of pfname
  | PEInt of int64 * pword option
  | PECond of pexpr * (pexpr * pexpr)
  | PEFun of pargs * pexpr
  | PELet of (psymbol * pargs option * pexpr) * pexpr
  | PESlice of pexpr * pslice
  | PEAssign of pexpr * pslice * pexpr
  | PEApp of pfname * pexpr option loced list

and pexpr = pexpr_ loced

and pslice = (pexpr * pexpr option * pexpr option)

(* -------------------------------------------------------------------- *)
type pdef = { name : symbol; args : pargs; rty : pword; body : pexpr }

type pprogram = pdef list
