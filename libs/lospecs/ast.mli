(* -------------------------------------------------------------------- *)
type symbol = Ptree.symbol

(* -------------------------------------------------------------------- *)
module Ident : sig
  type ident

  val create : string -> ident
end

type ident = Ident.ident

(* -------------------------------------------------------------------- *)
type aword = [ `W of int ]
type atype = [ aword | `Signed | `Unsigned ]

type aarg  = ident * aword
type aargs = aarg list

type lr   = [`L | `R]
type la   = [`L | `A]
type us   = [`U | `S]
type hl   = [`H | `L]
type hld  = [hl | `D]
type mulk = [`U of hld | `S of hld | `US]

(* -------------------------------------------------------------------- *)
type aexpr_ =
  | EVar of ident
  | EInt of int64
  | ESlice of aexpr * (aexpr * int * int)
  | EAssign of aexpr * (aexpr * int * int) * aexpr
  | EApp of ident * aexpr list
  | EMap of (aword * aword) * (aargs * aexpr) * aexpr list
  | EConcat of aword * aexpr list
  | ERepeat of aword * (aexpr * int)
  | EShift of lr * la * (aexpr * aexpr)
  | EExtend of us * aword * aexpr
  | ESat of us * aword * aexpr
  | ELet of (ident * aargs option * aexpr) * aexpr
  | ECond of aexpr * (aexpr * aexpr)
  | ENot of aword * aexpr
  | EIncr of aword * aexpr
  | EAdd of aword * [`Sat of us | `Word] * (aexpr * aexpr)
  | ESub of aword * (aexpr * aexpr)
  | EMul of mulk * aword * (aexpr * aexpr)
  | EOr of aword * (aexpr * aexpr)
  | EXor of aword * (aexpr * aexpr)
  | EAnd of aword * (aexpr * aexpr)
  | EEq of aword * (aexpr * aexpr)
  | ECmp of aword * us * [`Gt | `Ge] * (aexpr * aexpr)
  | EPopCount of aword * aexpr

and aexpr = { node : aexpr_; type_ : atype }

(* -------------------------------------------------------------------- *)
type adef = {
  name : string;
  arguments : aargs;
  body : aexpr;
  rettype : aword;
}

(* -------------------------------------------------------------------- *)
val atype_as_aword : atype -> int
val get_size : aword -> int
val pp_atype : Format.formatter -> atype -> unit
