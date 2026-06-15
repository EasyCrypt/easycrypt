(* -------------------------------------------------------------------- *)
type symbol = Ptree.symbol

exception DestrError of string

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

module IdentMap = Map.Make(struct
  type t = Ident.ident
  let compare a b = (Ident.id a) - (Ident.id b)
end) 

(* -------------------------------------------------------------------- *)
type ident = Ident.ident

(* -------------------------------------------------------------------- *)
type aword = [ `W of int ]

(* -------------------------------------------------------------------- *)
type atype = [ aword | `Signed | `Unsigned ]

(* -------------------------------------------------------------------- *)
type aarg = ident * aword

(* -------------------------------------------------------------------- *)
type aargs = aarg list

(* -------------------------------------------------------------------- *)
type lr = [`L | `R]
type la = [`L | `A]
type us = [`U | `S]
type hl = [`H | `L]
type hld = [hl | `D]
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
  name: string;
  arguments : aargs;
  body : aexpr;
  rettype : aword;
}

(* -------------------------------------------------------------------- *)
let atype_as_aword (ty : atype) =
  match ty with `W n -> n | _ -> raise (DestrError "atype_as_aword") 

(* -------------------------------------------------------------------- *)
let get_size (`W w : aword) : int =
  w

(* -------------------------------------------------------------------- *)
let pp_aword (fmt : Format.formatter) (`W n : aword) =
  Format.fprintf fmt "@%d" n

(* -------------------------------------------------------------------- *)
let pp_atype (fmt : Format.formatter) (t : atype) =
  match t with
  | `W _ as w -> Format.fprintf fmt "%a" pp_aword w
  | `Unsigned -> Format.fprintf fmt "%s" "unsigned"
  | `Signed -> Format.fprintf fmt "%s" "signed"
