(* -------------------------------------------------------------------- *)
type symbol = Ptree.symbol [@@deriving yojson]

(* -------------------------------------------------------------------- *)
module Ident : sig
  type ident [@@deriving yojson]

  val create : string -> ident
  val name : ident -> string
  val id : ident -> int
end = struct
  type ident = symbol * int [@@deriving yojson]

  let create (x : string) : ident = (x, Oo.id (object end))
  let name ((x, _) : ident) : string = x
  let id ((_, i) : ident) : int = i
end

module IdentMap = Map.Make(struct
  type t = Ident.ident
  let compare a b = (Ident.id a) - (Ident.id b)
end) 

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
type mulk = [`U of hld | `S of hld | `US] [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type aexpr_ =
  | EVar of ident
  | EInt of int
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
  | EOr of aword * (aexpr * aexpr)
  | EXor of aword * (aexpr * aexpr)
  | EAnd of aword * (aexpr * aexpr)
  | EMul of mulk * aword * (aexpr * aexpr)
  | ECmp of aword * us * [`Gt | `Ge] * (aexpr * aexpr)
[@@deriving yojson]

and aexpr = { node : aexpr_; type_ : atype } [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type adef = {
  name: string;
  arguments : aargs;
  body : aexpr;
  rettype : aword;
} [@@deriving yojson]

(* -------------------------------------------------------------------- *)
let atype_as_aword (ty : atype) =
  match ty with `W n -> n | _ -> assert false

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
