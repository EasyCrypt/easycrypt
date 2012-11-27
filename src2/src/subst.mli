(* -------------------------------------------------------------------- *)
open Typesmod

(* -------------------------------------------------------------------- *)
type subst

type subst1 = [
  | `Module of Ident.t * Path.path
]

val create: subst1 list -> subst

(* -------------------------------------------------------------------- *)
module ModType : sig
  val apply: subst -> tymod -> tymod
end
