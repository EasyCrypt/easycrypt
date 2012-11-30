(* -------------------------------------------------------------------- *)
open EcTypesmod

(* -------------------------------------------------------------------- *)
type subst

type subst1 = [
  | `Module of EcIdent.t * EcPath.path
]

val create: subst1 list -> subst

(* -------------------------------------------------------------------- *)
module ModType : sig
  val apply: subst -> tymod -> tymod
end
