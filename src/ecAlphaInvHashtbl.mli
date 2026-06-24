(* -------------------------------------------------------------------- *)
open EcAst

(* -------------------------------------------------------------------- *)
(* A hash-table over formulas keyed by alpha-equivalence (in the
   hypotheses context given at creation). Bound variables are hashed by
   de-Bruijn level, so alpha-equivalent formulas share an entry. *)

(* Alpha-invariant, bounded hash of a formula. *)
val hash : form -> int

(* -------------------------------------------------------------------- *)
type 'a t

(* [create hyps size] builds an empty table whose key equality is
   [EcReduction.is_alpha_eq hyps]. *)
val create : EcEnv.LDecl.hyps -> int -> 'a t

val clear    : 'a t -> unit
val add      : 'a t -> form -> 'a -> unit
val find_opt : 'a t -> form -> 'a option
