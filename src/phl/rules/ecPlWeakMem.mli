(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv
open EcPV

(* -------------------------------------------------------------------- *)
(* Weakening of a memory, shared by the [weakmem] rules of every logic: a
   judgement on a statement that holds in a memory [me] holds in [me]
   extended with fresh local program variables [xs], which the judgement
   does not mention. *)

exception InvalidWeakening of string

(* [restrict env xs me' used] is the memory [me] such that
   [me' = EcMemory.bindall xs me] (same memory identifier): [xs] are the
   last variables declared in [me'], each fresh in [me]. The program
   variables [used] by the judgement must not include [xs], so that the
   judgement is well-formed in [me]. Raises [InvalidWeakening]
   otherwise. *)
val restrict : env -> ovariable list -> memenv -> PV.t -> memenv

(* [used env m s fs]: the program variables read or written by [s],
   joined with the program variables of memory [m] in the formulas
   [fs]. *)
val used : env -> memory -> stmt -> form list -> PV.t
