(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Weakest preconditions, shared by the wp rules of every logic. Computing
   them is done here and nowhere else.

   A statement [s] is traversed backwards, instruction by instruction, as
   long as the instruction is wp-able. Each function returns [(r, pre)]:
   [r] is the prefix of [s] that could not be traversed (empty when [s] is
   entirely wp-able), and [pre] the weakest precondition, of the
   postcondition, of the suffix that was. With [~uselet] (the default),
   the substitutions are let-bound in [pre] rather than applied.

   Please, note that WP only operates over assignments and conditional
   statements. Any weakening of this restriction may break the soundness
   of the bounded hoare logic. *)

(* [wp hyps me s Q]: wp-able are assignments, [if] and [match] whose
   branches are entirely wp-able, and, only when [~onesided] (the hoare
   logic), [raise e], whose wp is the exceptional postcondition of [e] in
   [Q] (its default branch, or [true] when there is none: an exception
   covered by no branch is unconstrained). [~mc] gives the two memories of a
   two-sided postcondition. *)
val wp :
     ?mc:(memory * memory)
  -> ?uselet:bool
  -> ?onesided:bool
  -> LDecl.hyps -> memenv -> stmt -> exnpost
  -> instr list * form

(* [ewp env me s Q]: expectation-wp, for the ehoare logic. wp-able are
   assignments, samplings (wp: the expectation of the wp of what follows)
   and [if] whose branches are entirely wp-able. *)
val ewp :
  ?uselet:bool -> env -> memenv -> stmt -> form -> instr list * form

(* [check_wp_progress tc k r]: when an explicit position [k] was given,
   fails with "remaining n instruction(s)" if the statement after [k]
   left [r] non-empty. *)
val check_wp_progress : tcenv1 -> 'a option -> instr list -> unit
