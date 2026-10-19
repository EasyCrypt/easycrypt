(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Strongest postcondition, shared by the [sp] rules of every logic.

   An instruction is sp-able when it is an assignment, or a conditional
   whose two branches are (entirely) sp-able. *)

(* [sp_stmt ?mc me env c P] = [(rest, sp(c1, P))], where [c = c1; rest],
   [c1] is the longest sp-able prefix of [c], and [sp(c1, P)] is the
   strongest postcondition of [c1] from [P] (a formula in the memory of
   [me]). The variables existentially quantified in [sp(c1, P)] are fresh
   at each call: two calls on the same arguments agree up to
   alpha-conversion. [mc] gives the two memories of a two-sided goal (it
   only affects the names of these variables). *)
val sp_stmt :
     ?mc:(memory * memory) -> memenv -> env
  -> instr list -> form -> instr list * form

(* [check_sp_progress ?side tc bounded rest] — when the user gave a bound
   ([bounded]), fails (user-facing error) if [rest] is not empty. *)
val check_sp_progress :
  ?side:[`Left | `Right] -> tcenv1 -> bool -> instr list -> unit

(* [gap_at k] — the code gap before the [k]-th instruction (0-based), i.e.
   splitting at [gap_at k] keeps the first [k] instructions as prefix. *)
val gap_at : int -> EcMatching.Position.codegap1
