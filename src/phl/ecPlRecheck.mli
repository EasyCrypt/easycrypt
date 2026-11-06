(* -------------------------------------------------------------------- *)
open EcFol
open EcEnv
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Shared scaffolding for proof-node checkers (see [EcCoreGoal.rule]). *)

(* Compare [expected] subgoal conclusions against the recorded subgoals, up to
   conversion under each subgoal's own hypotheses; raise [RecheckFailure] on an
   arity or conversion mismatch. *)
val recheck_forms : string -> form list -> pregoal list -> unit

(* [checker_of name destr build] is a [rule_checker]: it reads the judgement
   from the goal with [destr], recomputes the subgoals with [build] (handed the
   goal's hypotheses), and compares them with [recheck_forms]. Any exception
   raised while reading or rebuilding is wrapped in [RecheckFailure]. *)
val checker_of :
     string
  -> (proofenv -> form -> 'a)
  -> (LDecl.hyps -> 'a -> form list)
  -> rule_checker
