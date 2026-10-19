(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_bdhoare_match] — pattern matching, with [~] the goal's comparison
   ([<=], [=] or [>=]). With [C_1, ..., C_n] the constructors of the type
   of [e], one premise per constructor, in declaration order:

       phoare{m + ys_i} [b_i[ys_i/xs_i] : e = C_i ys_i /\ P ==> Q] ~ d
     -------------------------------------------------------  (i = 1..n)
          phoare{m} [match e with | C_i xs_i => b_i end : P ==> Q] ~ d

   where [ys_i] are fresh program variables, named after the pattern
   variables [xs_i] and of the same types, added to the memory [m] (see
   [EcPlMatch.match_branches]). Side condition: the statement is the
   single [match] (otherwise fails).

   Node: [RBdHoareMatch]. Checker: "bdhoare-match"; it recomputes the
   constructors of the type of [e] from the goal's context. *)
val t_bdhoare_match : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_match_head] — on [phoare [match e with | C_i xs_i => b_i
   end; c : P ==> Q] ~ d]:
   1. when [c] is not empty, [EcBdHoareTransform.t_bdhoare_transform]
      with [EcTrMatchPush.TrMatchPush], giving
        phoare [match e with | C_i xs_i => { b_i; c } end : P ==> Q] ~ d;
   2. [t_bdhoare_match].
   Visible goals, one per constructor:
     phoare{m + ys_i} [b_i[ys_i/xs_i]; c : e = C_i ys_i /\ P ==> Q] ~ d.
   Fails if the first instruction is not a [match]. Emits no node of its
   own. *)
val t_bdhoare_match_head : backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [match] on a [bdHoareS] goal: applies [t_bdhoare_match_head]. The side
   or [=], if any, is ignored (behaviour preserved). *)
val process_bdhoare_match : matchmode -> backward
