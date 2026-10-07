(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoare_match] — pattern matching. With [C_1, ..., C_n] the
   constructors of the type of [e], one premise per constructor, in
   declaration order:

       hoare{m + ys_i} [b_i[ys_i/xs_i] : e = C_i ys_i /\ P ==> Q | E]
     ------------------------------------------------------  (i = 1..n)
          hoare{m} [match e with | C_i xs_i => b_i end : P ==> Q | E]

   where [ys_i] are fresh program variables, named after the pattern
   variables [xs_i] and of the same types, added to the memory [m] (see
   [EcPlMatch.match_branches]). Side condition: the statement is the
   single [match] (otherwise fails).

   Node: [RHoareMatch]. Checker: "hoare-match"; it recomputes the
   constructors of the type of [e] from the goal's context. *)
val t_hoare_match : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_match_head] — on [hoare [match e with | C_i xs_i => b_i end;
   c : P ==> Q | E]]:
   1. when [c] is not empty, [EcHoareTransform.t_hoare_transform] with
      [EcTrMatchPush.TrMatchPush], giving
        hoare [match e with | C_i xs_i => { b_i; c } end : P ==> Q | E];
   2. [t_hoare_match].
   Visible goals, one per constructor:
     hoare{m + ys_i} [b_i[ys_i/xs_i]; c : e = C_i ys_i /\ P ==> Q | E].
   Fails if the first instruction is not a [match]. Emits no node of its
   own. *)
val t_hoare_match_head : backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [match] on a [hoareS] goal: applies [t_hoare_match_head]. The side or
   [=], if any, is ignored (behaviour preserved). *)
val process_hoare_match : matchmode -> backward
