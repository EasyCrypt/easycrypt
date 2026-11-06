(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoare_sp] — strongest postcondition:

     ------------------------------------  c sp-able
     hoare [c : P ==> sp(c, P) | Q_e]

   where [sp] is [EcPlSp.sp_stmt]. The exceptional postconditions [Q_e]
   play no role: an sp-able statement (assignments and conditionals) raises
   nothing. No premise. Side conditions: [c] is entirely sp-able, and the
   postcondition is convertible to [sp(c, P)] (otherwise fails).

   Node: [RHoareSp]. Checker: "hoare-sp". *)
val t_hoare_sp : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_sp_prefix at] — on [hoare [c : P ==> Q | Q_e]], with [c0] the
   prefix of [c] up to [at] (the whole of [c] when [at] is [None]), and
   [c1] the longest sp-able prefix of [c0], [c = c1; c2]:
   1. [EcHoareSeq.t_hoare_seq] at [|c1|], with [R := sp(c1, P)], giving
        (a) hoare [c1 : P ==> sp(c1, P) | Q_e],
        (b) hoare [c2 : sp(c1, P) ==> Q | Q_e];
   2. on (a), [t_hoare_sp].
   Visible goal: (b). Fails (before applying any rule) when [at] is given
   and [c0] is not entirely sp-able. Emits no node of its own. *)
val t_hoare_sp_prefix : codegap1 option -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [sp] / [sp k] on a [hoareS] goal (a single position): applies
   [t_hoare_sp_prefix]. *)
val process_hoare_sp : pcodegap1 option -> backward
