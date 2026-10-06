(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_equiv_sp] — strongest postcondition:

     -------------------------------------------  c, c' sp-able
     equiv [c ~ c' : P ==> sp<2>(c', sp<1>(c, P))]

   where [sp<i>] is [EcPlSp.sp_stmt] in the memory of side [i]: the left
   statement is traversed first, then the right one from the result. No
   premise. Side conditions: [c] and [c'] are entirely sp-able, and the
   postcondition is convertible to [sp<2>(c', sp<1>(c, P))] (otherwise
   fails).

   Node: [REquivSp]. Checker: "equiv-sp". *)
val t_equiv_sp : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_sp_prefix at] — on [equiv [c ~ c' : P ==> Q]], with [c0] /
   [c0'] the prefixes of [c] / [c'] up to the positions [at] (the whole
   statements when [at] is [None]), and [c1] / [c1'] their longest sp-able
   prefixes, [c = c1; c2], [c' = c1'; c2']:
   1. [EcEquivSeq.t_equiv_seq] at [(|c1|, |c1'|)], with
      [R := sp<2>(c1', sp<1>(c1, P))], giving
        (a) equiv [c1 ~ c1' : P ==> R],
        (b) equiv [c2 ~ c2' : R ==> Q];
   2. on (a), [t_equiv_sp].
   Visible goal: (b). Fails (before applying any rule) when [at] is given
   and [c0] or [c0'] is not entirely sp-able. Emits no node of its own. *)
val t_equiv_sp_prefix : codegap1 pair option -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [sp] / [sp k k'] on an [equivS] goal (a pair of positions): applies
   [t_equiv_sp_prefix]. *)
val process_equiv_sp : pcodegap1 pair option -> backward
