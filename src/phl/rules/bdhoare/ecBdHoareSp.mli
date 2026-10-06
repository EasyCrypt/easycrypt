(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_sp_rule = {
  bspr_at : codegap1;   (* split position k: end of the sp-able prefix *)
}

(* [t_bdhoare_sp { bspr_at = k }] — strongest postcondition of a prefix,
   with [~] the goal's comparison:

         phoare [c2 : sp(c1, P) ==> Q] ~ d
     -----------------------------------------  c = c1; c2   (c1 = c[0..k))
             phoare [c : P ==> Q] ~ d            c1 sp-able, d not written by c1

   where [sp] is [EcPlSp.sp_stmt]. Side conditions: [c1] is entirely
   sp-able and does not write the variables of the bound [d] (otherwise
   fails).

   RETAINED IMPLICIT SEQ. Unlike the hoare and equiv [sp] rules, this rule
   is stated on [c1; c2]. [EcBdHoareSeq.t_bdhoare_seq] with phi := true,
   R := sp(c1, P), f1 := 1, f2 := d, g1 := 0, g2 := 1 has this rule's
   premise as its (F2), but deriving the rule from it would also need
   closing, on the spot: (H) by [EcHoareTrue]; (F1)
   [phoare [c1 : P ==> sp(c1, P)] ~ 1] by a further trusted bdhoare rule;
   (G1) [phoare [c1 : P ==> !sp(c1, P)] ~ 0] through the not yet migrated
   hoare-to-phoare consequence; and the arithmetic (B)
   [P => 1 * d + 0 * 1 ~ d] and non-modification (N) premises with
   best-effort tactics, which do not reliably close them (so the visible
   goals could change). The rule is kept on [c1; c2] until this can be
   done exactly. Its side condition on [d] is what (N) would express.

   Node: [RBdHoareSp { bspn_at = k (resolved index) }].
   Checker: "bdhoare-sp". *)
val t_bdhoare_sp : bdhoare_sp_rule -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_sp_prefix at] — on [phoare [c : P ==> Q] ~ d], with [c0] the
   prefix of [c] up to [at] (the whole of [c] when [at] is [None]), and
   [c1] the longest sp-able prefix of [c0]: [t_bdhoare_sp] at [|c1|].
   Fails (before applying the rule) when [c0] writes the bound [d], or
   when [at] is given and [c0] is not entirely sp-able. Visible goal: the
   premise of the rule. Emits no node of its own. *)
val t_bdhoare_sp_prefix : codegap1 option -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [sp] / [sp k] on a [bdHoareS] goal (a single position): applies
   [t_bdhoare_sp_prefix]. *)
val process_bdhoare_sp : pcodegap1 option -> backward
