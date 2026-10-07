(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_equiv_if] — synchronized conditionals:

     forall &1 &2, P => (b<1> <=> b'<2>)
     equiv [c1 ~ c1' : P /\ b<1> ==> Q]
     equiv [c2 ~ c2' : P /\ !b<1> ==> Q]
     ---------------------------------------------------------------
     equiv [if b then c1 else c2 ~ if b' then c1' else c2' : P ==> Q]

   Side condition: each statement is a single conditional (otherwise
   fails).

   Node: [REquivIf]. Checker: "equiv-if". *)
val t_equiv_if : backward

type equiv_if_onesided = {
  eio_side : side;   (* side of the conditional *)
}

(* [t_equiv_if_onesided { eio_side = `Left }] — one-sided conditional:

     equiv [c1 ~ c' : P /\ b<1> ==> Q]
     equiv [c2 ~ c' : P /\ !b<1> ==> Q]
     -----------------------------------------
     equiv [if b then c1 else c2 ~ c' : P ==> Q]

   (symmetrically for [`Right]). Side condition: the statement of that
   side is a single conditional (otherwise fails).

   Node: [REquivIfOneSided { eio_side }]. Checker: "equiv-if-onesided". *)
val t_equiv_if_onesided : equiv_if_onesided -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_if_head side]:
   - [side = Some `Left], on [equiv [if b then c1 else c2; c ~ c' : P ==> Q]]
     (symmetrically for [`Right]):
     1. when [c] is not empty, [EcEquivTransform.t_equiv_transform] on that
        side with [EcTrIfPush.TrIfPush], giving
          equiv [if b then { c1; c } else { c2; c } ~ c' : P ==> Q];
     2. [t_equiv_if_onesided].
     Visible goals: equiv [c1; c ~ c' : P /\ b<1> ==> Q] and
     equiv [c2; c ~ c' : P /\ !b<1> ==> Q].
   - [side = None], on [equiv [if b then c1 else c2; c ~
     if b' then c1' else c2'; c' : P ==> Q]]:
     1. the push of step 1 above on the left (when [c] is not empty), then
        on the right (when [c'] is not empty);
     2. [t_equiv_if].
     Visible goals: forall &1 &2, P => (b<1> <=> b'<2>), then
     equiv [c1; c ~ c1'; c' : P /\ b<1> ==> Q] and
     equiv [c2; c ~ c2'; c' : P /\ !b<1> ==> Q].
   Fails if the first instruction of a side is not a conditional (left
   checked first). Emits no node of its own. *)
val t_equiv_if_head : oside -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* On an [equivS] goal:
   - [if] / [if{i}]: applies [t_equiv_if_head];
   - [if{i}? k k' : R] (and [if := R], i.e. [if _ _ : R]): [t_equiv_seq]
     before the conditionals at [(k, k')] (by default, the last top-level
     conditional of each side) with the relation [R], then
     [t_equiv_if_head] on the second premise; visible goals: the first
     premise of [seq], then those of [t_equiv_if_head];
   - [if{i} k? : (_ : P ==> Q)]: [t_equiv_seq_onesided] on side [i] before
     the conditional at [k] (by default, the last top-level one) with
     [P] / [Q], then [EcBdHoareIf.t_bdhoare_if_head] on its [phoare]
     premise; visible goals: the [equiv] premise of the one-sided [seq],
     then those of [t_bdhoare_if_head]. *)
val process_equiv_if : pcond_info -> backward
