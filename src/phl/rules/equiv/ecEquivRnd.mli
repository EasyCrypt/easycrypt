(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
type mkbij_t   = ty -> ty -> ts_inv          (* bijection, at given types *)
type semrndpos = (bool * codegap1) doption   (* [rndsem] positions *)

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_rnd = {
  ern_f    : ts_inv;   (* f    : tyL -> tyR *)
  ern_finv : ts_inv;   (* finv : tyR -> tyL *)
}

(* [t_equiv_rnd { ern_f = f; ern_finv = finv }] — two-sided sampling,
   along a bijection:

     ---------------------------------------------------------------------
     equiv [xL <$ dL ~ xR <$ dR :
                (forall v, v \in dR => v = f (finv v))
             /\ (forall v, v \in dR => mu1 dR v = mu1 dL (finv v))
             /\ (forall v, v \in dL =>
                     f v \in dR /\ v = finv (f v) /\ Q[xL<1> := v, xR<2> := f v])
           ==> Q]

   ([/\] is the asymmetric conjunction [&&].) Side conditions: both
   statements are single samplings, [f : tyL -> tyR] and
   [finv : tyR -> tyL] where [dL : tyL distr] and [dR : tyR distr], and the
   precondition is, up to alpha-conversion, the one displayed (otherwise
   fails).

   Node: [REquivRnd { ern_f = f; ern_finv = finv }]. Checker: "equiv-rnd". *)
val t_equiv_rnd : equiv_rnd -> backward

type equiv_rnd_onesided = {
  eros_side : side;   (* side of the sampling *)
}

(* [t_equiv_rnd_onesided { eros_side = `Left }] — one-sided sampling:

     -------------------------------------------------------------------------
     equiv [x <$ d ~ skip : is_lossless d /\ (forall v, v \in d => Q[x<1> := v]) ==> Q]

   (symmetrically for [`Right]; [/\] is [&&]). Side conditions: that side is
   a single sampling, the other one is empty, and the precondition is, up to
   alpha-conversion, the one displayed (otherwise fails).

   Node: [REquivRndOneSided { eros_side }]. Checker: "equiv-rnd-onesided". *)
val t_equiv_rnd_onesided : equiv_rnd_onesided -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_rnd_last bij] — on [equiv [c; xL <$ dL ~ c'; xR <$ dR : P ==> Q]],
   with [f, finv] the bijection [bij] instantiated at the types [tyL], [tyR]
   of the sampled values — the identity when [bij] is [None], which
   requires [tyL = tyR] — and [R] the precondition of [t_equiv_rnd]:
   1. [EcEquivSeq.t_equiv_seq] before both samplings, with intermediate
      relation [R], giving
        (a) equiv [c ~ c' : P ==> R],
        (b) equiv [xL <$ dL ~ xR <$ dR : R ==> Q];
   2. [t_equiv_rnd] closes (b);
   3. on (a), the second conjunct of [R] (the [mu1] condition) and the
      [f v \in dR /\ v = finv (f v)] part of the third one are each
      dropped from the relation when [t_solve ~bases:["random"]] proves it
      on its own (as a lemma over the memories), with
      [EcPhlConseq.t_equivS_conseq] (whose side conditions are closed).
   Visible goal: (a), with the relation simplified by step 3. *)
val t_equiv_rnd_last : (mkbij_t pair) option -> backward

(* [t_equiv_rnd_onesided_last side] — on [equiv [c; x <$ d ~ c' : P ==> Q]]
   (for [`Left]; symmetrically for [`Right]), with [R] the precondition of
   [t_equiv_rnd_onesided]:
   1. [EcEquivSeq.t_equiv_seq] before the sampling on that side and at the
      end of the other one, with intermediate relation [R], giving
        (a) equiv [c ~ c' : P ==> R],
        (b) equiv [x <$ d ~ skip : R ==> Q];
   2. [t_equiv_rnd_onesided] closes (b);
   3. on (a), when [t_solve ~bases:["random"]] proves [is_lossless d]
      (as a stand-alone lemma over the memories), it is dropped from the
      relation with [EcPhlConseq.t_equivS_conseq] (side conditions closed).
   Visible goal: (a), with the relation simplified by step 3. *)
val t_equiv_rnd_onesided_last : side -> backward

(* [t_equiv_rnd_full ?pos side (f, finv)] — the surface [rnd] on equiv:
   - one-sided ([side] given, no position, no bijection):
     [t_equiv_rnd_onesided_last side];
   - two-sided (no side): [EcEquivRndSem.t_equiv_rndsem] on the left, then
     on the right, at the positions [pos] (a single one is used on both
     sides) when given, then [t_equiv_rnd_last] with the bijection [f] /
     [finv] (either one standing for both when the other is absent).
   Fails on any other combination. *)
val t_equiv_rnd_full :
  ?pos:semrndpos -> oside -> (mkbij_t option) pair -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rnd{i}], [rnd [f [finv]]] and [rnd [f [finv]] : [*]k [[*]k'] ] on an
   [equivS] goal. The bijections are typed as [tyL -> tyR] / [tyR -> tyL]
   functions in the goal's memories; the positions in the memory of their
   side (a single position with no side, in the bare environment). Applies
   [t_equiv_rnd_full]. *)
val process_equiv_rnd :
  oside -> psemrndpos option -> rnd_tac_info_f -> backward
