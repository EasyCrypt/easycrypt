(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import StdRing StdOrder.
(*---*) import RField RealOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
lemma eq_lub (E1 E2 : real -> bool) :
  (forall x, E1 x <=> E2 x) => lub E1 = lub E2.
proof.
move=> eqE; have /fun_ext ->//: forall x, E1 x = E2 x.
by move=> x; apply/eq_iff/eqE.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_lub (E1 E2 : real -> bool) :
     (forall x, E1 x => exists y, E2 y /\ x <= y)
  => has_lub E2 => nonempty E1 => lub E1 <= lub E2.
proof.
move=> le lub2 [x E1x]; have lub1: has_lub E1.
  split; [exists x | exists (lub E2)]; move=> // y.
  by move/le=> [z] [E2z /ler_trans]; apply; apply/lub_upper_bound.
apply/lerNgt/negP=> lt21; have := lub_adherent _ lub1.
move/(_ (lub E1 - lub E2)); rewrite subr_gt0 lt21 => -[e] [E1e].
rewrite opprB addrCA addrN addr0 => lt2e.
move/le: E1e => [y] [E2y] leey; have := lub_upper_bound _ lub2.
by move/(_ _ E2y); rewrite lerNgt /=; apply/(@ltr_le_trans e).
qed.
