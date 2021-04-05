(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require Subtype.

pragma +implicits.

(* -------------------------------------------------------------------- *)
(* This theory defines the effective quotient [qT] obtained from [T]    *)
(* via a representative/canonical surjecton pair of functions.          *)
(* -------------------------------------------------------------------- *)
abstract theory CoreQuotient.

type T, qT.

op repr : qT -> T.              (* representative selection *)
op pi   : T  -> qT.             (* canonical surjection *)

axiom reprK: cancel repr pi.

op (==) (x y : T) = (pi x = pi y).

(* -------------------------------------------------------------------- *)
lemma piP (x : T): x == repr (pi x).
proof. by rewrite /(==) reprK. qed.

lemma quotW P: (forall y, P (pi y)) => forall x, P x.
proof. by move=> Py x; rewrite -(reprK x); apply/Py. qed.

lemma quotP P: (forall y, repr (pi y) = y => P (pi y)) => forall x, P x.
proof. by move=> Py x; rewrite -(reprK x); apply/Py; rewrite reprK. qed.

end CoreQuotient.

(* -------------------------------------------------------------------- *)
(* This theory defines the effective quotient by an equivalence         *)
(* relation. It is build on the former theory, using for [qT] the       *)
(* elements of [T] that are stable by repr \o pi.                       *)
(* -------------------------------------------------------------------- *)
abstract theory EquivQuotient.

type T.

op eqv : T -> T -> bool.

theory EqvEquiv.
axiom eqv_refl : reflexive  eqv.
axiom eqv_sym  : symmetric  eqv.
axiom eqv_trans: transitive eqv.
end EqvEquiv.

import EqvEquiv.

lemma eqv_choose (x : T): exists y, eqv x y.
proof. by exists x; rewrite eqv_refl. qed.

op canon (x : T) = choiceb (eqv x) x.

lemma eqv_canon (x : T) : eqv x (canon x).
proof.
rewrite /canon; apply: (@choicebP (eqv x) x).
by exists x; apply: eqv_refl.
qed.

lemma eqv_canon_eq (x y : T): eqv x y => canon x = canon y.
proof.
move=> eqv_xy; rewrite /canon (@eq_choice (eqv x) (eqv y)).
- move=> z; split => [eqv_xz|eqv_yz].
  - by apply/(eqv_trans x) => //; rewrite eqv_sym.
  - by apply/(eqv_trans _ eqv_xy eqv_yz).
by apply: choice_dfl_irrelevant; exists y; apply: eqv_refl.
qed.

lemma canonK x : canon (canon x) = canon x.
proof. by rewrite &(eqv_canon_eq) eqv_sym eqv_canon. qed.

op iscanon x = canon x = x.

lemma canon_iscanon x : iscanon x => canon x = x.
proof. by move=> @/iscanon /eq_sym ->; apply: canonK. qed.

lemma iscanon_canon x : iscanon (canon x).
proof. by rewrite /iscanon canonK. qed.

lemma eqvP x y : (eqv x y) <=> (canon x = canon y).
proof.
split=> [/eqv_canon_eq //|eq].
rewrite &(eqv_trans (canon y)) -1:eqv_sym -1:eqv_canon.
apply/(eqv_trans (canon x)); first by apply/eqv_canon.
by rewrite eq &(eqv_refl).
qed.

type qT.

clone import Subtype with
  type T  <- T,
  type sT <- qT,
  pred P  <- iscanon,
  op  wsT <- canon witness.

clone include CoreQuotient with
  type T     <- T,
  type qT    <- qT,
  op   pi    =  fun x => Subtype.insubd (canon x),
  op   repr  =  fun x => Subtype.val x

  proof *.

realize reprK. proof.
by move=> q; rewrite /pi /repr /insubd canon_iscanon 1:valP valK.
qed.

lemma eqv_pi : forall x y , eqv x y <=> pi x = pi y.
proof.
move=> x y @/pi; split=> [eq_xy|]; first by congr; apply: eqv_canon_eq.
by move/(congr1 val); rewrite !val_insubd !iscanon_canon /= => /eqvP.
qed.

lemma eqv_repr : forall x, eqv (repr (pi x)) x.
proof.
move=> x @/pi @/repr; rewrite val_insubd.
by rewrite iscanon_canon /= eqv_sym &(eqv_canon).
qed.
end EquivQuotient.
