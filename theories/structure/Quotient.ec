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
(* This theory defines the effective quotient using an idempotent map,  *)
(* canon. It builds on the previous theory by using for [qT] the        *)
(* elements that are stable under canon.                                *)
(* -------------------------------------------------------------------- *)

abstract theory CanonQuotient.

type T.

op canon : T -> T.

axiom canonK (x : T): canon (canon x) = canon x.

op iscanon x = canon x = x.

lemma iscanon_canon x : iscanon (canon x).
proof. by rewrite /iscanon canonK. qed.

subtype qT as QSub = {x : T | iscanon x}.
realize inhabited by exists (canon witness); apply canonK.

import QSub.

(* NOTE: The `canon` in `repr` might look like it does nothing,         *)
(*       but it can make `iscanon_repr` trivial when `iscanon_canon` is *)
clone include CoreQuotient with
  type T     <- T,
  type qT    <- qT,
  op   pi    =  fun x => QSub.insubd (canon x),
  op   repr  =  fun x => canon (QSub.val x)

  proof *.
realize reprK by move => q; rewrite /pi /repr canonK valP valKd.

lemma iscanon_repr v : iscanon (repr v) by rewrite iscanon_canon. 

lemma piK x : repr (pi x) = canon x.
proof. by rewrite /repr insubdK // iscanon_canon. qed.

end CanonQuotient.

(* -------------------------------------------------------------------- *)
(* This theory defines the effective quotient by an equivalence         *)
(* relation. It is build on the former theory, using for canon the      *)
(* choice map selecting a member of the equivalence class.              *)
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
proof. apply (@choicebP (eqv x) x); by exists x; apply eqv_refl. qed.

lemma eqv_canon_eq (x y : T): eqv x y => canon x = canon y.
proof.
move=> eqv_xy; rewrite /canon (@eq_choice (eqv x) (eqv y)) => [z|].
- split => [eqv_xz|eqv_yz].
  + by apply (eqv_trans x) => //; rewrite eqv_sym.
  + by apply (eqv_trans _ eqv_xy eqv_yz).
by apply choice_dfl_irrelevant; exists y; apply eqv_refl.
qed.

clone include CanonQuotient with
  type T <- T,
  op canon <- canon
  proof *.
realize canonK by move => x; rewrite &(eqv_canon_eq) eqv_sym eqv_canon.

import QSub.

lemma eqvP x y : eqv x y <=> canon x = canon y.
proof.
split=> [/eqv_canon_eq //|eq].
rewrite &(eqv_trans (canon y)) -1:eqv_sym -1:eqv_canon.
apply/(eqv_trans (canon x)); first by apply/eqv_canon.
by rewrite eq &(eqv_refl).
qed.

lemma eqv_pi x y : eqv x y <=> pi x = pi y.
proof.
rewrite eqvP /pi; split => [->//|].
by move => /(congr1 val); rewrite !val_insubd !iscanon_canon.
qed.

lemma eqv_repr x : eqv (repr (pi x)) x.
proof. rewrite /repr val_insubd iscanon_canon eqv_sym /= canonK eqv_canon. qed.
end EquivQuotient.
