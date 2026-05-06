pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Core.
require import TcMonoid TcRing.

(* -------------------------------------------------------------------- *)
pred homo2 ['a 'b] (op_ : 'a -> 'b) (aR : 'a rel) (rR : 'b rel) =
  forall x y, aR x y => rR (op_ x) (op_ y).

pred mono2 ['a 'b] (op_ : 'a -> 'b) (aR : 'a rel) (rR : 'b rel) =
  forall x y, rR (op_ x) (op_ y) <=> aR x y.

lemma mono2W f (aR : 'a rel) (rR : 'b rel) :
  mono2 f aR rR => homo2 f aR rR.
proof. by move=> + x y - ->. qed.

lemma monoLR ['a 'b] f g (aR : 'a rel) (rR : 'b rel) :
  cancel g f => mono2 f aR rR => forall x y,
    rR (f x) y <=> aR x (g y).
proof. by move=> can_gf mf x y; rewrite -{1}[y]can_gf mf. qed.

lemma monoRL ['a 'b] f g (aR : 'a rel) (rR : 'b rel) :
  cancel g f => mono2 f aR rR => forall x y,
    rR x (f y) <=> aR (g x) y.
proof. by move=> can_gf mf x y; rewrite -{1}can_gf mf. qed.

(* ==================================================================== *)
(* Real-closed domain: ordered integral domain with norm. Mirrors      *)
(* [theories/algebra/Number.ec:RealDomain] but as a TC class on top   *)
(* of [idomain].                                                       *)
(* ==================================================================== *)
type class tcrealdomain <: idomain = {
  op "`|_|" : tcrealdomain -> tcrealdomain
  op ( <= ) : tcrealdomain -> tcrealdomain -> bool
  op ( <  ) : tcrealdomain -> tcrealdomain -> bool
  op minr   : tcrealdomain -> tcrealdomain -> tcrealdomain
  op maxr   : tcrealdomain -> tcrealdomain -> tcrealdomain

  axiom ler_norm_add :
    forall (x y : tcrealdomain), `|x + y| <= `|x| + `|y|
  axiom addr_gt0 :
    forall (x y : tcrealdomain), zero<:tcrealdomain> < x => zero < y => zero < x + y
  axiom norm_eq0 :
    forall (x : tcrealdomain), `|x| = zero<:tcrealdomain> => x = zero
  axiom ger_leVge :
    forall (x y : tcrealdomain),
      zero<:tcrealdomain> <= x => zero <= y => (x <= y) \/ (y <= x)
  axiom normrM :
    forall (x y : tcrealdomain), `|x * y| = `|x| * `|y|
  axiom ler_def :
    forall (x y : tcrealdomain), x <= y <=> `|y - x| = y - x
  axiom ltr_def :
    forall (x y : tcrealdomain), x < y <=> (y <> x) /\ x <= y
  axiom real_axiom :
    forall (x : tcrealdomain), zero<:tcrealdomain> <= x \/ x <= zero
  axiom minrE :
    forall (x y : tcrealdomain), minr x y = if x <= y then x else y
  axiom maxrE :
    forall (x y : tcrealdomain), maxr x y = if y <= x then x else y
}.

(* -------------------------------------------------------------------- *)
section.
declare type t <: tcrealdomain.

(* -------------------------------------------------------------------- *)
(* Sign / positivity / order reflexivity                                *)
(* -------------------------------------------------------------------- *)

lemma ger0_def (x : t): (zero <= x) <=> (`|x| = x).
proof. by rewrite ler_def subr0. qed.

lemma subr_ge0 (x y : t): (zero <= x - y) <=> (y <= x).
proof. by rewrite ger0_def -ler_def. qed.

lemma oppr_ge0 (x : t): (zero <= -x) <=> (x <= zero).
proof. by rewrite -sub0r subr_ge0. qed.

(* -------------------------------------------------------------------- *)
(* TODO Phase 2: port the remaining ~280 [RealDomain] lemmas. Many     *)
(* have proof scripts written with specific term structure in mind     *)
(* ([!mulr1] expecting both [_ * oner] and [oner * _] occurrences,     *)
(* etc.) that interact with our TC abstraction differently than the    *)
(* original concrete-clone form. Each batch needs review for           *)
(* multi-instance disambiguation and rewrite patterns.                 *)
(* -------------------------------------------------------------------- *)

end section.
