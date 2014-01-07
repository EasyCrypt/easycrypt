require import ExtEq.

(*** Properties of functions (see ssrfun) *)
(** Definitions *)
(* id<:'a> is the identity function on 'a *)
op id (x:'a) = x.

(** Definitions for composition *)
theory Composition.
  op comp (g:'b -> 'c) (f:'a -> 'b): ('a -> 'c) =
    fun x, g (f x).
end Composition.
export Composition.

theory Morphism.
  (** Morphisms *)
  (* Morphism property for unary and binary functions *)
  pred morphism_1 (f:'a -> 'b) aF rF =
    forall x, f (aF x) = rF (f x).

  pred morphism_2 (f:'a -> 'b) aOp rOp =
    forall x y, f (aOp x y) = rOp (f x) (f y).

  (* Homomorphism property for unary and binary relations *)
  pred homomorphism_1 (f:'a -> 'b) aP rP =
    forall x, aP x => rP (f x).

  pred homomorphism_2 (f:'a -> 'b) aR rR =
    forall x y, aR x y => rR (f x) (f y).

  (* Stability property for unary and binary relations *)
  pred monomorphism_1 (f:'a -> 'b) (aP: 'a -> 'c) rP =
    forall x, rP (f x) = aP x.

  pred monmorphism_2 (f:'a -> 'b) (aR:'a -> 'a -> 'c) rR =
    forall x y, rR (f x) (f y) = aR x y.
end Morphism.
export Morphism.

pred injective (f:'a -> 'b) =
  forall (x y:'a), f x = f y => x = y.

pred cancel (f:'a -> 'b) (g:'b -> 'a) =
  comp g f = id.

pred pcancel (f:'a -> 'b) (g:'b -> 'a) (p:'b -> bool) =
  forall (x:'a), p (f x) /\ comp g f x = x.

(* NOTE: ssreflect ocancel deals with options *)
pred ocancel (f:'a -> 'b) (g:'b -> 'a) (p:'a -> bool) =
  forall (x:'a), p x => comp g f x = x.

pred bijective (f:'a -> 'b) =
  exists (g:'b -> 'a), cancel f g /\ cancel g f.

pred involutive (f:'a -> 'a) = cancel f f.

(** Properties of operators *)
(* e is a left-identity element for o *)
pred left_id (e:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o e x = x.

(* e is a right-identity element for o *)
pred right_id (e:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x e = x.

(* inv is a left inverse for o (with identity e) *)
pred left_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o (inv x) x = e.

(* inv is a right inverse for o (with identity e) *)
pred right_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x (inv x) = e.

(* o is its own inverse (with identity e) *)
pred self_inverse (e:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x x = e.

(* o is idempotent *)
pred idempotent (o:'a -> 'a -> 'a) =
  forall (x:'a), o x x = x.

(* o is associative: oA *)
pred associative (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x (o y z) = o (o x y) z.

(* o is commutative: oC *)
pred commutative (o:'a -> 'a -> 'a) =
  forall (x y:'a),  o x y = o y x.

(* o is left-commutative: oAC *)
pred left_commutative (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x (o y z) = o y (o x z).

(* o is right-commutative: oCA *)
pred right_commutative (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o (o x y) z = o (o x z) y.

(* z is a left-zero for o *)
pred left_zero (z:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o z x = z.

(* z is a right-zero for o *)
pred right_zero (z:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x z = z.

(* o1 distributes to the left over o2 *)
pred left_distributive (o1:'a -> 'a -> 'a) (o2:'a -> 'a -> 'a) =
  forall (x y z:'a), o1 (o2 x y) z = o2 (o1 x z) (o1 y z).

(* o1 distributes to the right over o2 *)
pred right_distributive (o1:'a -> 'a -> 'a) (o2:'a -> 'a -> 'a) =
  forall (x y z:'a), o1 x (o2 y z) = o2 (o1 x y) (o1 x y).

(* o1 and o2 satisfy an interchange law *)
pred interchange (o1:'a -> 'a -> 'a) (o2:'a -> 'a -> 'a) =
  forall (x y z t:'a), o1 (o2 x y) (o2 z t) = o2 (o1 x z) (o1 y t).

(* o is injective in its first argument *)
pred left_injective (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x y = o z y => x = z.

(* o is injective in its second argument *)
pred right_injective (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x y = o x z => y = z.

(* o (inv x) is always a left inverse of o x *)
pred left_loop (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x y:'a), o (inv x) (o x y) = y.

(* o x is always a left inverse of o (inv x) *)
pred rev_left_loop (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x y:'a), o x (o (inv x) y) = y.

(* same things with right inverse *)
pred right_loop (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x y:'a), o (o x y) (inv y) = x.

(* ditto *)
pred rev_right_loop (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x y:'a), o (o x (inv y)) y = x.