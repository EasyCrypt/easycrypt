require import AllCore.

inductive iseqv ['a] (e : 'a -> 'a -> bool) =
| IsEqv of
      (forall x, e x x)
    & (forall x y, e x y => e y x)
    & (forall y x z, e x y => e y z => e x z).

op eqv (i : int) (x y : int) : bool.

axiom eqvzz (i x : int) : eqv i x x.
axiom eqv_sym (i x y : int) : eqv i x y => eqv i y x.
axiom eqv_trans (i y x z : int) : eqv i x y => eqv i y z => eqv i x z.

relation eqv.

realize Top.eqv_is_eqv.
move=> x; split.
- by apply: eqvzz.
- by apply: eqv_sym.
- by apply: eqv_trans.
qed.

axiom eqv_addl (i t x y) : eqv i x y => eqv i (x + t) (y + t).
axiom eqv_addr (i t x y) : eqv i x y => eqv i (t + x) (t + y).

morphism CoreInt.add / 1 ==> eqv.

realize Top.add_is_morphism_for_eqv_at_1.
proof. admitted.

morphism CoreInt.add / 2 ==> eqv.

realize Top.add_is_morphism_for_eqv_at_2.
proof. admitted.

pred p : int.

lemma foo (i t1 t2 x y : int) :
  eqv i x y => p x => eqv i ((x + t2)) ((x + t2)).
proof.
move=> e.
rewrite {2 3}e.

abort.
