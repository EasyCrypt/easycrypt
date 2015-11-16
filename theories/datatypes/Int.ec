(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** Begin Import **)
  op zero : int = 0.
  op one  : int = 1.
  op (<)  : int -> int -> bool.
  op (>)  (x y:int) = y < x.
  op (<=) (x y:int) = x < y \/ x = y.
  op (+)  : int -> int -> int.
  op [-]  : int -> int.
  op ( * ): int -> int -> int.

  theory CommutativeGroup.
    axiom Assoc: forall (x y z : int), x + y + z = x + (y + z).
    axiom Unit_def_l: forall (x : int), zero + x = x.
    axiom Unit_def_r: forall (x : int), x + zero = x.
    axiom Inv_def_l: forall (x : int), -x + x = zero.
    axiom Inv_def_r: forall (x : int), x + -x = zero.

    theory Comm.
      axiom Comm: forall (x y : int), x + y = y + x.
    end Comm.
  end CommutativeGroup.
  
  theory Assoc.
    axiom Assoc: forall (x y z : int), x * y * z = x * (y * z).
  end Assoc.

  axiom Mul_distr_l:
    forall (x y z : int), x * (y + z) = x * y + x * z.

  axiom Mul_distr_r:
    forall (x y z : int), (y + z) * x = y * x + z * x.
  
  op (-) (x y:int) = x + -y.
  
  theory Comm.
    axiom Comm: forall (x y : int), x * y = y * x.
  end Comm.
  
  axiom Unitary: forall (x : int), one * x = x.
  
  axiom NonTrivialRing: zero <> one.
  
  op (>=) (x y:int) = y <= x.
  
  axiom Refl: forall (x : int), x <= x.
  
  axiom Trans:
    forall (x y z : int), x <= y => y <= z => x <= z.
  
  axiom Antisymm: forall (x y : int), x <= y => y <= x => x = y.
  
  axiom Total: forall (x y : int), x <= y \/ y <= x.
  
  axiom ZeroLessOne: zero <= one.
  
  axiom CompatOrderAdd:
    forall (x y z : int), x <= y => x + z <= y + z.
  
  axiom CompatOrderMult:
    forall (x y z : int),
      x <= y => zero <= z => x * z <= y * z.
(** End Import **)

(* Random thing *)
op int_of_bool (b : bool) = if b then 1 else 0.

lemma int_of_bool0 (b : bool):
  int_of_bool b = 0 <=> !b.
proof. by case b. qed.

lemma int_of_bool1 (b : bool):
  int_of_bool b = 1 <=> b.
proof. by case b. qed.

(* Group operation *)
op zeroz = 0.
op onez  = 1.

lemma nosmt addz1_neq0 (i : int): 0 <= i => i+1 <> 0
by smt full.

lemma nosmt onez_neq0 : 1 <> 0 
by smt.

lemma nosmt addzA (x y z : int): x + (y + z) = (x + y) + z
by smt.

lemma nosmt addzC (x y : int): x + y = y + x
by smt.

lemma nosmt add0z (x : int): 0 + x = x
by smt full.

lemma nosmt addNz (x : int): (-x) + x = 0
by smt full.

lemma nosmt addzCA (x y z : int): x + (y + z) = y + (x + z)
by smt.

lemma nosmt addzAC (x y z : int): (x + y) + z = (x + z) + y
by smt.

lemma nosmt addIz (x1 x2 y : int): x1 + y = x2 + y => x1 = x2
by smt.

lemma nosmt addzI (x1 x2 y : int): y + x1 = y + x2 => x1 = x2
by smt.

lemma nosmt oppzK (x : int): -(-x) = x
by smt full.

lemma nosmt oppz0: -0 = 0
by smt full.

lemma nosmt addAzN (x y : int): (x + y) - y = x
by smt full.

lemma nosmt mulzA  (x y z : int): x * (y * z) = (x * y) * z
by smt.

lemma nosmt mulzC  (x y : int): x * y = y * x
by smt.

lemma nosmt mul1z  (x : int): 1 * x = x
by smt full.

lemma nosmt mulzDl (x y z : int): (x + y) * z = x * z + y * z
by smt.

lemma subzE (x y : int): x - y = x + (- y)
by smt full.

(** Number theory *)
op "`|_|" (x:int) = (0 <= x) ? x : -x.

lemma nosmt lez_norm_add (x y : int): `|x + y| <= `|x| + `|y|
by smt full.

lemma nosmt addz_gt0     (x y : int): 0 < x => 0 < y => 0 < x + y
by smt full.

lemma nosmt norm_eq0     (x   : int): `|x| = 0 => x = 0
by smt full.

lemma nosmt gez_leVge    (x y : int): 0 <= x => 0 <= y => x <= y \/ y <= x
by smt.

lemma nosmt normzM       (x y : int): `|x * y| = `|x| * `|y|
by smt full.

lemma nosmt lez_def      (x y : int): x <= y <=> `|y - x| = y - x
by smt full.

lemma nosmt ltz_def      (x y : int): x < y <=> ( y <> x /\ x <= y)
by smt full.

lemma nosmt subzz (z : int): z - z = 0 by smt full.

lemma nosmt lezz (z : int): z <= z by [].
lemma nosmt ltzz (z : int): z < z <=> false by smt full.

lemma nosmt ltzNge (x y : int): (x <  y) <=> !(y <= x) by smt full.
lemma nosmt lezNgt (x y : int): (x <= y) <=> !(y <  x) by smt full.

lemma nosmt gez_le (x y : int): (x >= y) <=> (y <= x) by smt full.
lemma nosmt gtz_lt (x y : int): (x >  y) <=> (y <  x) by smt full.

lemma nosmt neq_ltz (x y : int): (x <> y) <=> (x < y \/ y < x) by smt full.
lemma nosmt eqz_leq (x y : int): (x = y) <=> (x <= y /\ y <= x) by [].

lemma nosmt lez_add2l (x y z : int): (x + y <= x + z) <=> (y <= z) by smt.
lemma nosmt lez_add2r (x y z : int): (y + x <= z + x) <=> (y <= z) by smt.

lemma nosmt lez_addl (x y : int) : (x <= x + y) = (0 <= y) by smt.
lemma nosmt lez_addr (x y : int) : (x <= y + x) = (0 <= y) by smt.

lemma nosmt addz_ge0 (x y : int) : 0 <= x => 0 <= y => 0 <= x + y by smt.

lemma nosmt lez_add1r (x y : int): (1 + x <= y) = (x < y) by smt full.

lemma nosmt subz_ge0 x y : (0 <= y - x) = (x <= y) by smt.
lemma nosmt subz_gt0 x y : (0 < y - x) = (x < y) by smt.
lemma nosmt subz_le0 x y : (y - x <= 0) = (y <= x) by smt.
lemma nosmt subz_lt0  x y : (y - x < 0) = (y < x) by smt.

lemma nosmt oppz_ge0 x : (0 <= - x) = (x <= 0) by smt.
lemma nosmt oppz_gt0 x : (0 < - x) = (x < 0) by smt.
lemma nosmt oppz_le0 x : (- x <= 0) = (0 <= x) by smt.
lemma nosmt oppz_lt0 x : (- x < 0) = (0 < x) by smt.

lemma nosmt lezWP (z1 z2 : int) : (z1 <= z2) || (z2 <= z1) by smt.
lemma nosmt ltzW (z1 z2 : int) : (z1 < z2) => (z1 <= z2) by smt.

theory Induction.

  axiom nosmt induction (p:int -> bool):
    (p 0) =>
    (forall i, 0 <= i => p i => p (i + 1)) =>
    (forall i, 0 <= i => p i).

  lemma nosmt strongInduction (p:int -> bool):
    (forall j, 0 <= j => (forall k, 0 <= k < j => p k) => p j) =>
    (forall i, 0 <= i => p i).
  proof strict.
    intros hyp i iVal.
    apply (induction (fun i, forall k, 0 <= k <= i => p k) _ _ i); 1..2:(smt full); smt.
  qed.

  lemma nosmt natind (p : int -> bool):
       (forall n, n <= 0 => p n)
    => (forall n, 0 <= n => p n => p (n+1))
    => forall n, p n.
  proof.
    move=> h0 hS n; case (n < 0); 1: smt full.
    by rewrite -lezNgt; elim/induction n; smt.
  qed.

  lemma nosmt natcase (p : int -> bool):
       (forall n, n <= 0 => p n)
    => (forall n, 0 <= n => p (n+1))
    => forall n, p n.
  proof. smt full. qed.

  lemma nosmt ge0ind (p : int -> bool):
       (forall n, n < 0 => p n)
    => p 0
    => (forall n, 0 <= n => p n => p (n+1))
    => forall n, p n.
  proof.
    move=> hN h0 hS n; case (n < 0); 1: by move=> /hN.
    by rewrite -lezNgt; elim/induction n.
  qed.

  lemma nosmt ge0case (p : int -> bool):
       (forall n, n < 0 => p n)
    => p 0
    => (forall n, 0 <= n => p (n+1))
    => forall n, p n.
  proof. smt full. qed.
end Induction.

(* -------------------------------------------------------------------- *)
(* Fold operator *)

op fold : ('a -> 'a) -> 'a -> int -> 'a.

axiom foldle0 p (f : 'a -> 'a) a: p <= 0 => fold f a p = a.

lemma fold0 (f : 'a -> 'a) a: fold f a 0 = a
by smt.

axiom foldS (f : 'a -> 'a) a n: 0 <= n => fold f a (n+1) = f (fold f a n).

lemma nosmt foldpos (f : 'a -> 'a) a n: 0 < n => f (fold f a (n-1)) = fold f a n
by smt full.

lemma fold_add (f : 'a -> 'a) a n1 n2 : 0 <= n1 => 0 <= n2 =>
   fold f (fold f a n2) n1 = fold f a (n1 + n2).
proof. elim/Induction.induction n1; smt full. qed.

(* -------------------------------------------------------------------- *)
(* Power *)

op ( ^ ) (x:int) (p:int) = fold (( * ) x) 1 p
axiomatized by powE.

lemma nosmt powNeg p x: p <= 0 => x ^ p = 1
by smt.

lemma pow0 x: x ^ 0 = 1
by smt all.

lemma powS p x: 0 <= p => x ^ (p+1) = x * x ^ p
by smt.

lemma pow_add z p1 p2: 0 <= p1 => 0 <= p2 => z^p1 * z^p2 = z^(p1+p2).
proof. 
  move=> Hp1; elim/Induction.induction p2; smt full.
qed.

lemma pow_mul z p1 p2: 0 <= p1 => 0 <= p2 => (z^p1)^p2 = z^(p1*p2).
proof.
  move=> Hp1; elim/Induction.induction p2; smt full.
qed.

lemma powPos z p: 0 < z => 0 < z ^ p.
proof.
 case (0 <= p); intros Hp Hz; last smt full.
 elim/Induction.induction p Hp; smt full.
qed.

lemma pow_Mle (x y:int): 0 <= x <= y => 2^x <= 2^y.
proof.
  intros [leq0_x leqx_y]; cut leq0_y: 0 <= y by smt.
  move: leqx_y; elim /Induction.induction y leq0_y.
    smt.
  smt full.
qed.

(* -------------------------------------------------------------------- *)
(* Diveucl *)
(** Begin Import **)
  op (/%) : int -> int -> int.
  
  op (%%) : int -> int -> int.

  axiom Div_mod: forall (x y:int), y <> zero => x = y * (x /% y) + (x %% y).
  
  axiom Div_bound: forall (x y:int), x >= zero /\ y > zero => zero <= x /% y <= x.
  
  axiom Mod_bound: forall (x y:int), y <> zero => zero <= x %% y < `|y|.
  
  axiom Mod_1: forall (x:int), x %% one = zero.
  
  axiom Div_1: forall (x:int), x /% one = x.
  
  axiom Div_inf: forall (x y:int), zero <= x < y => x /% y = zero.
  
  axiom Div_inf_neg: forall (x y:int), zero < x <= y => (-x) /% y = -one.

  axiom Mod_0: forall (y:int), y > one => 0 %% y = 0.
  
  axiom Div_1_left: forall (y:int), y > one => one /% y = zero.
  
  axiom Div_minus1_left: forall (y:int), y > one => (-one) /% y = -one.
  
  axiom Mod_1_left: forall (y:int), y > one => one %% y = 1.
  
  axiom Mod_minus1_left: forall (y:int), y > one => (-one) %% y = y - one.
  
  axiom Div_mult: forall (x y z:int), x > zero => (x * y + z) /% x = y + z /% x.
  
  axiom Mod_mult: forall (x y z:int), x > zero => (x * y + z) %% x = z %% x.
(** End Import **)

theory Extrema.
  op min (a b:int) = if (a < b) then a else b.

  lemma nosmt minC a b : min a b = min b a
  by smt full.

  lemma nosmt min_lel a b : a <= b => min a b = a
  by smt full.

  lemma nosmt min_ler a b : a <= b => min b a = a
  by smt full.

  lemma nosmt min_is_lb a b:
    min a b <= a /\
    min a b <= b
  by smt full.

  lemma nosmt min_is_glb x a b:
    x <= a => x <= b =>
    x <= min a b
  by smt.

  lemma nosmt min_is_extremum a b:
    min a b = a \/ min a b = b
  by smt.

  op max (a b:int) = if (a < b) then b else a.

  lemma nosmt maxC a b : max a b = max b a
  by smt full.

  lemma nosmt max_lel a b : a <= b => max b a = b
  by smt full.

  lemma nosmt max_ler a b : a <= b => max a b = b
  by smt full.

  lemma leq_maxl m n : m <= max m n
  by smt full.

  lemma leq_maxr m n : n <= max m n
  by smt full.

  lemma geq_max m n1 n2 : (max n1 n2 <= m) <=> (n1 <= m) /\ (n2 <= m)
  by smt full.

  lemma nosmt max_is_ub a b:
    a <= max a b /\
    b <= max a b
  by smt full.

  lemma nosmt max_is_lub x a b:
    a <= x => b <= x =>
    max a b <= x
  by smt.

  lemma nosmt max_is_extremum a b:
    max a b = a \/ max a b = b
  by smt.
end Extrema.
export Extrema.

(* -------------------------------------------------------------------- *)
lemma mulMle : forall (x1 x2 y1 y2:int),
   0 <= x1 <= x2 => 0 <= y1 <= y2 => x1 * y1 <= x2 * y2.
proof.
 intros x1 x2 y1 y2 Hx Hy.
 apply (Trans _ (x1 * y2)).
 rewrite ?(Comm.Comm x1) CompatOrderMult; smt full.
 apply CompatOrderMult; smt full.
qed.
