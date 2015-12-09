(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
op zero   : int = 0.
op one    : int = 1.
op ( < )  : int -> int -> bool.
op (<= )  = fun x y => x < y \/ x = y.
op ( + )  : int -> int -> int.
op ([-])  : int -> int.
op ( * )  : int -> int -> int.
op "`|_|" = fun x =>  (0 <= x) ? x : -x.

abbrev ( - ) (x y : int) = x + (-y).

axiom nosmt addzA     : forall x y z, x + (y + z) = (x + y) + z.
axiom nosmt addzC     : forall x y, x + y = y + x.
axiom nosmt addz0     : forall x, x + 0 = x.
axiom nosmt add0z     : forall x, 0 + x = x.
axiom nosmt addzN     : forall x, x - x = 0.
axiom nosmt addNz     : forall x, -x + x = 0.
axiom nosmt mulzA     : forall x y z, (x * y) * z = x * (y * z).
axiom nosmt mulzC     : forall x y, x * y = y * x.
axiom nosmt mulz1     : forall x, x * 1 = x.
axiom nosmt mul1z     : forall x, 1 * x = x.
axiom nosmt mulzDl    : forall x y z, (x + y) * z = x * z + y * z.
axiom nosmt mulzDr    : forall x y z, x * (y + z) = x * y + x * z.
axiom nosmt onez_neq0 : 1 <> 0.

(* -------------------------------------------------------------------- *)
axiom nosmt lezz      : forall x, x <= x.
axiom nosmt lez_trans : forall y x z, x <= y => y <= z => x <= z.
axiom nosmt ltz_trans : forall y x z, x < y => y < z => x < z.
axiom nosmt lez_anti  : forall (x y : int), x <= y <= x => x = y.
axiom nosmt lez01     : 0 <= 1.
axiom nosmt lez_total : forall x y, x <= y \/ y <= x.

(* -------------------------------------------------------------------- *)
axiom nosmt subzz (z : int): z - z = 0.
axiom nosmt subz0 (z : int): z - 0 = z.

axiom nosmt oppzK: forall (x  : int), -(-x) = x.
axiom nosmt oppz0: -0 = 0.

axiom nosmt addzCA (x y z : int): x + (y + z) = y + (x + z).
axiom nosmt addzAC (x y z : int): (x + y) + z = (x + z) + y.

axiom nosmt addzI  (x y z : int): x + y = x + z => y = z.
axiom nosmt addIz  (x y z : int): y + x = z + x => y = z.

axiom nosmt addzK (y x : int): (x + y) - y = x.
axiom nosmt addKz (y x : int): -y + (y + x) = x.

axiom nosmt subz_add2r (x y z : int): (x + z) - (y + z) = x - y.

axiom nosmt lez_norm_add (x y : int): `|x + y| <= `|x| + `|y|.

axiom nosmt addz_gt0 (x y : int): 0 < x => 0 < y => 0 < x + y.

axiom nosmt normz_eq0 (x   : int): `|x| = 0 => x = 0.

axiom nosmt normzM (x y : int): `|x * y| = `|x| * `|y|.

axiom nosmt lez_def (x y : int): x <= y <=> `|y - x| = y - x.
axiom nosmt ltz_def (x y : int): x < y <=> ( y <> x /\ x <= y).

axiom nosmt ltzz (z : int): z < z <=> false.

axiom nosmt ltzNge (x y : int): (x <  y) <=> !(y <= x).
axiom nosmt lezNgt (x y : int): (x <= y) <=> !(y <  x).

axiom nosmt neq_ltz (x y : int): (x <> y) <=> (x < y \/ y < x).
axiom nosmt eqz_leq (x y : int): (x = y) <=> (x <= y /\ y <= x).

axiom nosmt lez_add2l (x y z : int): (x + y <= x + z) <=> (y <= z).
axiom nosmt lez_add2r (x y z : int): (y + x <= z + x) <=> (y <= z).

axiom nosmt ltz_add2l (x y z : int): (x + y <  x + z) <=> (y < z).
axiom nosmt ltz_add2r (x y z : int): (y + x <  z + x) <=> (y < z).

axiom nosmt lez_addl (x y : int) : (x <= x + y) = (0 <= y).
axiom nosmt lez_addr (x y : int) : (x <= y + x) = (0 <= y).

axiom nosmt ltz_addl (x y : int) : (x < x + y) = (0 < y).
axiom nosmt ltz_addr (x y : int) : (x < y + x) = (0 < y).

axiom nosmt addz_ge0 (x y : int) : 0 <= x => 0 <= y => 0 <= x + y.

axiom nosmt lez_add1r (x y : int): (1 + x <= y) = (x < y).

axiom nosmt subz_ge0 x y : (0 <= y - x) = (x <= y).
axiom nosmt subz_gt0 x y : (0 < y - x) = (x < y).
axiom nosmt subz_le0 x y : (y - x <= 0) = (y <= x).
axiom nosmt subz_lt0  x y : (y - x < 0) = (y < x).

axiom nosmt oppz_ge0 x : (0 <= - x) = (x <= 0).
axiom nosmt oppz_gt0 x : (0 < - x) = (x < 0).
axiom nosmt oppz_le0 x : (- x <= 0) = (0 <= x).
axiom nosmt oppz_lt0 x : (- x < 0) = (0 < x).

axiom nosmt lezWP (z1 z2 : int) : (z1 <= z2) || (z2 <= z1).
axiom nosmt ltzW (z1 z2 : int) : (z1 < z2) => (z1 <= z2).

axiom nosmt addz1_neq0 (i : int) : 0 <= i => i+1 <> 0.
axiom nosmt add1z_neq0 (i : int) : 0 <= i => 1+i <> 0.
axiom nosmt addz1_neqC0 (i : int): 0 <= i => 0 <> i+1.
axiom nosmt add1z_neqC0 (i : int): 0 <= i => 0 <> 1+i.

hint rewrite addz_neq0 : addz1_neq0 add1z_neq0 addz1_neqC0 add1z_neqC0.

axiom nosmt lez_eqVlt : forall x y, (x <= y) <=> ((x = y) \/ (x < y)).

axiom nosmt lez_lt_asym x y : !(x <= y < x).

(* -------------------------------------------------------------------- *)
axiom nosmt intind (p:int -> bool):
  (p 0) =>
  (forall i, 0 <= i => p i => p (i + 1)) =>
  (forall i, 0 <= i => p i).

lemma nosmt natind (p : int -> bool):
     (forall n, n <= 0 => p n)
  => (forall n, 0 <= n => p n => p (n+1))
  => forall n, p n.
proof.
move=> ihn ihp n; case: (lezWP 0 n)=> [|_ /ihn] //.
by elim/intind: n => [|i /ihp]; first by apply/ihn.
qed.

lemma nosmt natcase (p : int -> bool):
     (forall n, n <= 0 => p n)
  => (forall n, 0 <= n => p (n+1))
  => forall n, p n.
proof. by move=> ihn ihp; elim/natind=> [n /ihn|n /ihp]. qed.

lemma nosmt ge0ind (p : int -> bool):
     (forall n, n < 0 => p n)
  => p 0
  => (forall n, 0 <= n => p n => p (n+1))
  => forall n, p n.
proof.
move=> ihn ih0 ihp; elim/natind=> [n|n /ihp] //.
by rewrite lez_eqVlt=> [->|/ihn].
qed.

lemma nosmt ge0case (p : int -> bool):
     (forall n, n < 0 => p n)
  => p 0
  => (forall n, 0 <= n => p (n+1))
  => forall n, p n.
proof. by move=> ihn ih0 ihp n; apply/ge0ind=> // k /ihp. qed.

(* -------------------------------------------------------------------- *)
(* Fold operator *)

op fold : ('a -> 'a) -> 'a -> int -> 'a.

axiom foldle0 p (f : 'a -> 'a) a: p <= 0 => fold f a p = a.

lemma fold0 (f : 'a -> 'a) a: fold f a 0 = a
by smt.

axiom foldS (f : 'a -> 'a) a n: 0 <= n => fold f a (n+1) = f (fold f a n).

lemma nosmt foldpos (f : 'a -> 'a) a n: 0 < n => f (fold f a (n-1)) = fold f a n
by smt.

lemma fold_add (f : 'a -> 'a) a n1 n2 : 0 <= n1 => 0 <= n2 =>
   fold f (fold f a n2) n1 = fold f a (n1 + n2).
proof. elim/intind: n1; smt. qed.

(* -------------------------------------------------------------------- *)
(* Power *)

op ( ^ ) (x:int) (p:int) = fold (( * ) x) 1 p
axiomatized by powE.

lemma nosmt powNeg p x: p <= 0 => x ^ p = 1
by smt.

lemma pow0 x: x ^ 0 = 1
by smt all.

lemma pow1 (n:int): n ^ 1 = n
by smt all.

lemma powS p x: 0 <= p => x ^ (p+1) = x * x ^ p
by smt.

lemma pow_add z p1 p2: 0 <= p1 => 0 <= p2 => z^p1 * z^p2 = z^(p1+p2).
proof. 
  move=> Hp1; elim/intind: p2; smt.
qed.

lemma pow_mul z p1 p2: 0 <= p1 => 0 <= p2 => (z^p1)^p2 = z^(p1*p2).
proof.
  move=> Hp1; elim/intind: p2; smt.
qed.

lemma powPos z p: 0 < z => 0 < z ^ p.
proof.
 case (0 <= p); intros Hp Hz; last smt.
 elim/intind: p Hp; smt.
qed.

lemma pow_Mle (x y:int): 0 <= x <= y => 2^x <= 2^y.
proof.
  intros [leq0_x leqx_y]; cut leq0_y: 0 <= y by smt.
  move: leqx_y; elim/intind: y leq0_y.
    smt.
  smt.
qed.

(* -------------------------------------------------------------------- *)
(* Diveucl *)
(** Begin Import **)
(** End Import **)

theory Extrema.
  op min (a b:int) = if (a < b) then a else b.

  lemma nosmt minC a b : min a b = min b a
  by smt.

  lemma nosmt min_lel a b : a <= b => min a b = a
  by smt.

  lemma nosmt min_ler a b : a <= b => min b a = a
  by smt.

  lemma nosmt min_is_lb a b:
    min a b <= a /\
    min a b <= b
  by smt.

  lemma nosmt min_is_glb x a b:
    x <= a => x <= b =>
    x <= min a b
  by smt.

  lemma nosmt min_is_extremum a b:
    min a b = a \/ min a b = b
  by smt.

  op max (a b:int) = if (a < b) then b else a.

  lemma nosmt maxC a b : max a b = max b a
  by smt.

  lemma nosmt max_lel a b : a <= b => max b a = b
  by smt.

  lemma nosmt max_ler a b : a <= b => max a b = b
  by smt.

  lemma leq_maxl m n : m <= max m n
  by smt.

  lemma leq_maxr m n : n <= max m n
  by smt.

  lemma geq_max m n1 n2 : (max n1 n2 <= m) <=> (n1 <= m) /\ (n2 <= m)
  by smt.

  lemma nosmt max_is_ub a b:
    a <= max a b /\
    b <= max a b
  by smt.

  lemma nosmt max_is_lub x a b:
    a <= x => b <= x =>
    max a b <= x
  by smt.

  lemma nosmt max_is_extremum a b:
    max a b = a \/ max a b = b
  by smt.
end Extrema.
export Extrema.
