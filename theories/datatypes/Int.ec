(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
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
op "`|_|" = fun x => (0 <= x) ? x : -x.

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
by rewrite lez_eqVlt=> -[->|/ihn].
qed.

lemma nosmt ge0case (p : int -> bool):
     (forall n, n < 0 => p n)
  => p 0
  => (forall n, 0 <= n => p (n+1))
  => forall n, p n.
proof. by move=> ihn ih0 ihp n; apply/ge0ind=> // k /ihp. qed.

lemma nosmt intwlog (p:int -> bool):
  (forall i, p (-i) => p i) =>
  (p 0) =>
  (forall i, 0 <= i => p i => p (i + 1)) =>
  (forall i, p i).
proof.
move=> wlog ih0 ihS; have: forall i, 0 <= i => p i by elim/intind.
move=> {ih0 ihS} ih i; case: (lezWP 0 i); 1: by apply/ih.
by move=> _ le0_i; apply/wlog/ih; rewrite oppz_ge0.
qed.

lemma nosmt sintind (p : int -> bool):
  (forall i, 0 <= i => (forall j, 0 <= j < i => p j) => p i) =>
  (forall i, 0 <= i => p i).
proof.
move=> sih i ^ge0_i; elim/intind: i ge0_i {-2}i (lezz i).
+ move=> i le0_i ge0_i; suff ->: i = 0; first apply/sih=> //.
  * by move=> j; rewrite lez_lt_asym.
  by rewrite eqz_leq le0_i ge0_i.
move=> i ge0_i ih j le_j_Si ge0_j; apply/sih => //.
move=> k [ge0_k lt_kj]; apply/ih=> //; apply/(lez_trans (j-1)).
+ move: lt_kj; rewrite -lez_add1r => lt; rewrite -(lez_add2r 1).
  by rewrite -addzA (addzC (-1)) subzz addz0 addzC.
+ by rewrite -(lez_add2r 1) -addzA (addzC _ 1) subzz addz0.
qed.
