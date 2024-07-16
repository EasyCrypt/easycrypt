(* -------------------------------------------------------------------- *)
require CoreInt.

(* -------------------------------------------------------------------- *)
abbrev ( < ) = CoreInt.lt.
abbrev (<= ) = CoreInt.le.
abbrev ( + ) = CoreInt.add.
abbrev ([-]) = CoreInt.opp.
abbrev ( * ) = CoreInt.mul.

abbrev ( - ) (x y : int) = x + (-y).

abbrev "`|_|" = CoreInt.absz.

lemma intind (p:int -> bool):
  (p 0) =>
  (forall i, 0 <= i => p i => p (i + 1)) =>
  (forall i, 0 <= i => p i).
proof. exact/CoreInt.intind. qed.

(* -------------------------------------------------------------------- *)
axiom addzA     : forall x y z, x + (y + z) = (x + y) + z.
axiom addzC     : forall x y, x + y = y + x.
axiom addz0     : forall x, x + 0 = x.
axiom add0z     : forall x, 0 + x = x.
axiom addzN     : forall x, x - x = 0.
axiom addNz     : forall x, -x + x = 0.
axiom mulzA     : forall x y z, (x * y) * z = x * (y * z).
axiom mulzC     : forall x y, x * y = y * x.
axiom mulz1     : forall x, x * 1 = x.
axiom mul1z     : forall x, 1 * x = x.
axiom mulzDl    : forall x y z, (x + y) * z = x * z + y * z.
axiom mulzDr    : forall x y z, x * (y + z) = x * y + x * z.
axiom onez_neq0 : 1 <> 0.

(* -------------------------------------------------------------------- *)
axiom lezz      : forall x, x <= x.
axiom lez_trans : forall y x z, x <= y => y <= z => x <= z.
axiom ltz_trans : forall y x z, x < y => y < z => x < z.
axiom lez_anti  : forall (x y : int), x <= y <= x => x = y.
axiom lez01     : 0 <= 1.
axiom lez_total : forall x y, x <= y \/ y <= x.

(* -------------------------------------------------------------------- *)
axiom subzz (z : int): z - z = 0.
axiom subz0 (z : int): z - 0 = z.

axiom oppzK: forall (x  : int), -(-x) = x.
axiom oppz0: -0 = 0.

axiom addzCA (x y z : int): x + (y + z) = y + (x + z).
axiom addzAC (x y z : int): (x + y) + z = (x + z) + y.

axiom addzI  (x y z : int): x + y = x + z => y = z.
axiom addIz  (x y z : int): y + x = z + x => y = z.

axiom addzK (y x : int): (x + y) - y = x.
axiom addKz (y x : int): -y + (y + x) = x.

axiom subz_add2r (x y z : int): (x + z) - (y + z) = x - y.

axiom lez_norm_add (x y : int): `|x + y| <= `|x| + `|y|.

axiom addz_gt0 (x y : int): 0 < x => 0 < y => 0 < x + y.

axiom normz_eq0 (x   : int): `|x| = 0 => x = 0.

axiom normzM (x y : int): `|x * y| = `|x| * `|y|.

axiom lez_def (x y : int): x <= y <=> `|y - x| = y - x.
axiom ltz_def (x y : int): x < y <=> ( y <> x /\ x <= y).

axiom ltzz (z : int): z < z <=> false.

axiom ltzNge (x y : int): (x <  y) <=> !(y <= x).
axiom lezNgt (x y : int): (x <= y) <=> !(y <  x).

axiom neq_ltz (x y : int): (x <> y) <=> (x < y \/ y < x).
axiom eqz_leq (x y : int): (x = y) <=> (x <= y /\ y <= x).

axiom lez_add2l (x y z : int): (x + y <= x + z) <=> (y <= z).
axiom lez_add2r (x y z : int): (y + x <= z + x) <=> (y <= z).

axiom ltz_add2l (x y z : int): (x + y <  x + z) <=> (y < z).
axiom ltz_add2r (x y z : int): (y + x <  z + x) <=> (y < z).

axiom lez_addl (x y : int) : (x <= x + y) = (0 <= y).
axiom lez_addr (x y : int) : (x <= y + x) = (0 <= y).

axiom ltz_addl (x y : int) : (x < x + y) = (0 < y).
axiom ltz_addr (x y : int) : (x < y + x) = (0 < y).

axiom addz_ge0 (x y : int) : 0 <= x => 0 <= y => 0 <= x + y.

axiom lez_add1r (x y : int): (1 + x <= y) = (x < y).

axiom subz_ge0 x y : (0 <= y - x) = (x <= y).
axiom subz_gt0 x y : (0 < y - x) = (x < y).
axiom subz_le0 x y : (y - x <= 0) = (y <= x).
axiom subz_lt0  x y : (y - x < 0) = (y < x).

axiom oppz_ge0 x : (0 <= - x) = (x <= 0).
axiom oppz_gt0 x : (0 < - x) = (x < 0).
axiom oppz_le0 x : (- x <= 0) = (0 <= x).
axiom oppz_lt0 x : (- x < 0) = (0 < x).

axiom lezWP (z1 z2 : int) : (z1 <= z2) || (z2 <= z1).
axiom ltzW (z1 z2 : int) : (z1 < z2) => (z1 <= z2).

axiom addz1_neq0 (i : int) : 0 <= i => i+1 <> 0.
axiom add1z_neq0 (i : int) : 0 <= i => 1+i <> 0.
axiom addz1_neqC0 (i : int): 0 <= i => 0 <> i+1.
axiom add1z_neqC0 (i : int): 0 <= i => 0 <> 1+i.

hint rewrite addz_neq0 : addz1_neq0 add1z_neq0 addz1_neqC0 add1z_neqC0.

axiom lez_eqVlt : forall x y, (x <= y) <=> ((x = y) \/ (x < y)).

axiom lez_lt_asym x y : !(x <= y < x).

(* -------------------------------------------------------------------- *)
lemma natind (p : int -> bool):
     (forall n, n <= 0 => p n)
  => (forall n, 0 <= n => p n => p (n+1))
  => forall n, p n.
proof.
move=> ihn ihp n; case: (lezWP 0 n)=> [|_ /ihn] //.
by elim/intind: n => [|i /ihp]; first by apply/ihn.
qed.

lemma natcase (p : int -> bool):
     (forall n, n <= 0 => p n)
  => (forall n, 0 <= n => p (n+1))
  => forall n, p n.
proof. by move=> ihn ihp; elim/natind=> [n /ihn|n /ihp]. qed.

lemma ge0ind (p : int -> bool):
     (forall n, n < 0 => p n)
  => p 0
  => (forall n, 0 <= n => p n => p (n+1))
  => forall n, p n.
proof.
move=> ihn ih0 ihp; elim/natind=> [n|n /ihp] //.
by rewrite lez_eqVlt=> -[->|/ihn].
qed.

lemma ge0case (p : int -> bool):
     (forall n, n < 0 => p n)
  => p 0
  => (forall n, 0 <= n => p (n+1))
  => forall n, p n.
proof. by move=> ihn ih0 ihp n; apply/ge0ind=> // k /ihp. qed.

lemma intwlog (p:int -> bool):
  (forall i, p (-i) => p i) =>
  (p 0) =>
  (forall i, 0 <= i => p i => p (i + 1)) =>
  (forall i, p i).
proof.
move=> wlog ih0 ihS; have: forall i, 0 <= i => p i by elim/intind.
move=> {ih0 ihS} ih i; case: (lezWP 0 i); 1: by apply/ih.
by move=> _ le0_i; apply/wlog/ih; rewrite oppz_ge0.
qed.

lemma intswlog (p:int -> bool):
  ((forall i, 0 <= i => p i) => (forall i, i < 0 => p i)) =>
  (p 0) =>
  (forall i, 0 <= i => p i => p (i + 1)) =>
  (forall i, p i).
proof.
move=> wlog ih0 ihS; have: forall i, 0 <= i => p i by elim/intind.
move=> {ih0 ihS} ih i; case: (0 <= i); 1: by apply/ih.
by rewrite lezNgt /=; apply/wlog/ih.
qed.

lemma sintind (p : int -> bool):
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

(* -------------------------------------------------------------------- *)
lemma lt0n n : (0 <= n) => (0 < n <=> n <> 0).
proof. by rewrite ltz_def => ->. qed.

lemma eqn0Ngt n : (0 <= n) => (n = 0) <=> !(0 < n).
proof. by rewrite eq_sym lez_eqVlt -oraE => -[<-|?->]. qed.

lemma ltzS m n : (m < n+1) <=> (m <= n).
proof. by rewrite -lez_add1r addzC lez_add2r. qed.

lemma leqn0 n : 0 <= n => (n <= 0) <=> (n = 0).
proof. by rewrite eqz_leq => ->. qed.

lemma ltzE m n : (m < n) <=> (m+1 <= n).
proof. by rewrite -(ltz_add2r 1) ltzS. qed.

lemma ltz1 m : (m < 1) <=> (m <= 0).
proof. by rewrite -(ltzS m 0). qed.

lemma ltn1 m : 0 <= m => (m < 1) <=> (m = 0).
proof. by rewrite ltz1 eqz_leq => ->. qed.

(* -------------------------------------------------------------------- *)
op b2i (b : bool) = b ? 1 : 0.

lemma b2i0 : b2i false = 0. proof. by []. qed.
lemma b2i1 : b2i true  = 1. proof. by []. qed.

lemma b2i_or b1 b2: b2i (b1 \/ b2) = b2i b1 + b2i b2 - b2i b1 * b2i b2.
proof. by rewrite /b2i; case: b1 b2 => [|] [|] //=; rewrite oppz0. qed.

lemma b2i_and b1 b2: b2i (b1 /\ b2) = b2i b1 * b2i b2.
proof. by rewrite /b2i; case: b1 b2 => [|] [|]. qed.

lemma le_b2i b1 b2: (b1 => b2) <=> (b2i b1 <= b2i b2).
proof. by case: b1 b2 => [|] [|]. qed.

lemma b2i_ge0 b: 0 <= b2i b.
proof. by case: b. qed.

lemma b2i_le1 b: b2i b <= 1.
proof. by case: b. qed.

lemma b2i_eq1 b : b2i b = 1 <=> b.
proof. by case: b. qed.

lemma b2i_eq0 b : b2i b = 0 <=> !b.
proof. by case: b. qed.

(* -------------------------------------------------------------------- *)
theory IterOp.
  op iteri ['a] : int -> (int -> 'a -> 'a) -> 'a -> 'a.

  axiom iteri0 ['a] n opr (x : 'a):
    n <= 0 => iteri n opr x  = x.

  axiom iteriS ['a] n opr (x : 'a):
    0 <= n => iteri (n+1) opr x = opr n (iteri n opr x).

  lemma iteriS_rw ['a] (n : int) (opr : int -> 'a -> 'a) (x : 'a) :
    0 < n => iteri n opr x = opr (n - 1) (iteri (n - 1) opr x).
  proof.
  by move=> gt0_n; rewrite {1}[n](_ : n = n - 1 + 1) // iteriS //#.
  qed.

  lemma eq_iteri (f1 f2 : int -> 'a -> 'a) k a:
       (forall i a, 0 <= i < k => f1 i a = f2 i a)
    => iteri k f1 a = iteri k f2 a.
  proof.
  elim/natind: k=> [n le0_n|n ge0_n ih] h; first by rewrite !iteri0.
  rewrite !iteriS // h 1:ltz_addl ?ih // => i b [ge0_i lt_in].
  by apply/h; rewrite ge0_i (ltz_trans n) // ltz_addl.
  qed.

  op iter ['a] n f x0 = iteri<:'a> n (fun i => f) x0.

  lemma iter0 ['a] n opr (x : 'a): n <= 0 => iter n opr x = x.
  proof. by move/iteri0<:'a>=> @/iter ->. qed.

  lemma iterS ['a] n opr (x : 'a): 0 <= n =>
    iter (n+1) opr x = opr (iter n opr x).
  proof. by move/iteriS<:'a>=> @/iter ->. qed.

  lemma iter1 ['a] opr (x : 'a): iter 1 opr x = opr x.
  proof. by rewrite (@iterS 0) // iter0. qed.

  lemma iter2 ['a] opr (x : 'a): iter 2 opr x = opr (opr x).
  proof. by rewrite (@iterS 1) // iter1. qed.

  lemma iterSr n opr (x : 'a):
    0 <= n => iter (n + 1) opr x = iter n opr (opr x).
  proof.
    elim: n=> /=; first by rewrite (iterS 0) ?iter0.
    by move=> n geo0 ih; rewrite (iterS (n+1)) 2:ih ?iterS // addz_ge0.
  qed.

  op iterop ['a] (n : int) opr (x z : 'a) : 'a =
    let f = fun i y, if i <= 0 then x else opr x y in
    iteri n f z.

  lemma iterop0 ['a] (n : int) opr (x z : 'a): n <= 0 =>
    iterop n opr x z = z.
  proof. by move=> le0_n; rewrite /iterop /= iteri0. qed.

  lemma iterop1 ['a] opr (x z : 'a): iterop 1 opr x z = x.
  proof. by rewrite /iterop /= (iteriS 0). qed.

  lemma iteropS ['a] (n : int) opr (x z : 'a): 0 <= n =>
    iterop (n+1) opr x z = iter n (opr x) x.
  proof.
    rewrite /iterop; elim: n=> /=; first by rewrite iter0 ?(iteriS 0).
    move=> n ge0_n /= ih; rewrite (@iteriS (n+1)) 1:addz_ge0 //= ih.
    by rewrite {1}addzC lez_add1r ltzNge ge0_n /= iterS.
  qed.
end IterOp.

export IterOp.

(* -------------------------------------------------------------------- *)
op odd (z : int) = iter `|z| [!] false.

lemma odd0 : !odd 0. proof. by rewrite /odd iter0. qed.
lemma odd1 :  odd 1. proof. by rewrite /odd iter1. qed.
lemma odd2 : !odd 2. proof. by rewrite /odd iter2. qed.

hint exact : odd0 odd1 odd2.

lemma oddN z : odd (-z) = odd z by smt().
lemma odd_abs z : odd `|z| = odd z by smt().
lemma oddS z : odd (z + 1) = !(odd z) by smt(iterS).

lemma odd3 : odd 3.
proof. by rewrite (oddS 2) odd2. qed.

lemma oddD z1 z2 : odd (z1 + z2) = (odd z1 = !odd z2).
proof. by elim/intwlog: z1 z2; smt(odd0 oddS oddN). qed.

lemma oddM z1 z2 : odd (z1 * z2) = ((odd z1) /\ (odd z2)).
proof.
elim/intwlog: z1 => [z1 /#| |z1] /=; 1: by rewrite odd0.
by move=> ge0_z1 ih; rewrite mulzDl /= oddS oddD ih /#.
qed.

(* -------------------------------------------------------------------- *)
(* TO BE REMOVED                                                        *)

op fold : ('a -> 'a) -> 'a -> int -> 'a.

axiom foldle0 p (f : 'a -> 'a) a: p <= 0 => fold f a p = a.
axiom foldS (f : 'a -> 'a) a n: 0 <= n => fold f a (n+1) = f (fold f a n).

lemma fold0 (f : 'a -> 'a) a: fold f a 0 = a.
proof. by rewrite foldle0. qed.

lemma foldpos (f : 'a -> 'a) a n: 0 < n =>
  f (fold f a (n-1)) = fold f a n.
proof. by move=> gt0_n; rewrite -foldS /#. qed.

lemma fold_add (f : 'a -> 'a) a n1 n2 : 0 <= n1 => 0 <= n2 =>
   fold f (fold f a n2) n1 = fold f a (n1 + n2).
proof. elim/intind: n1; smt(fold0 foldS). qed.

(* -------------------------------------------------------------------- *)
op min (a b:int) = if (a < b) then a else b.
op max (a b:int) = if (a < b) then b else a.

lemma lez_minl a b :
  a <= b => min a b = a.
proof. by smt(). qed.

lemma lez_minr a b :
  b <= a => min a b = b.
proof. by smt(). qed.

lemma lez_maxl a b :
  b <= a => max a b = a.
proof. by smt(). qed.

lemma lez_maxr a b :
  a <= b => max a b = b.
proof. by smt(). qed.

lemma maxzz : idempotent max by smt().
lemma minzz : idempotent min by smt().
