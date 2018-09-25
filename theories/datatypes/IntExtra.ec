(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int.

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

lemma odd0 : !odd 0. proof. by rewrite iter0. qed.
lemma odd1 :  odd 1. proof. by rewrite iter1. qed.
lemma odd2 : !odd 2. proof. by rewrite iter2. qed.

lemma oddN z : odd (-z) = odd z by [].
lemma odd_abs z : odd `|z| = odd z by [].
lemma oddS z : odd (z + 1) = !(odd z) by [].

lemma oddD z1 z2 : odd (z1 + z2) = (odd z1 = !odd z2).
proof. by elim/intwlog: z1 z2; smt(odd0 oddS oddN). qed.

lemma oddM z1 z2 : odd (z1 * z2) = ((odd z1) /\ (odd z2)).
proof.
elim/intwlog: z1 => [z1 /#| |z1] /=; 1: by rewrite odd0.
by move=> ge0_z1 ih; rewrite mulzDl /= oddS oddD ih /#.
qed.

(* -------------------------------------------------------------------- *)
op argmin (f : int -> 'a) (p : 'a -> bool) =
  choiceb (fun j => 0 <= j /\ p (f j) /\ forall i, 0 <= i < j => !p (f i)) 0.

lemma argmin_out (f : int -> 'a) p: (forall i, !p (f i)) => argmin f p = 0.
proof. by move=> pN; rewrite choiceb_dfl => //= x; rewrite pN. qed.

lemma nosmt argminP_r (f : int -> 'a) p i: 0 <= i => p (f i) =>
     0 <= argmin f p
  /\ p (f (argmin f p))
  /\ forall i, 0 <= i < (argmin f p) => !p (f i).
proof.
pose F := fun i0 => forall j, 0 <= j < i0 => !p (f j).
move=> ge0_i pi; have: exists j, 0 <= j /\ p (f j) /\ F j.
  elim/sintind: i ge0_i pi => i ge0_i ih pi.
  case: (exists j, (0 <= j < i) /\ p (f j)).
    by case=> j [/ih {ih} ih/ih]; apply.
  move=> h; exists i; rewrite pi ge0_i => j lt_ji; apply/negP.
  by move=> pj; apply/h; exists j; rewrite pj.
by move/choicebP/(_ 0); apply.
qed.

lemma argminP (f : int -> 'a) p i: 0 <= i => p (f i) => p (f (argmin f p)).
proof. by move=> ge0_i/(argminP_r _ _ _ ge0_i). qed.

lemma ge0_argmin (f : int -> 'a) p: 0 <= argmin f p.
proof.                          (* FIXME: choice_spec *)
case: (exists i, 0 <= i /\ p (f i)); first by case=> i [] /(argminP_r f p) h /h.
move=> h; rewrite choiceb_dfl ?lez_lt_asym //=.
by move=> x; apply/negP=> [# ge0_x px xmin]; apply/h; exists x.
qed.

lemma argmin_min (f : int -> 'a) p: forall j, 0 <= j < argmin f p => !p (f j).
proof.                          (* FIXME: choice_spec *)
case: (exists i, 0 <= i /\ p (f i)); first by case=> i [] /(argminP_r f p) h /h.
move=> h j; rewrite choiceb_dfl ?lez_lt_asym //=.
by move=> x; apply/negP=> [# ge0_x px xmin]; apply/h; exists x.
qed.

(* -------------------------------------------------------------------- *)
abbrev minz = argmin (fun (i : int) => i).

(* -------------------------------------------------------------------- *)
(* TO BE REMOVED                                                        *)

op fold : ('a -> 'a) -> 'a -> int -> 'a.

axiom foldle0 p (f : 'a -> 'a) a: p <= 0 => fold f a p = a.
axiom foldS (f : 'a -> 'a) a n: 0 <= n => fold f a (n+1) = f (fold f a n).

lemma fold0 (f : 'a -> 'a) a: fold f a 0 = a.
proof. by rewrite foldle0. qed.

lemma nosmt foldpos (f : 'a -> 'a) a n: 0 < n =>
  f (fold f a (n-1)) = fold f a n.
proof. by move=> gt0_n; rewrite -foldS /#. qed.

lemma fold_add (f : 'a -> 'a) a n1 n2 : 0 <= n1 => 0 <= n2 =>
   fold f (fold f a n2) n1 = fold f a (n1 + n2).
proof. elim/intind: n1; smt(fold0 foldS). qed.

(* -------------------------------------------------------------------- *)
(* Power *)

op ( ^ ) (x:int) (p:int) = fold (( * ) x) 1 p
  axiomatized by powE.

lemma nosmt powNeg p x: p <= 0 => x ^ p = 1.
proof. by move=> le0_p; rewrite powE foldle0. qed.

lemma pow0 x: x ^ 0 = 1.
proof. by rewrite powE fold0. qed.

lemma pow1 (n:int): n ^ 1 = n.
proof. by rewrite powE -foldpos //= fold0 mulz1. qed.

lemma powS p x: 0 <= p => x ^ (p+1) = x * x ^ p.
proof. by move=> ge0_p; rewrite !powE foldS. qed.

lemma pow_le0 p x: p <= 0 => x ^ p = 1.
proof. by move=> ?; rewrite powE foldle0. qed.

lemma pow_add z p1 p2: 0 <= p1 => 0 <= p2 => z^p1 * z^p2 = z^(p1+p2).
proof. by move=> ge0_p1; elim/intind: p2; smt(pow0 powS). qed.

lemma pow_mul z p1 p2: 0 <= p1 => 0 <= p2 => (z^p1)^p2 = z^(p1*p2).
proof.
move=> ge0_p1; elim/intind: p2 => /=; first by rewrite !pow0.
by move=> i ge0_i ih; rewrite powS // mulzDr -pow_add /#.
qed.

lemma powPos z p: 0 < z => 0 < z ^ p.
proof.
case: (p <= 0)=> [le0_p|]; first by rewrite pow_le0.
move/ltzNge=> /ltzW h gt0_z; elim/intind: p h; first by rewrite pow0.
by move=> i ge0_i ih; rewrite powS //#.
qed.

lemma pow_Mle x y: 0 <= x <= y => 2^x <= 2^y.
proof.
case=> ge0_x le_xy; have ge0_y : 0 <= y by smt().
by elim/intind: y ge0_y le_xy; smt(powPos powS).
qed.

(* -------------------------------------------------------------------- *)
theory Extrema.
  op min (a b:int) = if (a < b) then a else b.

  lemma nosmt minC a b : min a b = min b a by smt().

  lemma nosmt min_lel a b : a <= b => min a b = a by smt().

  lemma nosmt min_ler a b : a <= b => min b a = a by smt().

  lemma nosmt min_is_lb a b:
    min a b <= a /\
    min a b <= b
  by smt().

  lemma nosmt min_is_glb x a b:
    x <= a => x <= b =>
    x <= min a b
  by smt().

  lemma nosmt min_is_extremum a b:
    min a b = a \/ min a b = b
  by smt().

  op max (a b:int) = if (a < b) then b else a.

  lemma nosmt maxC a b : max a b = max b a by smt().

  lemma nosmt max_lel a b : a <= b => max b a = b by smt().

  lemma nosmt max_ler a b : a <= b => max a b = b by smt().

  lemma leq_maxl m n : m <= max m n by smt().

  lemma leq_maxr m n : n <= max m n by smt().

  lemma geq_max m n1 n2 : (max n1 n2 <= m) <=> (n1 <= m) /\ (n2 <= m)
  by smt().

  lemma gt_max m n1 n2 : (max n1 n2 < m) <=> (n1 < m) /\ (n2 < m)
  by smt().

  lemma nosmt max_is_ub a b:
    a <= max a b /\
    b <= max a b
  by smt().

  lemma nosmt max_is_lub x a b:
    a <= x => b <= x =>
    max a b <= x
  by smt().

  lemma nosmt max_is_extremum a b:
    max a b = a \/ max a b = b
  by smt().
end Extrema.

export Extrema.
