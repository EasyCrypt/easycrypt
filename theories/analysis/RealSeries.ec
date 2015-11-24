(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import StdRing StdOrder StdBigop Discrete List RealSeq.
(*---*) import IterOp Bigreal Bigreal.BRA IntOrder RealOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op partial (s : int -> real) (n : int) : real =
  bigi predT s 0 n.

op convergeto (s : int -> real) (x : real) =
  RealSeq.convergeto (partial s) x.

op converge (s : int -> real) =
  exists x, convergeto s x.

(* -------------------------------------------------------------------- *)
op summable (s : 'a -> real) =
  exists M, forall J,
    uniq J => big predT (fun i => `|s i|) J <= M.

axiom sbl_countable (s : 'a -> real) :
  summable s => countable (fun i => s i <> 0%r).

(* -------------------------------------------------------------------- *)
lemma nosmt summableN (s : 'a -> real):
  summable s => summable (fun x => -(s x)).
proof.
case=> M h; exists M => J /h; pose F := fun x => `|-s x|.
by rewrite (@eq_bigr _ _ F) // => x _ @/F; rewrite normrN.
qed.

(* -------------------------------------------------------------------- *)
op pos (s : 'a -> real) = fun i => if s i < 0%r then 0%r else `|s i|.
op neg (s : 'a -> real) = fun i => if 0%r < s i then 0%r else `|s i|.

lemma posN (s : 'a -> real) x: pos (fun x => -s x) x = neg s x.
proof. by rewrite /pos /neg /= normrN oppr_lt0. qed.

lemma negN (s : 'a -> real) x: neg (fun x => -s x) x = pos s x.
proof. by rewrite /pos /neg /= normrN oppr_gt0. qed.

lemma nosmt ler_pos (s1 s2 : 'a -> real):
  (forall x, s1 x <= s2 x) => forall x, pos s1 x <= pos s2 x.
proof. admit. qed.

lemma nosmt ler_neg (s1 s2 : 'a -> real):
  (forall x, s1 x <= s2 x) => forall x, neg s2 x <= neg s1 x.
proof. admit. qed.

lemma summable_pos (s : 'a -> real) : summable s =>
  has_lub (fun M => exists J, uniq J /\ M = big predT (pos s) J).
proof. admit. qed.

lemma summable_neg (s : 'a -> real) : summable s =>
  has_lub (fun M => exists J, uniq J /\ M = big predT (neg s) J).
proof. admit. qed.

(* -------------------------------------------------------------------- *)
op sum (s : 'a -> real) =
  if summable s then
      lub (fun M => exists J, uniq J /\ M = big predT (pos s) J)
    - lub (fun M => exists J, uniq J /\ M = big predT (neg s) J)
  else 0%r.

axiom nosmt sumE (s : 'a -> real) :
  forall (J : int -> 'a option),
       (forall i j x, J i = Some x => J j = Some x => i = j)
    => (forall x, s x <> 0%r => exists i, 0 <= i /\ J i = Some x)
    => sum s = lim (fun n => big predT s (pmap J (range 0 n))).

(* -------------------------------------------------------------------- *)
lemma nosmt sumE_id (s : int -> real) :
    sum (fun x => if x < 0 then 0%r else s x)
  = lim (fun (n : int) => big predT s (range 0 n)).
proof. rewrite (@sumE _ Some).
+ by move=> i j x /= -> ->.
+ move=> x /=; case: (x < 0) => //=; rewrite -lerNgt.
  by move=> ge0_x _; exists x.
apply/(lim_eq 0)=> n ge0_n /=; rewrite -{1}(@map_id (range 0 n)).
rewrite map_pK // !big_seq; apply/eq_bigr=> i /= /mem_range.
by case=> /IntOrder.lerNgt ->.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt sumE_fin ['a] (s : 'a -> real) (J : 'a list) :
     uniq J
  => (forall x, s x <> 0%r => mem J x)
  => sum s = big predT s J.
proof.
move=> uqJ sJ; rewrite (@sumE _ (fun i => nth None (map Some J) i)).
+ move=> i j x /=. admit.
+ move=> x /sJ sx; exists (index x J); rewrite ?index_ge0 /=.
  by rewrite (@nth_map x) /= 1:index_ge0 1:index_mem // nth_index.
admit.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_lub (E1 E2 : real -> bool) :
     (forall x, E1 x => exists y, E2 y /\ x <= y)
  => has_lub E2 => lub E1 <= lub E2.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_sum (s1 s2 : 'a -> real) :
     (forall x, s1 x <= s2 x)
  => summable s1 => summable s2
  => sum s1 <= sum s2.
proof.
move=> le_s12 sum_s1 sum_s2 @/sum; rewrite sum_s1 sum_s2 /=.
rewrite ler_sub; apply/ler_lub=> /=.
+ move=> x [J] [uqJ ->]; exists (big predT (pos s2) J).
  by split; [exists J | apply/ler_sum => y _; apply/ler_pos].
+ by apply/summable_pos.
+ move=> x [J] [uqJ ->]; exists (big predT (neg s1) J).
  by split; [exists J | apply/ler_sum => y _; apply/ler_neg].
+ by apply/summable_neg.
qed.
