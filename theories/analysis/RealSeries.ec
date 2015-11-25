(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import StdRing StdOrder StdBigop Discrete List RealLub RealSeq.
(*---*) import IterOp Bigreal Bigreal.BRA IntOrder RField RealOrder.

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
lemma nosmt summable0: summable (fun (x:'a) => 0%r).
proof. by exists 0%r=> J uqJ; rewrite Bigreal.sumr_const normr0. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt summableN (s : 'a -> real):
  summable s => summable (fun x => -(s x)).
proof.
case=> M h; exists M => J /h; pose F := fun x => `|-s x|.
by rewrite (@eq_bigr _ _ F) // => x _ @/F; rewrite normrN.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt summableD (s1 s2 : 'a -> real):
  summable s1 => summable s2 => summable (fun x => s1 x + s2 x).
proof.
move=> [M1 leM1] [M2 leM2]; exists (M1 + M2)=> J uqJ.
have /ler_add /(_ _ _ (leM2 J _)) := leM1 _ uqJ => // le.
apply/(ler_trans _ _ le); rewrite -big_split /=; apply/ler_sum.
by move=> a _ /=; apply/ler_norm_add.
qed.

(* -------------------------------------------------------------------- *)
op pos (s : 'a -> real) = fun i => if s i < 0%r then 0%r else `|s i|.
op neg (s : 'a -> real) = fun i => if 0%r < s i then 0%r else `|s i|.

lemma nosmt posN (s : 'a -> real) x: pos (fun x => -s x) x = neg s x.
proof. by rewrite /pos /neg /= normrN oppr_lt0. qed.

lemma nosmt negN (s : 'a -> real) x: neg (fun x => -s x) x = pos s x.
proof. by rewrite /pos /neg /= normrN oppr_gt0. qed.

lemma nosmt pos_ge0 (s : 'a -> real) x: 0%r <= pos s x.
proof. by rewrite /pos; case: (s x < _)=> //=; rewrite normr_ge0. qed.

lemma nosmt neg_ge0 (s : 'a -> real) x: 0%r <= neg s x.
proof. by rewrite -posN pos_ge0. qed.

lemma nosmt pos_ger (s : 'a -> real) x: s x <= pos s x.
proof. by rewrite /pos; case: (s x < 0%r)=> [/ltrW|_] //; apply/ler_norm. qed.

lemma nosmt neg_ler (s : 'a -> real) x: -neg s x <= s x.
proof. by rewrite -posN ler_oppl pos_ger. qed.

lemma nosmt abs_pos_ler (s : 'a -> real) x: `|pos s x| <= `|s x|.
proof.
rewrite /pos; case: (s x < 0%r); 1: by rewrite normr0 normr_ge0.
by move=> _; rewrite normr_id.
qed.

lemma nosmt abs_neg_ler (s : 'a -> real) x: `|neg s x| <= `|s x|.
proof. by rewrite -posN -(@normrN (s x)); apply/abs_pos_ler. qed.

lemma nosmt ler_pos (s1 s2 : 'a -> real):
  (forall x, s1 x <= s2 x) => forall x, pos s1 x <= pos s2 x.
proof.
move=> le_s12 x @{1}/pos; case: (s1 x < 0%r); 1: by rewrite pos_ge0.
move/lerNgt=> ^ge0_s1x /ger0_norm -> @/pos; rewrite ltrNge.
have ge0_s2x: 0%r <= s2 x by apply/(ler_trans (s1 x))/le_s12.
by rewrite ge0_s2x /= ger0_norm //; apply/le_s12.
qed.

lemma nosmt ler_neg (s1 s2 : 'a -> real):
  (forall x, s1 x <= s2 x) => forall x, neg s2 x <= neg s1 x.
proof.
move=> le_s12 x; rewrite -!posN; apply/ler_pos=> y /=.
by rewrite ler_oppr opprK le_s12.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt summable_pos (s : 'a -> real) : summable s => summable (pos s).
proof.
case=> M leM; exists M=> J /leM; (pose F := big _ _ _) => le.
by apply(ler_trans F)=> // @/F; apply/ler_sum=> a _; apply/abs_pos_ler.
qed.

lemma nosmt summable_neg (s : 'a -> real) : summable s => summable (neg s).
proof.
case=> M leM; exists M=> J /leM; (pose F := big _ _ _) => le.
by apply(ler_trans F)=> // @/F; apply/ler_sum=> a _; apply/abs_neg_ler.
qed.

(* -------------------------------------------------------------------- *)
op psum (s : 'a -> real) =
  lub (fun M => exists J, uniq J /\ M = big predT (fun x => `|s x|) J).

op sum (s : 'a -> real) =
  if summable s then psum (pos s) - psum (neg s) else 0%r.

(* -------------------------------------------------------------------- *)
lemma nosmt sum_sbl (s : 'a -> real) : summable s =>
  sum s = psum (pos s) - psum (neg s).
proof. by move=> @/sum ->. qed.

(* -------------------------------------------------------------------- *)
axiom nosmt sumE (s : 'a -> real) :
  forall (J : int -> 'a option),
       (forall i j x, J i = Some x => J j = Some x => i = j)
    => (forall x, s x <> 0%r => exists i, 0 <= i /\ J i = Some x)
    => sum s = lim (fun n => big predT s (pmap J (range 0 n))).

(* -------------------------------------------------------------------- *)
lemma nosmt sumE_fin ['a] (s : 'a -> real) (J : 'a list) :
     uniq J
  => (forall x, s x <> 0%r => mem J x)
  => sum s = big predT s J.
proof.
move=> uqJ sJ; rewrite (@sumE _ (fun i => nth None (map Some J) i)).
+ move=> i j x /=; pose n := size J; case: (0 <= i < n); last first.
    by move=> Nrg_i; rewrite nth_out ?size_map.
  case: (0 <= j < n); last by move=> Nrg_j _ _; rewrite nth_out ?size_map.
  move=> lt_jn lt_in; rewrite !(@nth_map x) //= => {2}<-.
  by move/(congr1 (fun x => index x J))=> /=; rewrite !index_uniq.
+ move=> x /sJ sx; exists (index x J); rewrite ?index_ge0 /=.
  by rewrite (@nth_map x) /= 1:index_ge0 1:index_mem // nth_index.
apply/(@limC_eq_from (size J)) => n ge_Jn /=.
rewrite (@range_cat (size J)) 1:size_ge0 // pmap_cat big_cat.
rewrite addrC -(@eq_in_pmap (fun i => None)) ?pmap_none ?big_nil /=.
  by move=> x /mem_range [le_Jx lt_xn]; rewrite nth_default ?size_map.
congr; pose F := fun (i : int) => Some (nth witness J i).
rewrite -(@eq_in_pmap F) /F 2:pmap_some 2:map_nth_range //.
by move=> x /mem_range lt_xJ /=; rewrite (@nth_map witness).
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_psum (s1 s2 : 'a -> real) :
     (forall x, `|s1 x| <= `|s2 x|)
  => summable s2 => psum s1 <= psum s2.
proof.
move=> le_s12 ^sbl_s2 [M2 bs2]; have ^sbl_s1 [M1 bs1]: summable s1.
  exists M2=> J /bs2; (pose F := big _ _ _) => leFM.
  rewrite (ler_trans F) // /F; apply/ler_sum=> a _ /=; apply/le_s12.
apply/ler_lub; first last; first split.
+ by exists 0%r, []=> /=; apply/eq_sym/(@big_nil _ _).
+ by exists M2=> x [J] [+ ->] - /bs2.
+ by exists 0%r, []=> /=; apply/eq_sym/(@big_nil _ _).
move=> x [J] [uqJ ->] /=; exists (big predT (fun x => `|s2 x|) J).
by split; [exists J | apply/ler_sum].
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_sum (s1 s2 : 'a -> real) :
     (forall x, s1 x <= s2 x)
  => summable s1 => summable s2
  => sum s1 <= sum s2.
proof.
move=> le_s12 sbl1 sbl2; rewrite !sum_sbl // ler_sub.
  apply/ler_psum/summable_pos/sbl2=> x.
  by rewrite !ger0_norm ?pos_ge0 ler_pos.
apply/ler_psum/summable_neg/sbl1=> x.
by rewrite !ger0_norm ?neg_ge0 ler_neg.
qed.
