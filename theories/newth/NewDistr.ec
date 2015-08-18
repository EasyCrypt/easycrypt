(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import StdRing StdOrder StdBigop RealSeq RealSeries NewList.
(*---*) import IterOp BRA RealOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
pred countable ['a] (E : 'a -> bool) =
  exists (C : int -> 'a option),
    forall x, E x => exists i, C i = Some x.

(* -------------------------------------------------------------------- *)
type 'a distr.

op mu : 'a distr -> ('a -> real).
op mk : ('a -> real) -> 'a distr.

pred isdistr (m : 'a -> real) =
     (forall x, 0%r <= m x)
  /\ (forall s, uniq s => BRA.big predT m s <= 1%r)
  /\ (countable (fun x => m x <> 0%r)).

axiom distrW (P : 'a distr -> bool):
  (forall m, isdistr m => P (mk m)) => forall d, P d.

axiom muK (m : 'a -> real): isdistr m => mu (mk m) = m.
axiom mkK (d : 'a distr): mk (mu d) = d.

lemma ge0_mu ['a] (d : 'a distr) (x : 'a):
  0%r <= mu d x.
proof. by move: d x; elim/distrW=> m dm; rewrite muK //; case: dm. qed.

lemma le1_mu ['a] (d : 'a distr) (x : 'a):
  forall (s : 'a list), uniq s => BRA.big predT (mu d) s <= 1%r.
proof. by move: d x; elim/distrW=> m dm; rewrite muK //; case: dm. qed.      

lemma countable_mu ['a] (d : 'a distr):
  countable (fun x => mu d x <> 0%r).
proof. by move: d; elim/distrW=> m dm; rewrite muK //; case: dm. qed.

lemma eq_distr (d1 d2 : 'a distr):
  (d1 = d2) <=> (forall x, mu d1 x = mu d2 x).
proof.
  split=> [->//|eq_mu]; rewrite -@(mkK d1) -@(mkK d2).
  by congr; apply/fun_ext.
qed.

op prS ['a] (E : 'a -> bool) (d : 'a distr) = fun (x : real) =>
  existsb (fun (s : 'a list) => uniq s /\ x = BRA.big E (mu d) s).

lemma prSP ['a] (E : 'a -> bool) (d : 'a distr) (x : real):
  prS E d x <=> exists s, uniq s /\ x = BRA.big E (mu d) s.
proof. split; first by move/existsbP. by move=> h; apply/existsbP. qed.
  
op pr ['a] (E : 'a -> bool) (d : 'a distr) = lub (prS E d).

lemma prE ['a] (E : 'a -> bool) (d : 'a distr):
  forall (s : int -> 'a option),
       (forall i j x, s i = Some x => s j = Some x => i = j)
    => (forall x, mu d x <> 0%r => exists i, 0 <= i /\ s i = Some x)
    => pr E d = lim (fun n => BRA.big E (mu d) (pmap s (range 0 n))).
proof. admit. qed.

lemma prE_fin ['a] (E : 'a -> bool) (s : 'a list) (d : 'a distr): uniq s =>
      (forall x, mu d x <> 0%r => mem s x)
   => pr E d = BRA.big E (mu d) s.
proof. admit. qed.

(* --------------------------------------------------------------------- *)
theory MUnit.
  op munit ['a] (x : 'a) =
    fun y => if x = y then 1%r else 0%r.

  lemma isdistr (x : 'a): isdistr (munit x).
  proof.
    do! split=> [y|s uq_s|]; 1: by rewrite /munit; case: (x = y).
      case: (mem s x) => [|x_notin_s]; last first.
        rewrite big1_seq // /munit => y [_].
        by apply/absurd; case: (x = y).
      move/bigD1=> -> //; rewrite /munit /= big1_seq //=.
      by move=> y; rewrite /predC1 eq_sym => [->].
    exists (fun i => if i = 0 then Some x else None).
    move=> y; rewrite /munit; case: (x = y)=> // <- _.
    by exists 0.
  qed.

  op dunit ['a] (x : 'a) = mk (munit x).

  (* FIXME: [rewrite /dunit] should not be necessary *)
  lemma dunit1E ['a] (x y : 'a):
    mu (dunit x) y = if x = y then 1%r else 0%r.
  proof. by rewrite /dunit muK // isdistr. qed.

  lemma dunit1xx ['a] (x : 'a): mu (dunit x) x = 1%r.
  proof. by rewrite dunit1E. qed.

  lemma dunitE ['a] (E : 'a -> bool) (x : 'a):
    pr E (dunit x) = if E x then 1%r else 0%r.
  proof.
    rewrite @(prE_fin E [x]) //.
      by move=> y; rewrite dunit1E; case: (x = y).
    by rewrite big_mkcond big_seq1 /= dunit1xx.
  qed.
end MUnit.

(* -------------------------------------------------------------------- *)
theory MUniform.
  op muniform ['a] (s : 'a list) =
    fun x => if mem s x then 1%r / (size (undup s))%r else 0%r.

  lemma isdistr (s : 'a list): isdistr (muniform s).
  proof.
    pose m := size (undup s); do! split=> [y|r uq_r|].
    + rewrite /muniform; case: (mem _ _) => //=.
      by apply/divr_ge0=> //; rewrite from_intMle size_ge0.
    + pose F := fun (x : 'a) => 1%r / m%r.
      rewrite @(bigID _ _ (mem s)) @(eq_bigr _ _ F).
        by rewrite /muniform; move=> x [_ ->].
      rewrite /F big_const big1.
        by rewrite /muniform /predC; move=> x [_ ->].
      admit. (* FIXME: extend Ring with natmul *)
    admit.
  qed.

  op duniform ['a] (s : 'a list) = mk (muniform s).

  lemma duniform1E ['a] (s : 'a list) x:
    mu (duniform s) x = if mem s x then 1%r / (size (undup s))%r else 0%r.
  proof. by rewrite /duniform muK ?isdistr. qed.

  lemma eq_duniformP ['a] (s1 s2 : 'a list):
        (forall x, mem s1 x <=> mem s2 x)
     => (duniform s1 = duniform s2).
  proof.
    rewrite eq_distr => h x; rewrite !duniform1E -h.
    case: (mem _ _)=> //=; rewrite -@(perm_eq_size (undup s2)) //.
      rewrite uniq_perm_eq ?undup_uniq //.
    by move=> y; rewrite !mem_undup h.
  qed.

  lemma duniformE ['a] (E : 'a -> bool) (s : 'a list):
    let n = 1%r / (size (undup s))%r in
    pr E (duniform s) = (count E s)%r * n.
  proof.
    rewrite @(prE_fin E (undup s)) ?undup_uniq //.
      by move=> x; rewrite duniform1E mem_undup; case: (mem _ _).
    admit.
  qed.
end MUniform.

import MUniform.

(* -------------------------------------------------------------------- *)
theory MIntUniform.
  op drange (m n : int) = MUniform.duniform (range m n).

  lemma drangeE (m n x : int):
    mu (drange m n) x = if m <= x < n then 1%r / (n - m)%r else 0%r.
  proof. admit. qed.
(*
    rewrite /drange duniformE ?range_uniq // mem_range.
    case: (m <= x < n)=> //; case=> le_mx lt_xn.
    by rewrite size_range max_ler 1:smt.
*)
end MIntUniform.
