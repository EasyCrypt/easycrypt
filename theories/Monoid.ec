theory Monoid.
  type t.

  op Z : t.
  op ( + ) : t -> t -> t.

  axiom addmA (x y z : t): x + (y + z) = (x + y) + z.
  axiom add0m (x : t): Z + x = x.
  axiom addm0 (x : t): x + Z = x.
end Monoid.

theory Comoid.
  type t.

  op Z : t.
  op ( + ) : t -> t -> t.

  axiom addmA (x y z : t): x + (y + z) = (x + y) + z.
  axiom add0m (x : t): Z + x = x.
  axiom addm0 (x : t): x + Z = x.

  axiom addmC (x y:t): x + y = y + x.
end Comoid.

theory NatMul.
  type t.

  op Z : t.
  op ( + ) : t -> t -> t.

  axiom addmA (x y z : t): x + (y + z) = (x + y) + z.
  axiom add0m (x : t): Z + x = x.
  axiom addm0 (x : t): x + Z = x.

  require import Int.

  op ( +* ) : int -> t -> t. (* NOTE: This is not the notation we're looking for *)
  axiom mulmn0 (x : t): 0 +* x = Z.
  axiom mulmnS (x : t) (n : int): 0 <= n => (n + 1) +* x = x + (n +* x).
end NatMul.

theory NatMulC.

  type t.

  op Z : t.
  op ( + ) : t -> t -> t.

  axiom addmA (x y z : t): x + (y + z) = (x + y) + z.
  axiom add0m (x : t): Z + x = x.
  axiom addm0 (x : t): x + Z = x.

  axiom addmC (x y:t): x + y = y + x.

  require import Int.

  op ( +* ) : int -> t -> t. (* NOTE: This is not the notation we're looking for *)
  axiom mulmn0 (x : t): 0 +* x = Z.
  axiom mulmnS (x : t) (n : int): 0 <= n => (n + 1) +* x = x + (n +* x).
end NatMulC.

theory MonoidT.
  clone import Monoid.

  lemma uniquem0 (x : t):
    (forall y, y + x = y) => x = Z.
  proof strict.
  by intros=> x_neutral; rewrite -add0m x_neutral.
  qed.

  lemma unique0m (x : t):
    (forall y, x + y = y) => x = Z.
  proof strict.
  by intros=> x_neutral; rewrite -addm0 x_neutral.
  qed.
end MonoidT.

require Int.

clone import NatMulC as MInt with
  type t <- int,
  op Z = 0,
  op (+) = Int.(+),
  op ( +* ) = Int.( * )
  proof * by smt.

theory NatMulT.
  clone import NatMul.

  lemma mulmnDm (x : t) (m n : int):
    Int.(<=) 0 m => Int.(<=) 0 n =>
    (m + n) +* x = (m +* x) + (n +* x).
  proof strict.
  intros=> m_pos n_pos; elim/Int.Induction.induction m=> //; rewrite - /MInt.(+).
    by rewrite mulmn0 add0m.
    intros=> i i_pos IH;
       rewrite (_: i + 1 + n = i + n + 1) ? mulmnS // ?addmA - ?IH //=.
       by rewrite - ! MInt.addmA (MInt.addmC 1 n) //=.
       rewrite (mulmnS x (i + n)).
       smt.
  qed.
end NatMulT.

theory SumSet.
  clone import Comoid.

  require import FSet.

  op sum(f:'a -> t, s:'a set) = fold (lambda x s, s + (f x)) Z s.

  lemma sum_nil:
    forall (f:'a -> t), sum f empty = Z
  by (intros=> ?;delta sum;simplify;apply fold_empty).

  lemma sum_rm :
    forall (f:'a -> t) (s:'a set) (x:'a),
    mem x s =>
    sum f s = (f x) + (sum f (rm x s)).
  proof strict.
    simplify sum.
    intros ? ? ? ?.
    rewrite (foldC x (lambda x s, s + (f x))) // /=.
      by intros=> a b X;rewrite -addmA (addmC (f b)) addmA //.
      by rewrite addmC //.
  qed.

  lemma sum_add :
    forall (f:'a -> t) (s:'a set) (x:'a),
    (!mem x s) =>
    sum f (add x s) = (f x) + (sum f s).
  proof strict.
    intros ? ? ? ?.
    rewrite (sum_rm _ _ x);first rewrite mem_add //.
    by rewrite rm_add_eq -rm_nin_id //.
  save.


  lemma sum_in :
    forall (f:'a -> t) (s:'a set),
    sum f s = sum (lambda x, if mem x s then f x else Z) s.
  proof.
    intros ? ?.
    pose f' := (lambda x, if mem x s then f x else Z).
    pose xs := s.
    cut lem : xs <= s => sum f xs = sum f' xs;
      last apply lem;delta xs;apply leq_refl.
    elim/set_comp xs;first rewrite ! sum_nil //.
    intros ? ? ? ?.
    rewrite (sum_rm _ _ (pick s0));first apply mem_pick;trivial.
    rewrite (sum_rm<:'a> f' _ (pick s0));first apply mem_pick;trivial.
    rewrite H0;first apply (leq_tran _ s0);[apply rm_leq|trivial].
    delta f';simplify.
    rewrite (_: mem (pick s0) s = true) //.
    generalize H1;delta xs=> ?.
    by apply eqT;apply H1;apply mem_pick=> //.
  save.

  lemma sum_add2 :
    forall (f:'a -> t) (g:'a -> t) (s:'a set),
    (sum f s) + (sum g s) = sum (lambda x, f x + g x) s.
  proof.
    intros ? ? ?.
    elim/set_comp s;first rewrite ! sum_nil add0m //.
    intros ? ? ?.
    rewrite (sum_rm f _ (pick s0));first apply mem_pick;trivial.
    rewrite (sum_rm g _ (pick s0));first apply mem_pick;trivial.
    rewrite (sum_rm (lambda (x : 'a), f x + g x) _ (pick s0));first apply mem_pick;trivial.
    rewrite -H0.
    simplify.
    by rewrite -addmA (addmA (sum f (rm (pick s0) s0))) (addmC (sum f (rm (pick s0) s0))) - !addmA !addmA //.
  save.

  lemma sum_chind :
    forall (f:'a -> t) (g:'a -> 'a) (gg:'a -> 'a) (s:'a set),
      (forall x, mem x s => gg (g x) = x) =>
    (sum f s) = sum (lambda x, f (gg x)) (img g s).
  proof.
    intros ? ? ? ? ?.
    pose xs := s.
    cut lem : (xs <= s => (sum f xs) = sum (lambda x, f (gg x)) (img g xs));
      last apply lem;delta xs;apply leq_refl.
    elim/set_comp xs;first rewrite ! sum_nil //;
      first rewrite img_empty;rewrite sum_nil;trivial.
    intros ? ? ? ?.
    rewrite (sum_rm _ _ (pick s0));first apply mem_pick;trivial.
    rewrite (sum_rm _ (img g s0) (g (pick s0)));first apply mem_img;apply mem_pick;trivial.
    simplify.
    rewrite H;first apply H2;apply mem_pick;trivial.
    rewrite H1;first apply (leq_tran _ s0);[apply rm_leq|trivial].
    rewrite img_rm.
    cut -> : (forall (x' : 'a), mem x' s0 => g (pick s0) = g x' => pick s0 = x') = true;last by trivial.
    apply eqT=> x ? ?.
    rewrite -H;first apply H2;apply mem_pick;trivial.
    rewrite H4.
    by apply H;first apply H2;trivial.
  save.
end SumSet.

theory SumSetNatMulC.
  clone import NatMulC.
  clone export SumSet with theory Comoid = NatMulC.

  require import FSet.
  require import Int.

  lemma sum_const : forall (k:t) (f:'a->t) (s:'a set),
    (forall (x:'a), mem x s => f x = k) =>
    sum f s = (card s) +* k.
  proof strict.
    intros ? ? ? ?.
    pose xs := s.
    cut lem : xs <= s => sum f xs = (card xs)+*k;last apply lem;delta xs;apply leq_refl.
    elim/set_comp xs;first rewrite sum_nil card_empty=> ?;
      first rewrite mulmn0 //.
    intros ? ? ? ?.
    rewrite (sum_rm _ _ (pick s0));first by apply mem_pick.
    rewrite H1;first by apply (leq_tran _ s0);first apply rm_leq.
    rewrite H;first by apply H2;apply mem_pick.
    rewrite - {3} (add_rm_in (pick s0) s0);first by apply mem_pick.
    rewrite card_add_nin ? mem_rm //.
    rewrite mulmnS //.
    rewrite card_rm_in;first by apply mem_pick.
    smt.
  save.
end SumSetNatMulC.

clone SumSetNatMulC as SumInt with theory NatMulC = MInt.