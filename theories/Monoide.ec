theory Monoide.

type t.

op (+) : t -> t -> t.

op Z : t.

axiom C : forall x y, x + y = y + x.

axiom A : forall x y z, x + (y + z) = x + y + z.

axiom addZ : forall x, x + Z = x.

theory SumSet.

  require import FSet.

  
axiom foldCA_f: forall (x:'a) (ope:'b -> 'b -> 'b) (f:'a -> 'b) (z:'b) (xs:'a set),
  (forall x y, ope x y = ope y x) =>
  (forall x y z, ope x (ope y z) = ope (ope x y) z) =>
  mem x xs =>
  fold (lambda x s, ope s (f x)) z xs = ope (f x) (fold (lambda x s, ope s (f x)) z (rm x xs)).

  op sum(f:'a -> t, s:'a set) : t =
    fold (lambda x s, s + (f x)) Z s.

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
    by apply (foldCA_f x (+) f Z s _ _ _);[apply C|apply A|trivial].
  save.

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
    let f' = lambda x, if mem x s then f x else Z in
    sum f s = sum f' s.
  proof.
    intros ? ? ?.
    pose xs := s.
    cut lem : xs <= s => sum f xs = sum f' xs;
      last apply lem;delta xs;apply leq_refl.
    elimT set_comp xs;first rewrite ! sum_nil //.
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
    elimT set_comp s;first rewrite ! sum_nil addZ //.
    intros ? ? ?.
    rewrite (sum_rm f _ (pick s0));first apply mem_pick;trivial.
    rewrite (sum_rm g _ (pick s0));first apply mem_pick;trivial.
    rewrite (sum_rm (lambda (x : 'a), f x + g x) _ (pick s0));first apply mem_pick;trivial.
    rewrite -H0.
    simplify.
    by rewrite -A (A (sum f (rm (pick s0) s0))) (C (sum f (rm (pick s0) s0))) - !A !A //.
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
    elimT set_comp xs;first rewrite ! sum_nil //;
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

theory NatMul.
  require import FSet.
  require import Int.
  
  import SumSet.
  
  op ( * ) : int -> t -> t.

  axiom compZ : forall (x:t), 0*x = Z.

  axiom compI : forall n (x:t), n*x = x + (n-1)*x.

  lemma sum_const : forall (k:t) (f:'a->t) (s:'a set),
    (forall (x:'a), mem x s => f x = k) =>
    sum f s = (card s)*k.
  proof strict.
    intros ? ? ? ?.
    pose xs := s.
    cut lem : xs <= s => sum f xs = (card xs)*k;last apply lem;delta xs;apply leq_refl.
    elimT set_comp xs;first rewrite sum_nil card_empty=> ?;
      first rewrite compZ //.
    intros ? ? ? ?.
    rewrite (sum_rm _ _ (pick s0));first apply mem_pick;by trivial.
    rewrite H1;first apply (leq_tran _ s0);[apply rm_leq|by trivial].
    rewrite H;first apply H2;apply mem_pick;by trivial.
    rewrite card_rm_in;first apply mem_pick;by trivial.
    by rewrite -compI //.
  save.
end NatMul.

end Monoide.