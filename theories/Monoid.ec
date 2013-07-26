theory Comoid.

theory Base.
  type t.

  op (+) : t -> t -> t.

  op Z : t.

  axiom C : forall x y, x + y = y + x.

  axiom A : forall x y z, x + (y + z) = x + y + z.

  axiom addZ : forall x, x + Z = x.
end Base.
export Base.

require import FSet.

op sum(f:'a -> t, s:'a set) : t =
  fold (lambda x s, s + (f x)) Z s.

lemma sum_empty: forall (f:'a -> t), sum f empty = Z
by (intros=> ?;delta sum;simplify;apply fold_empty).

lemma sum_rm :
  forall (f:'a -> t) (s:'a set) (x:'a),
    mem x s =>
    sum f s = (f x) + (sum f (rm x s)).
proof strict.
  simplify sum.
  intros ? ? ? ?.
  rewrite (foldC x (lambda x s, s + (f x))) // /=.
    by intros=> a b X;rewrite -A (C (f b)) A //.
    by rewrite C //.
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
  cut := leq_refl s.
  pose {1 3 5} xs := s.
  elim/set_comp xs;first by rewrite ! sum_empty //.
  intros ? ? ? ?.
  rewrite (sum_rm _ _ (pick s0));
    first by apply mem_pick.
  rewrite (sum_rm<:'a> (lambda x, if mem x s then f x else Z) _ (pick s0));
    first by apply mem_pick.
  rewrite H0 /=;first by apply (leq_tran _ s0);
    first apply rm_leq.
  rewrite (_: mem (pick s0) s = true) //.
  by apply eqT;apply H1;apply mem_pick=> //.
save.

lemma sum_add2 :
  forall (f:'a -> t) (g:'a -> t) (s:'a set),
  (sum f s) + (sum g s) = sum (lambda x, f x + g x) s.
proof.
  intros ? ? ?.
  elim/set_comp s;first by rewrite ! sum_empty addZ //.
  intros ? ? ?.
  rewrite (sum_rm f _ (pick s0));first apply mem_pick;trivial.
  rewrite (sum_rm g _ (pick s0));first apply mem_pick;trivial.
  rewrite (sum_rm (lambda (x : 'a), f x + g x) _ (pick s0));
    first apply mem_pick=> //.
  rewrite -H0 /=.
  by rewrite -A (A (sum f (rm (pick s0) s0))) (C (sum f (rm (pick s0) s0))) - !A !A //.
save.

lemma sum_chind :
  forall (f:'a -> t) (g:'a -> 'b) (gg:'b -> 'a) (s:'a set),
    (forall x, mem x s => gg (g x) = x) =>
  (sum f s) = sum (lambda x, f (gg x)) (img g s).
proof.
  intros ? ? ? ? ?.
  cut := leq_refl s.
  pose {1 3 4} xs := s.
  elim/set_comp xs;first by rewrite ! sum_empty //;
    first by rewrite img_empty;rewrite sum_empty //.
  intros ? ? ? ?.
  rewrite (sum_rm _ _ (pick s0));first apply mem_pick=> //.
  rewrite (sum_rm _ (img g s0) (g (pick s0)));
    first apply mem_img;apply mem_pick=> //.
  simplify.
  rewrite H;first apply H2;apply mem_pick;trivial.
  rewrite H1;first apply (leq_tran _ s0);[apply rm_leq|trivial].
  rewrite img_rm.
  cut -> : (forall (x' : 'a), mem x' s0 => g (pick s0) = g x' => pick s0 = x') = true;last by trivial.
  apply eqT=> x ? ?.
  rewrite -H;first apply H2;apply mem_pick=> //.
  rewrite H4.
  by apply H;first apply H2=> //.
save.

lemma filter_empty : forall (p:'a -> bool), filter p empty = empty.
proof strict.
intros _.
apply set_ext=> x.
cut := mem_empty x.
rewrite mem_filter -rw_neqF=> -> //.
qed.

lemma rm_filter : forall x (p:'a -> bool) s, rm x (filter p s) = filter p (rm x s).
proof strict.
intros x p s.
apply set_ext=> a.
rewrite mem_filter mem_rm mem_filter mem_rm.
trivial.
qed.

lemma sum_filter :
  forall (f:'a -> t) (p:'a -> bool) (s:'a set),
    (forall x, (!p x) => f x = Z) =>
  sum f (filter p s) = sum f s.
proof strict.
  intros f p s h.
  cut := leq_refl s.
  pose {1 3 4} xs := s.
  elim/set_comp xs;first by rewrite filter_empty //.
  intros s0 nempty sub hrec.
  rewrite (sum_rm _ s0 (pick s0));
    first by apply mem_pick=> //.
  rewrite -sub;first apply (leq_tran _ s0);[apply rm_leq|trivial].
  case (p (pick s0))=> ppick.
    by rewrite (sum_rm _ (filter p s0) (pick s0)) ? rm_filter //;
      first by rewrite mem_filter;split=> //;apply mem_pick=> //.
    by rewrite h // -rm_filter C addZ -rm_nin_id // mem_filter -rw_nand ppick //.
save.

theory NatMul.
  require import Int.

  op ( * ) : int -> t -> t.

  axiom MulZ : forall (x:t), 0*x = Z.

  axiom MulI : forall n (x:t), 0 <= n => (n + 1) * x = x + n * x.

  lemma sum_const : forall (k:t) (f:'a->t) (s:'a set),
    (forall (x:'a), mem x s => f x = k) =>
    sum f s = (card s)*k.
  proof strict.
    intros ? ? ? ?.
    pose xs := s.
    cut lem : xs <= s => sum f xs = (card xs)*k;last apply lem;delta xs;apply leq_refl.
    elim/set_comp xs;first by rewrite sum_empty card_empty=> ?;
      first rewrite MulZ //.
    intros ? ? ? ?.
    rewrite (sum_rm _ _ (pick s0));first apply mem_pick;by trivial.
    rewrite H1;first apply (leq_tran _ s0);[apply rm_leq|by trivial].
    rewrite H;first apply H2;apply mem_pick;by trivial.
    rewrite card_rm_in;first apply mem_pick;by trivial.
    rewrite -MulI //; smt.
  save.
end NatMul.

end Comoid.

require Bool.
clone Comoid.Base as Bbor with
   type t = bool,
   op (+) = (\/),
   op Z = false
   proof * by smt.

require Real.
clone Comoid.Base as Brplus with
   type t = real,
   op (+) = Real.(+),
   op Z = 0%r
   proof * by smt.

clone Comoid as Mbor with theory Base = Bbor.
clone Comoid as Mrplus with
  theory Base = Brplus,
  op NatMul.( * ) = lambda n, (Real.( * ) (n%r))
  proof NatMul.* by smt.

require import FSet.
require import Distr.

pred cpOrs (X:('a->bool) set) (x:'a) = Mbor.sum (lambda (P:'a->bool), P x) X.

pred disj_or (X:('a->bool) set) =
  forall x1 x2,  x1 <> x2 => mem x1 X => mem x2 X =>
      forall a, x1 a => !(x2 a).

lemma or_exists : forall (f:'a->bool) s,
  (Mbor.sum f s) <=> (exists x, (mem x s /\ f x)).
intros d s.
apply iffI;
  last by intros=> [x [h1 h2]];rewrite (Mbor.sum_rm _ _ x) // h2 /Mbor.Base.(+) /Bbor.(+) //.
intros=> h.
pose p := lambda x, mem x s /\ d x.
change (exists x, p x).
apply ex_for.
delta p=> {p}.
generalize h.
apply absurd=> /= h.
cut := FSet.leq_refl s.
pose {1 3} xs := s.
elim/set_ind xs;
  first by rewrite Mbor.sum_empty //.
intros x s' nmem hrec hleq.
cut := h x.
cut leq : (s' <= s) by (apply (FSet.leq_tran _ (add x s'))=> //;apply leq_add).
rewrite Mbor.sum_add // /Mbor.Base.(+) /Bbor.(+) -rw_nor hrec // -rw_nand /=.
case (mem x s)=> // /=.
cut := hleq x.
rewrite mem_add /= => -> //.
qed.

lemma mu_ors :
  forall d (X:('a->bool) set), disj_or X =>
    mu d (cpOrs X) = Mrplus.sum (lambda P, mu d P) X.
proof strict.
intros d X.
elim/set_ind X => {X};
  first by intros Hd;
           rewrite Mrplus.sum_empty /Mrplus.Base.Z /Brplus.Z -(mu_false d);
           apply mu_eq; rewrite /cpOrs=> x /=;
           rewrite Mbor.sum_empty //.
intros x X Hn Hr Hd.
rewrite Mrplus.sum_add // /cpOrs.
cut -> :
  mu d  (lambda (x0 : 'a),
    (Mbor.sum (lambda (P : 'a -> bool), P x0) (add x X))) =
  mu d (cpOr x
    (lambda x0, (Mbor.sum (lambda (P : 'a -> bool), P x0) X)))
by (apply mu_eq => x0 /=;rewrite Mbor.sum_add //).
rewrite mu_disjoint;
  last by rewrite -Hr //;
          intros p1 p2 H_1 H2 H3 b;
          apply (Hd p1 p2 _ _ _ b)=> //;rewrite mem_add //;left;assumption.
rewrite /cpAnd /cpFalse => x0 /=.
rewrite -not_def => [H1 H2].
generalize Hn Hd H2.
elim/ set_ind X;first by rewrite Mbor.sum_empty /Mbor.Base.Z /Bbor.Z /=.
intros x1 X' Hn' Hr' Hn Hd H2.
cut H1' := Hd x x1 _ _ _ x0.
  by rewrite -not_def=> Ht;generalize Ht Hn => ->;rewrite mem_add.
  by rewrite mem_add.
  by rewrite ! mem_add.
generalize H2; rewrite Mbor.sum_add //=.
cut Hd': disj_or (add x X') by (
  rewrite /disj_or;
  intros a1 a2;
  rewrite ! mem_add;
  intros Hneq Hm1 Hm2;
  apply Hd;[
    assumption |
    rewrite ! mem_add -/Bbor.(+) -Bbor.A (Bbor.C (a1 = x1)) Bbor.A /Bbor.(+);left;assumption |
    rewrite ! mem_add -/Bbor.(+) -Bbor.A (Bbor.C (a2 = x1)) Bbor.A /Bbor.(+);left;assumption]).
rewrite /Mbor.Base.(+) /Bbor.(+) -(nnot (x1 x0)) H1' ?H1 // /= -not_def.
apply Hr'=> //.
generalize Hn.
rewrite mem_add -rw_nor //.
save.

require ISet.
import Real.
lemma mean :
  forall (d:'a distr) (p:'a -> bool),
    ISet.Finite.finite (ISet.support d) =>
    d <> Dempty.dempty =>
    mu d p = Mrplus.sum (lambda x, (mu_x d x)*(mu (Dunit.dunit x) p)) (ISet.Finite.toFSet (ISet.support d)).
proof strict.
intros=> d p finite nEmpty.
pose s := FSet.filter p (ISet.Finite.toFSet (ISet.support d)).
pose pi := lambda (a:'a) (b:'a), a = b.
pose piI := lambda (x:'a -> bool), pick (FSet.filter x s).
pose is := img pi s.
cut bij1 : forall x, mem x s => piI (pi x) = x.
  delta piI pi.
  intros x h /=.
  apply (_:forall a, mem a (filter (lambda (b : 'a), x = b) s) => a = x);
    first by (intros=> a;rewrite mem_filter //).
  rewrite mem_pick //.
  smt.
cut bij2 : forall x, mem x is => pi (piI x) = x.
  delta piI pi.
  intros x h /=.
  apply fun_ext=> a /=.
  smt.
cut p_is_or : mu d p = mu d (cpOrs is).
  rewrite /cpOrs /is mu_in_supp /cpAnd /=.
  congr=> //.
  apply fun_ext=> x /=.
  rewrite or_exists andC.
  case (in_supp x d /\ p x)=>h.
    rewrite rw_eq_sym rw_eqT.
    exists (pi x).
    split;last by delta pi=> //.
    by rewrite /s mem_img // mem_filter ISet.Finite.mem_toFSet // /ISet.support ISet.mem_create //.

    rewrite rw_eq_sym rw_neqF.
    pose q := (lambda x0, mem x0 (img pi s) /\ x0 x).
    change (! exists x, q x).
    apply nexists.
    intros a.
    delta q=> /= {q}.
    rewrite -rw_nand -/is.
    case (mem a is)=> // /= hmem.
    cut valA :pi (piI a) = a by (apply bij2=> //).
    generalize hmem.
    rewrite /is /s img_def.
    intros [y [<-]].
    rewrite mem_filter ISet.Finite.mem_toFSet // /ISet.support ISet.mem_create /=.
    delta pi=> /=.
    by apply absurd=> /= -> //.
cut disj_or_is : disj_or is.
  rewrite /disj_or /is.
  intros x1 x2 h.
  rewrite ! img_def=> [a1 [rh1 h1]] [a2 [rh2 h2]].
  intros x.
  generalize h.
  rewrite -rh1 -rh2.
  delta pi=> /=.
  rewrite (rw_imp (a1=x)) rw_nand.
  apply absurd=> /= h.
  apply fun_ext=> y /=.
by generalize h=> [-> ->] //.

rewrite p_is_or mu_ors //.
rewrite -(Mrplus.sum_filter _ p);
  first by intros x h /=;rewrite Dunit.mu_def_notin //.
rewrite -/s (Mrplus.sum_chind _ pi piI) // /= -/is Mrplus.sum_in rw_eq_sym Mrplus.sum_in rw_eq_sym.
congr=> //;apply fun_ext=> P /=.
rewrite /mu_x.
case (mem P is)=> memP //.
case (p (piI P))=> h.
  rewrite Dunit.mu_def_in // -{1}(bij2 P) //.
  delta pi=> /=.
  congr=> //.
  by apply fun_ext=> //.

  rewrite Dunit.mu_def_notin //.
  cut : (P = cpFalse);last smt.
  apply fun_ext.
  intros=> x.
  rewrite -(bij2 P) //.
  simplify pi.
  smt.
save.