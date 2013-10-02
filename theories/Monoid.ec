theory Comoid.

theory Base.
  type t.

  op Z: t.
  op (+): t -> t -> t.

  axiom addmC (x y:t): x + y = y + x.
  axiom addmA (x y z:t): x + (y + z) = x + y + z.
  axiom addmZ (x:t): x + Z = x.
end Base.
export Base.

lemma addmCA (x y z:t): (x + y) + z = (x + z) + y.
proof strict.
by rewrite -addmA (addmC y) addmA.
qed.

lemma addmAC (x y z:t): x + (y + z) = y + (x + z).
proof strict.
by rewrite addmA (addmC x) -addmA.
qed.

lemma addmACA (x y z t:t):
  (x + y) + (z + t) = (x + z) + (y + t).
proof strict.
by rewrite addmA -(addmA x) (addmC y) !addmA.
qed.

require import FSet.

op sum (f:'a -> t) (s:'a set) =
  fold (lambda x s, s + (f x)) Z s.

lemma sum_empty (f:'a -> t): sum f empty = Z.
proof strict.
by rewrite /sum fold_empty.
qed.

lemma sum_rm (f:'a -> t) (s:'a set) (x:'a):
  mem x s =>
  sum f s = (f x) + (sum f (rm x s)).
proof strict.
rewrite /sum=> x_in_s.
rewrite (foldC x) // /=; last by rewrite addmC.
by intros=> a b X; rewrite addmCA.
qed.

lemma sum_add (f:'a -> t) (s:'a set) (x:'a):
  (!mem x s) =>
  sum f (add x s) = (f x) + (sum f s).
proof strict.
intros=> x_nin_s;
rewrite (sum_rm _ _ x); first by rewrite mem_add.
by rewrite rm_add_eq -rm_nin_id.
save.

lemma sum_in (f:'a -> t) (s:'a set):
  sum f s = sum (lambda x, if mem x s then f x else Z) s.
proof strict.
cut := leq_refl s; pose {1 3 5} s' := s;
elim/set_comp s'.
  by rewrite 2!sum_empty.
  intros=> {s'} s' s'_nempty IH leq_s'_s;
  rewrite (sum_rm _ _ (pick s')); first by rewrite mem_pick.
  rewrite (sum_rm _ s' (pick s')); first by rewrite mem_pick.
  rewrite IH /=.
    by apply (leq_tran s')=> //; apply rm_leq.
    by rewrite (_: mem (pick s') s) // leq_s'_s // mem_pick.
qed.

lemma sum_add2 (f:'a -> t) (g:'a -> t) (s:'a set):
  (sum f s) + (sum g s) = sum (lambda x, f x + g x) s.
proof strict.
elim/set_comp s;first by rewrite !sum_empty addmZ.
intros {s} s s_nempty IH;
rewrite (sum_rm f _ (pick s)); first by rewrite mem_pick.
rewrite (sum_rm g _ (pick s)); first by rewrite mem_pick.
rewrite (sum_rm _ s (pick s)); first by rewrite mem_pick.
by rewrite -IH /= addmACA.
save.

lemma sum_chind (f:'a -> t) (g:'a -> 'b) (g':'b -> 'a) (s:'a set):
  (forall x, mem x s => g' (g x) = x) =>
  (sum f s) = sum (lambda x, f (g' x)) (img g s).
proof strict.
intros=> pcan_g'_g;
cut := leq_refl s; pose {1 3 4} s' := s.
elim/set_comp s'.
  by rewrite !sum_empty img_empty sum_empty.
  intros {s'} s' s'_nempty IH leq_s'_s;
  rewrite (sum_rm _ _ (pick s'));first by rewrite mem_pick.
  rewrite (sum_rm _ (img g s') (g (pick s'))) /=;
    first by rewrite mem_img // mem_pick.
  rewrite pcan_g'_g; first by apply leq_s'_s; apply mem_pick.
  rewrite IH; first apply (leq_tran s')=> //; apply rm_leq.
  rewrite img_rm;
  (cut ->: (forall x, mem x s' => g (pick s') = g x => pick s' = x) = true)=> //;
  apply eqT=> x x_in_s g_pick;
  rewrite -pcan_g'_g; first by apply leq_s'_s; apply mem_pick.
  by rewrite g_pick pcan_g'_g //; apply leq_s'_s.
save.

lemma sum_filter (f:'a -> t) (p:'a -> bool) (s:'a set):
  (forall x, (!p x) => f x = Z) =>
  sum f (filter p s) = sum f s.
proof strict.
intros=> f_Z; cut := leq_refl s; pose {1 3 4} s' := s;
elim/set_comp s'.
  by rewrite FSet.filter_empty.
  intros=> {s'} s' s'_nempty IH leq_s'_s;
  rewrite (sum_rm _ s' (pick s')); first by apply mem_pick.
  rewrite -IH;first apply (leq_tran s')=> //; apply rm_leq.
  case (p (pick s'))=> p_pick.
    by rewrite (sum_rm _ (filter p s') (pick s')) ?rm_filter // mem_filter;
       split=> //; apply mem_pick.
    by rewrite f_Z // -rm_filter addmC addmZ -rm_nin_id // mem_filter -rw_nand;
       right=> //.
qed.

theory NatMul.
  require import Int.

  op ( * ) : int -> t -> t.

  axiom MulZ : forall (x:t), 0*x = Z.
  axiom MulS : forall n (x:t), 0 <= n => (n + 1) * x = x + n * x.

  lemma sum_const (k:t) (f:'a->t) (s:'a set):
    (forall (x:'a), mem x s => f x = k) =>
    sum f s = (card s)*k.
  proof strict.
  intros=> f_x; pose s' := s;
  (cut -> : s' <= s => sum f s' = (card s')*k)=> //;
    last by delta s'; apply leq_refl.
  elim/set_comp s'.
    by rewrite sum_empty card_empty MulZ.
    intros=> {s'} s' s'_nempty IH leq_s'_s.
    rewrite (sum_rm _ _ (pick s'));first by rewrite mem_pick.
    rewrite IH; first by apply (leq_tran s')=> //; apply rm_leq.
    rewrite f_x; first by apply leq_s'_s; apply mem_pick.
    rewrite card_rm_in; first by apply mem_pick.
    rewrite -MulS; smt.
  qed.
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

pred cpOrs (X:('a cpred) set) (x:'a) = Mbor.sum (lambda (P:'a cpred), P x) X.

pred disj_or (X:('a->bool) set) =
  forall x1 x2, x1 <> x2 => mem x1 X => mem x2 X =>
  forall a, x1 a => !(x2 a).

lemma or_exists (f:'a->bool) s:
  (Mbor.sum f s) <=> (exists x, (mem x s /\ f x)).
split;
  last by intros=> [x [x_in_s f_x]]; rewrite (Mbor.sum_rm _ _ x) // f_x.
intros=> sum_true; pose p := lambda x, mem x s /\ f x; change (exists x, p x);
apply ex_for; delta p=> {p}; generalize sum_true; apply absurd=> /= h.
cut := FSet.leq_refl s; pose {1 3} s' := s;
elim/set_ind s'.
  by rewrite Mbor.sum_empty.
  intros=> {s'} x s' nmem IH leq_adds'_s;
  cut leq_s'_s : s' <= s by (apply (FSet.leq_tran (add x s'))=> //; apply leq_add);
  rewrite Mbor.sum_add // /Mbor.Base.(+) /Bbor.(+) -rw_nor IH // /=;
  cut := h x; rewrite -rw_nand;
  case (mem x s)=> //=;
  by cut := leq_adds'_s x; rewrite mem_add //= => ->.
qed.

lemma mu_ors d (X:('a->bool) set):
  disj_or X =>
  mu d (cpOrs X) = Mrplus.sum (lambda P, mu d P) X.
proof strict.
elim/set_ind X=> {X}.
  intros disj;
  rewrite Mrplus.sum_empty /Mrplus.Base.Z /Brplus.Z -(mu_false d) (mu_eq _ _ cpFalse) //
          /cpOrs => x;
  by rewrite /= Mbor.sum_empty.
  intros f X f_nin_X IH disj;
  rewrite Mrplus.sum_add // /cpOrs.
  cut ->:
    mu d  (lambda (x0 : 'a),
      (Mbor.sum (lambda (P : 'a -> bool), P x0) (add f X))) =
    mu d (cpOr f
      (lambda x0, (Mbor.sum (lambda (P : 'a -> bool), P x0) X)))
    by (apply mu_eq => x0 /=;rewrite Mbor.sum_add //).
  rewrite mu_disjoint;
    last by rewrite -IH // => p q neq_p_q p_in_X q_in_X a;
            apply disj=> //; rewrite mem_add //; left.
  rewrite /cpAnd /cpFalse=> x' /=;
  rewrite -not_def=> [f_x' sum_X];
  generalize f_nin_X disj sum_X.
  elim/set_ind X.
    by rewrite Mbor.sum_empty /Mbor.Base.Z /Bbor.Z /=.
    intros=> g X' g_nin_X' IH' f_nin_addgX' disj sum_addgX'.
    cut f_ng := disj f g  _ _ _ x'.
      by generalize f_nin_addgX'; rewrite mem_add; apply absurd.
      by rewrite mem_add.
      by rewrite 2!mem_add.
    generalize sum_addgX'; rewrite Mbor.sum_add //=.
    cut disj': disj_or (add f X')
      by(rewrite /disj_or=> x1 x2;
         rewrite !mem_add=> neq_x1_x2 x1_in_X' x2_in_X';
         apply disj=> //; rewrite !mem_add -/Bbor.(+) -Bbor.addmA
                                  ?(Bbor.addmC (x1 = g)) ?(Bbor.addmC (x2 = g))
                                  Bbor.addmA /Bbor.(+) /Bbor.(+); left=> //).
    by rewrite /Mbor.Base.(+) /Bbor.(+) -(nnot (g x')) f_ng ?f_x' // /= -not_def;
       apply IH'=> //; generalize f_nin_addgX'; rewrite mem_add -rw_nor.
qed.

require ISet.
import Real.
lemma mean (d:'a distr) (p:'a -> bool):
  ISet.Finite.finite (ISet.create (support d)) =>
  d <> Dempty.dempty =>
  mu d p = Mrplus.sum (lambda x, (mu_x d x)*(mu (Dunit.dunit x) p)) (ISet.Finite.toFSet (ISet.create (support d))).
proof strict.
intros=> fin_supp_d d_nempty.
pose s := FSet.filter p (ISet.Finite.toFSet (ISet.create (support d))).
pose eq := lambda (a b:'a), a = b.
pose pickp := lambda (p:'a -> bool), pick (FSet.filter p s).
pose is := img eq s.
cut pcan_pickp_eq : forall x, mem x s => pickp (eq x) = x.
  delta pickp eq; intros x x_in_s /=.
  apply (_:forall a, mem a (filter (lambda b, x = b) s) => a = x);
    first by (intros=> a; rewrite mem_filter //).
  rewrite mem_pick //; smt.
cut pcan_eq_pickp : forall x, mem x is => eq (pickp x) = x.
  by delta pickp eq; intros x h /=; apply fun_ext=> a /=; smt.
cut p_is_or: mu d p = mu d (cpOrs is).
  rewrite /cpOrs /is mu_in_supp /cpAnd /support /=;
  congr=> //; apply fun_ext=> x /=; rewrite or_exists andC;
  case (in_supp x d /\ p x)=> h.
    rewrite rw_eq_sym rw_eqT; exists (eq x);
    split;last by delta eq=> //.
    by rewrite /s mem_img // mem_filter ISet.Finite.mem_toFSet // /support ISet.mem_create.
    by rewrite rw_eq_sym rw_neqF;
       pose q := (lambda x', mem x' (img eq s) /\ x' x);
       change (! exists x, q x); apply nexists=> a;
       delta q=> /= {q}; rewrite -rw_nand -/is;
       case (mem a is)=> // /= a_in_is;
       cut valA :eq (pickp a) = a by (apply pcan_eq_pickp);
       generalize a_in_is; rewrite /is /s img_def=> [y [<-]];
       rewrite mem_filter ISet.Finite.mem_toFSet // /support ISet.mem_create /=;
       delta eq=> /=; apply absurd=> /= ->.
cut disj_or_is: disj_or is.
  by rewrite /disj_or /is=> x1 x2 h;
     rewrite !img_def=> [a1 [rh1 h1]] [a2 [rh2 h2]] x;
     generalize h; rewrite -rh1 -rh2; delta eq=> /=;
     rewrite (rw_imp (a1=x)) rw_nand; apply absurd=> /= h;
     apply fun_ext=> y /=; generalize h=> [-> ->].
rewrite p_is_or mu_ors // -(Mrplus.sum_filter _ p);
  first by intros=> x h /=; rewrite Dunit.mu_def_notin //.
rewrite -/s (Mrplus.sum_chind _ eq pickp) // /= -/is
        Mrplus.sum_in rw_eq_sym Mrplus.sum_in rw_eq_sym;
congr=> //; apply fun_ext=> P /=; rewrite /mu_x;
case (mem P is)=> memP //;
case (p (pickp P))=> h.
  by rewrite Dunit.mu_def_in // -{1}(pcan_eq_pickp P) //;
     delta eq=> /=; congr=> //; apply fun_ext=> //.
  rewrite Dunit.mu_def_notin //;
  cut :(P = cpFalse);last smt.
  by apply fun_ext=> x; rewrite -(pcan_eq_pickp P) //;
     simplify eq; smt.
qed.
