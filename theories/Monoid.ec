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
  fold (fun x s, s + (f x)) Z s.

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
qed.

lemma sum_add0 (f:'a -> t) (s:'a set) (x:'a):
  (mem x s => f x = Z) =>
  sum f (add x s) = (f x) + (sum f s).
proof strict.
case (mem x s) => /= Hin.
  by rewrite -add_in_id // => ->;rewrite addmC addmZ.
by apply sum_add.  
qed.

lemma sum_disj (f:'a -> t) (s1 s2:'a set) :
  disjoint s1 s2 =>
  sum f (union s1 s2) = sum f s1 + sum f s2.
proof.
 elim /set_ind s1.
   by intros Hd;rewrite union0s sum_empty addmC addmZ.
 intros x s Hx Hrec Hd;rewrite union_add sum_add.
   by generalize Hd;rewrite disjoint_spec mem_union;smt.
 rewrite sum_add.
   by generalize Hd;rewrite disjoint_spec;smt.
 rewrite Hrec;smt.
qed.

lemma sum_eq (f1 f2:'a -> t) (s: 'a set) :  
   (forall x, mem x s => f1 x = f2 x) =>
   sum f1 s = sum f2 s.
proof strict.
  elimT set_ind s.
    by rewrite !sum_empty.
  intros {s} x s Hx Hr Hf;rewrite sum_add // sum_add // Hf;first smt.
  by rewrite Hr // => y Hin;apply Hf;smt.
qed.

lemma sum_in (f:'a -> t) (s:'a set):
  sum f s = sum (fun x, if mem x s then f x else Z) s.
proof strict.
  by apply sum_eq => x /= ->.
qed.

lemma sum_comp (f: t -> t) (g:'a -> t) (s: 'a set):
  (f Z = Z) =>
  (forall x y, f (x + y) = f x + f y) =>
  sum (fun a, f (g a)) s = f (sum g s).
proof.
  intros Hz Ha;elimT set_ind s.
    by rewrite !sum_empty Hz.
  by intros {s} x s Hx Hr;rewrite sum_add // sum_add //= Hr Ha. 
qed.

lemma sum_add2 (f:'a -> t) (g:'a -> t) (s:'a set):
  (sum f s) + (sum g s) = sum (fun x, f x + g x) s.
proof strict.
elim/set_comp s;first by rewrite !sum_empty addmZ.
intros {s} s s_nempty IH;
rewrite (sum_rm f _ (pick s)); first by rewrite mem_pick.
rewrite (sum_rm g _ (pick s)); first by rewrite mem_pick.
rewrite (sum_rm _ s (pick s)); first by rewrite mem_pick.
by rewrite -IH /= addmACA.
qed.

lemma sum_chind (f:'a -> t) (g:'a -> 'b) (g':'b -> 'a) (s:'a set):
  (forall x, mem x s => g' (g x) = x) =>
  (sum f s) = sum (fun x, f (g' x)) (img g s).
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
  apply eqT=> x x_in_s g_pick.
  rewrite -pcan_g'_g; first by apply leq_s'_s.
  by rewrite -g_pick pcan_g'_g //; apply leq_s'_s; apply mem_pick.
qed.

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

require import Int.
import Interval.

op sum_ij (i j : int) (f:int -> t)  = 
  sum f (interval i j).

lemma sum_ij_gt (i j:int) f : 
  i > j => sum_ij i j f = Z.
proof.
 by intros Hlt;rewrite /sum_ij interval_neg // sum_empty.
qed.

lemma sum_ij_split (k i j:int) f:
  i <= k <= j + 1 => sum_ij i j f = sum_ij i (k-1) f + sum_ij k j f.
proof. 
  intros Hbound;rewrite /sum_ij -sum_disj.
    rewrite disjoint_spec=> x;rewrite !Interval.mem_interval;smt.
  congr=> //; apply set_ext=> x; rewrite mem_union; smt.
qed.

lemma sum_ij_eq i f: sum_ij i i f = f i.
proof.
 rewrite /sum_ij Interval.interval_single sum_add;first apply mem_empty.
 rewrite sum_empty;apply addmZ.
qed.

lemma sum_ij_le_r (i j:int) f : 
   i <= j =>
   sum_ij i j f = sum_ij i (j-1) f + f j.
proof.
  intros Hle;rewrite (sum_ij_split j); first by smt.
  by rewrite sum_ij_eq.
qed.

lemma sum_ij_le_l (i j:int) f : 
   i <= j =>
   sum_ij i j f = f i + sum_ij (i+1) j f.
proof.
 intros Hle; rewrite (sum_ij_split (i+1));smt.
qed.

lemma sum_ij_shf (k i j:int) f:
   sum_ij i j f = sum_ij (i-k) (j-k) (fun n, f (k+n)).
proof strict.
  rewrite /sum_ij.
  rewrite (sum_chind f (fun n, n - k) (fun n, k + n)) /=;first smt.
  congr => //;apply set_ext => x;rewrite Interval.mem_interval img_def /=;split.
  intros [x0 [Heq ]];rewrite Interval.mem_interval;subst;smt.
  intros _;exists (x + k);smt.
qed.

lemma sum_ij_shf0 (i j :int) f:
   sum_ij i j f = sum_ij 0 (j-i) (fun n, f (i+n)).
proof strict.
  rewrite (sum_ij_shf i);smt.
qed.

theory NatMul.

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

(* For bool *)
require Bool.

clone Comoid as Mbor with 
   type Base.t <- bool,
   op Base.(+) <- (\/),
   op Base.Z   <- false,
   op NatMul.( * ) = fun (n:int) (b:bool), n <> 0 /\ b
   proof Base.* by smt, NatMul.* by smt.

(* For int *)

theory Miplus.
  clone export Comoid as Miplus with
    type Base.t     <- int,
    op Base.(+)     <- Int.(+),
    op Base.Z       <- 0,
    op NatMul.( * ) <- Int.( * )
    proof Base.* by smt, NatMul.* by smt.

  import Int. import EuclDiv. 
  op sum_n i j = sum_ij i j (fun (n:int), n).

  lemma sum_n_0k (k:int) : 0 <= k => sum_n 0 k = (k*(k + 1))/%2.
  proof.
    rewrite /sum_n;elim /Int.Induction.induction k.
      rewrite sum_ij_eq => /=.
      by elim (ediv_unique 0 2 0 0 _ _ _) => //; smt.
    intros {k} k Hk Hrec;rewrite sum_ij_le_r;first smt.
    cut -> : k + 1 - 1 = k;first smt.
    rewrite Hrec /=.
    elim (ediv_unique ((k + 1) * (k + 1 + 1)) 2 (k * (k + 1) /% 2 + (k + 1)) 0 _ _ _) => //.
    smt.
    cut -> : (k + 1) * (k + 1 + 1) = k * (k+1) + 2*(k+1) by smt.
    elim (ediv_spec (k*(k+1)) 2 _) => //.
    intros _ {1}->.
    cut -> : k * (k + 1) %% 2 = 0;last smt.
    elim (ediv_spec k 2 _) => //;smt.
  qed.

 lemma sum_n_ii (k:int): sum_n k k = k
 by [].
 
 lemma sum_n_ij1 (i j:int) : i <= j => sum_n i (j+1) = sum_n i j + (j+1)
 by [].

 lemma sum_n_i1j (i j : int) : i <= j => i + sum_n (i+1) j = sum_n i j
 by [].

 lemma nosmt sumn_ij_aux (i j:int) : i <= j =>
   sum_n i j = i*((j - i)+1) + sum_n 0 ((j - i)).
 proof.
   intros Hle;rewrite {1} (_: j=i+(j-i));first smt.
   elim /Int.Induction.induction (j-i) => /=;last smt.
    rewrite !sum_n_ii //.
   intros {j Hle} j Hj; rewrite -CommutativeGroup.Assoc sum_n_ij1;smt.
 qed.

 lemma sumn_ij (i j:int) : i <= j =>
   sum_n i j = i*((j - i)+1) + (j-i)*(j-i+1)/%2.
 proof.
   intros Hle; rewrite sumn_ij_aux //;smt.
 qed.

import FSet.Interval.

 lemma sumn_pos (i j:int) : 0 <= i => 0 <= sum_n i j.
 proof.
   case (i <= j) => Hle Hp.
     rewrite sumn_ij => //;smt.
   by rewrite /sum_n sum_ij_gt; first smt.
 qed.

 lemma sumn_le (i j k:int) : i <= j =>  0 <= j => j <= k =>
   sum_n i j <= sum_n i k.    
 proof.
   intros Hij H0j Hjk;rewrite /sum_n /sum_ij.
   cut -> :interval i k = FSet.union (interval i j) (interval (j+1) k).
     by apply FSet.set_ext => x;rewrite FSet.mem_union ?mem_interval;smt.
   rewrite sum_disj.
     by rewrite FSet.disjoint_spec => x;rewrite ?mem_interval;smt.
   smt.
 qed.
   
end Miplus.
  
(* For real *)
require Real.

clone Comoid as Mrplus with
   type Base.t <- real,
   op Base.(+) <- Real.(+),
   op Base.Z   <- 0%r,
   op NatMul.( * ) = fun n, (Real.( * ) (n%r))
  proof Base.* by smt, NatMul.* by smt.

require import FSet.
require import Distr.

pred disj_or (X:('a->bool) set) =
  forall x1 x2, x1 <> x2 => mem x1 X => mem x2 X =>
  forall a, x1 a => !(x2 a).

lemma or_exists (f:'a->bool) s:
  (Mbor.sum f s) <=> (exists x, (mem x s /\ f x)).
proof.
  split;last by intros=> [x [x_in_s f_x]]; rewrite (Mbor.sum_rm _ _ x) // f_x.
  intros=> sum_true; pose p := fun x, mem x s /\ f x; change (exists x, p x);
    apply ex_for; delta p=> {p}; generalize sum_true; apply absurd=> /= h.
  cut := FSet.leq_refl s; pose {1 3} s' := s;elim/set_ind s'.
    by rewrite Mbor.sum_empty.
  intros=> {s'} x s' nmem IH leq_adds'_s;
  cut leq_s'_s : s' <= s by (apply (FSet.leq_tran (add x s'))=> //; 
  apply leq_add);
  rewrite Mbor.sum_add // -rw_nor IH // /=;
  cut := h x; rewrite -rw_nand;
  case (mem x s)=> //=;
  by cut := leq_adds'_s x; rewrite mem_add //= => ->.
qed.

pred cpOrs (X:('a cpred) set) (x:'a) = Mbor.sum (fun (P:'a cpred), P x) X.

lemma cpOrs0 : cpOrs (empty <:'a cpred>) = cpFalse.
proof.
  by apply fun_ext => y;rewrite /cpOrs Mbor.sum_empty.
qed.

lemma cpOrs_add s (p:'a cpred) : 
  cpOrs (FSet.add p s) = cpOr p (cpOrs s).
proof.
  apply fun_ext => y.
  rewrite /cpOrs /cpOr /= !or_exists rw_eq_iff;split=> /=.
    intros [x ];rewrite FSet.mem_add => [ [ ] H H0];first by right;exists x.
    by left;rewrite -H.
  intros [H | [x [H1 H2]]];first by exists p;rewrite FSet.mem_add.
  by exists x; rewrite FSet.mem_add;progress;left.
qed.

lemma mu_ors d (X:('a->bool) set):
  disj_or X =>
  mu d (cpOrs X) = Mrplus.sum (fun P, mu d P) X.
proof strict.
  elim/set_ind X=> {X}.
    by intros disj;rewrite Mrplus.sum_empty cpOrs0 mu_false.
  intros f X f_nin_X IH disj; rewrite Mrplus.sum_add // cpOrs_add mu_disjoint.
    rewrite /cpAnd /cpFalse=> x' /=;
      rewrite -not_def=> [f_x']; generalize f_nin_X disj .
    rewrite /cpOrs or_exists => Hnm Hd [p [Hp]] /=.
    by apply (Hd f p) => //; smt.
  rewrite IH => //.
  by intros x y H1 H2 H3;apply (disj x y) => //;smt.
qed.

require ISet.
import Real.

lemma mean (d:'a distr) (p:'a -> bool):
  ISet.Finite.finite (ISet.create (support d)) =>
  mu d p = 
    Mrplus.sum (fun x, (mu_x d x)*(charfun p x))
        (ISet.Finite.toFSet (ISet.create (support d))).
proof strict.
  intros=> fin_supp_d.
  pose sup := ISet.Finite.toFSet (ISet.create (support d)).
  pose is  := img (fun x y, p x /\ x = y) sup.
  rewrite mu_in_supp (mu_eq d _ (cpOrs is)).
    intros y;rewrite /cpAnd /is /cpOrs /= or_exists rw_eq_iff;split.
      intros [H1 H2];exists ((fun x0 y0, p x0 /\ x0 = y0) y);split => //.
      by apply mem_img;rewrite /sup ISet.Finite.mem_toFSet // ISet.mem_create.
    intros [p' []].
    by rewrite img_def; progress => //;smt. 
  rewrite mu_ors.
    rewrite /is => x1 x2 Hx; rewrite !img_def => [y1 [Heq1 Hm1]] [y2 [Heq2 Hm2]].
    subst; generalize Hx => /= Hx a [Hpa1 Heq1];rewrite -not_def => [Hpa2 Heq2].
    by subst; generalize Hx;rewrite not_def.
  rewrite /is => {is};elimT set_ind sup.
    by rewrite img_empty !Mrplus.sum_empty.
  intros x s Hnm Hrec;rewrite FSet.img_add Mrplus.sum_add0.
    rewrite img_def /= => [x0 [H1 H2]].
    by rewrite (mu_eq d _ cpFalse) //;smt.
  rewrite Mrplus.sum_add // -Hrec /=; congr => //.
  rewrite /charfun /mu_x;case (p x) => //= Hp.
    by apply mu_eq.       
  by rewrite -(mu_false d);apply mu_eq.
qed.
