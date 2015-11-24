(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

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

op sum (f:'a -> t) (s:'a fset) =
  fold (fun x s, s + (f x)) Z s.

lemma sum_empty (f:'a -> t): sum f fset0 = Z.
proof strict.
by rewrite /sum fold0.
qed.

lemma sum_rm (f:'a -> t) (s:'a fset) (x:'a):
  mem s x =>
  sum f s = (f x) + (sum f (s `\` fset1 x)).
proof strict.
rewrite /sum=> x_in_s.
rewrite (foldC x) // /=; last by rewrite addmC.
by intros=> a b X; rewrite addmCA.
qed.

lemma sum_add (f:'a -> t) (s:'a fset) (x:'a):
  (!mem s x) =>
  sum f (s `|` fset1 x) = (f x) + (sum f s).
proof strict.
intros=> x_nin_s;
rewrite (sum_rm _ _ x); first by rewrite in_fsetU in_fset1.
rewrite fsetDUl fsetDv fsetU0.
have -> //=: s `\` fset1 x = s. (* FIXME: views *)
by apply/fsetP=> x'; rewrite in_fsetD in_fset1; case (x' = x).
qed.

lemma sum_add0 (f:'a -> t) (s:'a fset) (x:'a):
  (mem s x => f x = Z) =>
  sum f (s `|` fset1 x) = (f x) + (sum f s).
proof strict.
case (mem s x) => /= Hin.  
  have -> ->: s `|` fset1 x = s
    by apply/fsetP=> x'; rewrite in_fsetU in_fset1; case (x' = x).
  by rewrite addmC addmZ.
by apply sum_add.  
qed.

lemma sum_disj (f:'a -> t) (s1 s2:'a fset) :
  s1 `&` s2 = fset0 =>
  sum f (s1 `|` s2) = sum f s1 + sum f s2.
proof -strict.
 elim/fset_ind s1.
   by move=> hd; rewrite fset0U sum_empty addmC addmZ.
 by intros x s Hx Hrec Hd; rewrite sum_add // -fsetUAC sum_add 1:smt Hrec smt.
qed.

lemma sum_eq (f1 f2:'a -> t) (s: 'a fset) :
   (forall x, mem s x => f1 x = f2 x) =>
   sum f1 s = sum f2 s.
proof strict.
  elim/fset_ind s.
    by rewrite !sum_empty.
  intros x s Hx Hr Hf; rewrite sum_add // sum_add // Hf;first smt.
  by rewrite Hr // => y Hin;apply Hf;smt.
qed.

lemma sum_in (f:'a -> t) (s:'a fset):
  sum f s = sum (fun x, if mem s x then f x else Z) s.
proof strict.
  by apply sum_eq => x /= ->.
qed.

lemma sum_comp (f: t -> t) (g:'a -> t) (s: 'a fset):
  (f Z = Z) =>
  (forall x y, f (x + y) = f x + f y) =>
  sum (fun a, f (g a)) s = f (sum g s).
proof -strict.
  intros Hz Ha;elim/fset_ind s.
    by rewrite !sum_empty Hz.
  by intros x s Hx Hr; rewrite sum_add // sum_add //= Hr Ha. 
qed.

lemma sum_add2 (f:'a -> t) (g:'a -> t) (s:'a fset):
  (sum f s) + (sum g s) = sum (fun x, f x + g x) s.
proof strict.
elim/fset_ind s=> [|x s x_notin_s ih].
  by rewrite !sum_empty addmZ.
by rewrite !sum_add// addmACA ih.
qed.

lemma sum_chind (f:'a -> t) (g:'a -> 'b) (g':'b -> 'a) (s:'a fset):
  (forall x, mem s x => g' (g x) = x) =>
  (sum f s) = sum (fun x, f (g' x)) (image g s).
proof strict.
intros=> pcan_g'_g; have: s <= s by done.
elim/fset_ind {1 3 4}s.
  by rewrite image0 !sum_empty.
  move=> x s' x_notin_s' ih leq_s'_s.
  rewrite sum_add// ih 1:smt.
  rewrite imageU image1 sum_add /=.
    rewrite imageP -negP=> [a] [a_in_s' ga_eq_gx].
    have:= pcan_g'_g a _. smt.
    have:= pcan_g'_g x _. smt.
    by rewrite ga_eq_gx=> -> ->>.
  rewrite pcan_g'_g //=.
  by apply/leq_s'_s; rewrite in_fsetU in_fset1.
qed.

lemma sum_filter (f:'a -> t) (p:'a -> bool) (s:'a fset):
  (forall x, (!p x) => f x = Z) =>
  sum f (filter p s) = sum f s.
proof strict.
intros=> f_Z; have: s <= s by done.
elim/fset_ind {1 3 4}s.
  by rewrite FSet.filter0.
  move=> x s' x_notin_s' ih leq_s'_s.
  rewrite filterU filter1; case (p x)=> //= [|/f_Z].
    by rewrite !sum_add// 1:in_filter 1:x_notin_s'// ih 1:smt.
  by rewrite fsetU0 sum_add// addmC => ->; rewrite addmZ ih 1:smt.
qed.

require import Int IntDiv.
import List.Iota.

op sum_ij (i j : int) (f:int -> t)  = 
  sum f (oflist (iota_ i (j - i + 1))).

lemma sum_ij_gt (i j:int) f : 
  j < i => sum_ij i j f = Z.
proof -strict.
  by move=> gt_i_j; rewrite /sum_ij iota0 1:smt -set0E sum_empty.
qed.

lemma sum_ij_split (k i j:int) f:
  i <= k <= j + 1 => sum_ij i j f = sum_ij i (k-1) f + sum_ij k j f.
proof -strict. 
  intros Hbound;rewrite /sum_ij -sum_disj.
    by apply/fsetP=> x; rewrite in_fset0 /= in_fsetI !mem_oflist !mem_iota smt.
  by congr; apply/fsetP=> x; rewrite in_fsetU !mem_oflist !mem_iota; smt.
qed.

lemma sum_ij_eq i f: sum_ij i i f = f i.
proof -strict.
  by rewrite /sum_ij /= iota1 -set1E /sum fold1 /= addmC addmZ.
qed.

lemma sum_ij_le_r (i j:int) f : 
   i <= j =>
   sum_ij i j f = sum_ij i (j-1) f + f j.
proof -strict.
  intros Hle;rewrite (sum_ij_split j); first by smt.
  by rewrite sum_ij_eq.
qed.

lemma sum_ij_le_l (i j:int) f : 
   i <= j =>
   sum_ij i j f = f i + sum_ij (i+1) j f.
proof -strict.
 intros Hle; rewrite (sum_ij_split (i+1));smt.
qed.

lemma sum_ij_shf (k i j:int) f:
   sum_ij i j f = sum_ij (i-k) (j-k) (fun n, f (k+n)).
proof strict.
  rewrite /sum_ij.
  rewrite (sum_chind f (fun n, n - k) (fun n, k + n)) /=;first smt.
  congr. apply/fsetP=> x; rewrite !mem_oflist !mem_iota imageP /=.
  by split=> [[a]|h]; [|exists (x + k)]; rewrite mem_oflist mem_iota; smt.
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

  lemma sum_const (k:t) (f:'a->t) (s:'a fset):
    (forall (x:'a), mem s x => f x = k) =>
    sum f s = (card s)*k.
  proof strict.
  intros=> f_x; pose s' := s.
  cut -> //: s' <= s => sum f s' = (card s') * k;
    last by smt. (* FIXME *)
  elim/fset_ind s'.
    by rewrite sum_empty fcards0 MulZ.
  move=> x s' x_notin_s' ih leq_s'_s.
  rewrite sum_add//. search (`|`) fset1.
  rewrite ih 1:smt fcardUI_indep 2:fcard1 //.
    by apply/fsetP=> x'; rewrite !inE; case (x' = x)=> [->|//=]; rewrite x_notin_s'.
  smt.
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

require import IntDiv.

(* For int *)
theory Miplus.
  clone export Comoid as Miplus with
    type Base.t     <- int,
    op Base.(+)     <- Int.(+),
    op Base.Z       <- 0,
    op NatMul.( * ) <- Int.( * )
    proof Base.* by smt, NatMul.* by smt.

  import Int.
  op sum_n i j = sum_ij i j (fun (n:int), n).

  lemma sum_n_0k (k:int) : 0 <= k => sum_n 0 k = (k*(k + 1))%/2.
  proof -strict.
    rewrite /sum_n;elim k.
      by rewrite sum_ij_eq => /=; smt all.
    intros k Hk Hrec;rewrite sum_ij_le_r;first smt.
    cut -> : k + 1 - 1 = k;first smt.
    rewrite Hrec /=.
    have ->: (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) by smt.
    rewrite (addzC (k * (k + 1))) Div_mult 1:smt.
    by rewrite addzC.
  qed.

 lemma sum_n_ii (k:int): sum_n k k = k
 by [].
 
 lemma sum_n_ij1 (i j:int) : i <= j => sum_n i (j+1) = sum_n i j + (j+1)
 by [].

 lemma sum_n_i1j (i j : int) : i <= j => i + sum_n (i+1) j = sum_n i j
 by [].

 lemma nosmt sumn_ij_aux (i j:int) : i <= j =>
   sum_n i j = i*((j - i)+1) + sum_n 0 ((j - i)).
 proof -strict.
   intros Hle;rewrite {1} (_: j=i+(j-i));first smt.
   cut: 0 <= (j-i) by smt.
   elim (j-i)=> //=.
     by rewrite !sum_n_ii.
   intros {j Hle} j Hj; rewrite -CommutativeGroup.Assoc sum_n_ij1;smt.
 qed.

 lemma sumn_ij (i j:int) : i <= j =>
   sum_n i j = i*((j - i)+1) + (j-i)*(j-i+1)%/2.
 proof -strict.
   intros Hle; rewrite sumn_ij_aux //;smt.
 qed.

 lemma sumn_pos (i j:int) : 0 <= i => 0 <= sum_n i j.
 proof.
   case (i <= j) => Hle Hp.
     rewrite sumn_ij=> //.
     have h: 0 <= (j - i) * (j - i + 1) by smt.
     have: 0 <= (j - i) * (j - i + 1) %/ 2 by smt.
     have: 0 <= i * (j - i + 1) by smt.
     smt.
   by rewrite /sum_n sum_ij_gt; first smt.
 qed.

 import FSet.
 import List.Iota.

 lemma sumn_le (i j k:int) : i <= j =>  0 <= j => j <= k =>
   sum_n i j <= sum_n i k.    
 proof -strict.
   intros Hij H0j Hjk;rewrite /sum_n /sum_ij.
   cut ->: oflist (iota_ i (k - i + 1))
           = oflist (iota_ i (j - i + 1)) `|` oflist (iota_ (j + 1) (k - (j + 1) + 1)).
     by apply/fsetP=> x; rewrite in_fsetU !mem_oflist !mem_iota; smt.
   rewrite sum_disj.
     by apply/fsetP=> x; rewrite in_fset0 /= in_fsetI !mem_oflist !mem_iota; smt.
   rewrite -!/(sum_ij _ _ _) -!/(sum_n _ _).
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
import Int.  
import Real.

lemma NatMul_mul : forall (n:int) (r:real), 0 <= n => 
    Mrplus.NatMul.( * ) n r = n%r * r.
proof.    
  move => n r;elim n;smt.
qed.

require import FSet.
require import Distr.

pred disj_or (X:('a->bool) fset) =
  forall x1 x2, x1 <> x2 => mem X x1 => mem X x2 =>
  forall a, x1 a => !(x2 a).

lemma or_exists (f:'a->bool) s:
  (Mbor.sum f s) <=> (exists x, (mem s x /\ f x)).
proof -strict.
  split;last by intros=> [x [x_in_s f_x]]; rewrite (Mbor.sum_rm _ _ x) // f_x.
  intros=> sum_true; pose p := fun x, mem s x /\ f x; change (exists x, p x);
    apply ex_for; delta p=> {p}; generalize sum_true; apply absurd=> /= h.
  (cut : s <= s by done); pose {1 3} s' := s;elim/fset_ind s'.
    by rewrite Mbor.sum_empty.
  intros=> x s' nmem IH leq_adds'_s.
  cut leq_s'_s : s' <= s by smt.
  rewrite Mbor.sum_add // -nor IH // /=; cut := h x; rewrite -nand.
  by case (mem s x)=> //=; cut := leq_adds'_s x; rewrite in_fsetU in_fset1 //= => ->.
qed.

pred cpOrs (X:(('a -> bool)) fset) (x:'a) = Mbor.sum (fun (P:('a -> bool)), P x) X.

lemma cpOrs0 : cpOrs (fset0<:('a -> bool)>) = pred0.
proof -strict.
  by apply fun_ext => y;rewrite /cpOrs Mbor.sum_empty.
qed.

lemma cpOrs_add s (p:('a -> bool)) : 
  cpOrs (s `|` fset1 p) = (predU p (cpOrs s)).
proof -strict.
  apply fun_ext => y.
  rewrite /cpOrs /predU /= !or_exists eq_iff;split=> /=.
    intros [x ];rewrite FSet.in_fsetU in_fset1 => [ [ ] H H0];first by right;exists x.
    by left;rewrite -H.
  intros [H | [x [H1 H2]]];first by exists p;rewrite FSet.in_fsetU in_fset1.
  by exists x; rewrite FSet.in_fsetU in_fset1;progress;left.
qed.

lemma mu_ors d (X:('a->bool) fset):
  disj_or X =>
  mu d (cpOrs X) = Mrplus.sum (fun P, mu d P) X.
proof strict.
  elim/fset_ind X.
    by intros disj;rewrite Mrplus.sum_empty cpOrs0 mu_false.
  intros f X f_nin_X IH disj; rewrite Mrplus.sum_add // cpOrs_add mu_disjoint.
    rewrite /predI /pred0=> x' /=;
      rewrite -not_def=> [f_x']; generalize f_nin_X disj .
    rewrite /cpOrs or_exists => Hnm Hd [p [Hp]] /=.
    by apply (Hd f p) => //; smt.
  rewrite IH => //.
  by intros x y H1 H2 H3;apply (disj x y) => //;smt.
qed.

require import Finite.
import Real.

lemma mean (d:'a distr) (p:'a -> bool):
  is_finite (support d) =>
  mu d p = 
    Mrplus.sum (fun x, (mu_x d x)*(charfun p x))
        (oflist (to_seq (support d))).
proof strict.
  intros=> fin_supp_d.
  pose sup := oflist (to_seq (support d)).
  pose is  := image (fun x y, p x /\ x = y) sup.
  rewrite mu_support (mu_eq d _ (cpOrs is)).
    intros y;rewrite /predI /is /cpOrs /= or_exists eq_iff;split.
      intros [H1 H2];exists ((fun x0 y0, p x0 /\ x0 = y0) y);split => //.
      by apply/imageP; exists y; rewrite /sup mem_oflist mem_to_seq.
    intros [p' []].
    by rewrite imageP; progress => //;smt. 
  rewrite mu_ors.
    rewrite /is => x1 x2 Hx; rewrite !imageP => [y1 [Hm1 Heq1]] [y2 [Hm2 Heq2]].
    subst; generalize Hx => /= Hx a [Hpa1 Heq1];rewrite -not_def => [Hpa2 Heq2].
    by subst; generalize Hx;rewrite not_def.
  rewrite /is => {is};elim/fset_ind sup.
    by rewrite image0 !Mrplus.sum_empty.
  intros x s Hnm Hrec;rewrite FSet.imageU FSet.image1 Mrplus.sum_add0.
    rewrite imageP /= => [x0 [H1 H2]].
    by rewrite (mu_eq d _ pred0) //;smt.
  rewrite Mrplus.sum_add // -Hrec /=; congr => //.
  rewrite /charfun /mu_x;case (p x) => //= Hp.
    by apply mu_eq; rewrite pred1E.
  by rewrite -(mu_false d);apply mu_eq.
qed.
