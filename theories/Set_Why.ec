require import Int.
require Fun.
require Real.
require Distr.


theory Fset.

  import why3 "set" "Fset"
    op "cardinal" as "#";
    op "subset" as "<=".

  op cPmem (s:'a set) (x:'a) = mem x s.
 
end Fset.


(* Cannot use SetComprehension from Why3 for finite sets *)
theory MapFilter.
 
  import Fun.
  import Fset.

  (** { x | x in U and p(x) } *)
  op filter : 'a cPred -> 'a set -> 'a set.

  axiom filter_def (p:'a cPred) (s:'a set) (x:'a) : 
    mem x (filter p s) <=> p x /\ mem x s.

  lemma filter_true (s:'a set) : filter cPtrue s = s
  by (apply extensionality; smt).

  (** { f x | x in U } *)
  op map : ('a -> 'b) -> 'a set -> 'b set.

  axiom map_def (f:'a -> 'b) (s:'a set) (y:'b) :
    mem y (map f s) <=> exists x, mem x s /\ y = f x.

  lemma map_def_alt (f:'a -> 'b) (s:'a set) (x:'a) :
    mem x s => mem (f x) (map f s) by [].

end MapFilter.


(* Sets equipped with an nth operator for enumeration *)
theory FsetNth.

  import Fset.
  import why3 "set" "FsetNth".

  import Real.
  import Distr.

  lemma mu_choose_mem : forall (S:'a set, x:'a),
    mem x S =>
    1%r / (#S)%r <= mu [0..#S - 1] (lambda i, nth i S = x).
  proof.
   intros S x H.
    cut H1 : (exists i, 0 <= i /\ i < #S /\ x = nth i S); first smt.
    elim H1; clear H1; intros i Hi.
    apply (Real.Trans (1%r / (#S)%r) (Distr.mu_x [0..#S - 1] i)).
    rewrite (Distr.Dinter.mu_x_def_in 0 (#S - 1) i _); smt.
    delta Distr.mu_x; simplify.
    apply Distr.mu_sub; smt.   
   qed.

end FsetNth.


(* Could instead import monomorphic Why3 theory, which requires cloning *)
theory FsetInduction.

  import Fset.
 
  axiom induction (p:'a set -> bool) :
    (forall (s:'a set), is_empty s => p s) =>
    (forall (s:'a set), p s => forall (x:'a), !mem x s => p (add x s)) =>
    forall (s:'a set), p s.

end FsetInduction.


theory Min.

  import why3 "set" "Min".

end Min.


(* Uniform distribution on a (finite) set *)
theory Duni.

  import Real.
  import Distr.
  import Fset.
  import MapFilter.

  op duni : 'a set -> 'a distr.

  axiom supp_def : forall (x:'a) X, in_supp x (duni X) <=> mem x X.

  axiom mu_def : forall (X:'a set) P, 
    !is_empty X => mu (duni X) P = (#filter P X)%r / (#X)%r. 

  axiom mu_def_empty : forall (P:'a cPred), mu (duni empty) P = 0%r.
 
  axiom mu_x_def_in : forall (x:'a) X, 
    mem x X => mu_x (duni X) x = 1%r / (#X)%r. 

  axiom mu_x_def_notin : forall (x:'a) X, 
    !mem x X => mu_x (duni X) x = 0%r.

  lemma weight_def : forall (X:'a set), 
    weight (duni X) = if is_empty X then 0%r else 1%r.
  proof.
    intros X; case (is_empty X); intros H.
    cut P : (X = empty).
    apply extensionality; smt.
    smt.
    delta weight; simplify. 
    rewrite (mu_def<:'a> X Fun.cPtrue _).
    assumption.
    rewrite (filter_true<:'a> X).
    cut W : ((#X)%r <> 0%r); smt.
  qed.

end Duni.


(** Restriction of a distribution (sub-distribution) *)
theory Drestr.

  import Fset.
  import Real.
  import Distr.

  op drestr : 'a distr -> 'a set -> 'a distr.
 
  axiom supp_def : forall (x:'a) d X, 
    in_supp x (drestr d X) <=> in_supp x d /\ !mem x X.
  
  axiom mu_x_def_notin : forall (x:'a) d X, 
    in_supp x d => !mem x X => mu_x (drestr d X) x = mu_x d x.

  lemma mu_x_def_in : forall (x:'a) d X, 
    in_supp x d => mem x X => mu_x (drestr d X) x = 0%r by [].

  axiom weight_def : forall (d:'a distr) X, 
    weight (drestr d X) = weight d - mu d (cPmem X).

end Drestr.


(** Scaled restriction of a distribution *)
theory Dexcepted.

  import Fset.
  import Real.
  import Distr.

  op (\) (d:'a distr, X:'a set) : 'a distr = Dscale.dscale (Drestr.drestr d X).

  lemma supp_def : forall (x:'a) d X,
    (in_supp x (d \ X) => (in_supp x d /\ !mem x X)) /\
    ((in_supp x d /\ !mem x X) => in_supp x (d \ X)).
  proof.
    intros d X x; split; smt.
  save.
    
  lemma mu_x_def : forall (x:'a) d X,
    mu_x (d \ X) x = 
    (in_supp x (d \ X)) ? mu_x d x / (weight d - mu d (cPmem X)) : 0%r.
  proof.
    intros x d X; delta (\); last smt.
  qed.

  lemma weight_def : forall (d:'a distr) X,
    weight (d \ X) = (weight d = mu d (cPmem X)) ? 0%r : 1%r
  by [].

end Dexcepted.


theory SetMap.

  require import Map.

  type 'a set = ('a, bool) map.

  op mem (x:'a) (s:'a set) = s.[x] = Some true.

  pred (==) (s1 s2:'a set) = forall (x:'a), mem x s1 <=> mem x s2.

  (* No extensionality due to option *)

  pred (<=) (s1 s2:'a set) = forall (x:'a), mem x s1 => mem x s2.
 
  lemma subset_refl (s:'a set) : s <= s
  by [].

  lemma subset_trans (s1 s2 s3:'a set) : s1 <= s2 => s2 <= s3 => s1 <= s3
  by [].

  const empty : 'a set = empty.

  pred is_empty (s:'a set) = forall (x:'a), !mem x s.

  lemma empty_def1 : is_empty (empty<:'a>) 
  by []. 

  lemma mem_empty : forall (x:'a), mem x SetMap.empty <=> false 
  by [].

  op add (x:'a) (s:'a set) : 'a set = s.[x <- true].

  lemma add_def1 : forall (x y:'a) (s:'a set), 
    mem x (add y s) <=> x = y \/ mem x s
  by [].

  op singleton (x:'a) : 'a set = add x SetMap.empty.

  op remove (x:'a) (s:'a set) : 'a set = Map.rm x s.

  lemma remove_def1 (x y:'a) (s:'a set) :
    mem x (remove y s) <=> x <> y /\ mem x s
  by [].

  lemma subset_remove (x:'a) (s:'a set) : remove x s <= s
  by [].

  op union : 'a set -> 'a set -> 'a set.

  axiom union_def (s1 s2:'a set) (x:'a) :
    (union s1 s2).[x] = Some true <=> s1.[x] = Some true || s2.[x] = Some true.

  lemma union_def1 (s1 s2:'a set) (x:'a) :
    mem x (union s1 s2) <=> mem x s1 \/ mem x s2
  by [].

  op inter : 'a set -> 'a set -> 'a set.

  axiom inter_def (s1 s2:'a set) (x:'a) : 
    (inter s1 s2).[x] = Some true <=> s1.[x] = Some true && s2.[x] = Some true.

  lemma inter_def1 (s1 s2:'a set) (x:'a) :
    mem x (inter s1 s2) <=> mem x s1 /\ mem x s2
  by [].

  op diff : 'a set -> 'a set -> 'a set.

  axiom diff_def (s1 s2:'a set) (x:'a) : 
    (diff s1 s2).[x] = Some true <=> s1.[x] = Some true && s2.[x] <> Some true.

  lemma diff_def1 (s1 s2:'a set) (x:'a) :
    mem x (diff s1 s2) <=> mem x s1 /\ !mem x s2
  by [].

  lemma subset_diff (s1 s2:'a set) : diff s1 s2 <= s1
  by [].

  op choose (s:'a set) : 'a = proj (find (lambda p, let (a,b) = p in b) s).

  lemma choose_def (s:'a set) : !is_empty s => mem (choose s) s.
  proof.
   intros H.
   cut H1 : (exists x, in_dom x s /\ s.[x] = Some true); first smt.
   elim H1; intros x Hx; clear H H1.
   cut H2 : (exists x, find (lambda p, let (a,b) = p in b) s = Some x).   
   apply (find_some2 (lambda p, let (a,b) = p in b) s x _); smt.
   elim H2; intros y Hy; clear x Hx H2.
   cut H3 : (in_dom y s /\ proj s.[y]). 
   apply (find_some1 (lambda p, let (a,b) = p in b) s y _); assumption.
   delta; simplify; rewrite Hy; clear Hy.
   cut P : (exists x, s.[y] = Some x); smt.
  qed.

end SetMap.
