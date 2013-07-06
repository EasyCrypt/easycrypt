require import Int.
require import Fun.
require import List. import PermutationLists.

type 'a set.

(** We use a list of elements as core specification *)
op elems:'a set -> 'a list.
axiom unique_elems: forall (X:'a set),
  unique (elems X).

(** mem *)
op mem:'a -> 'a set -> bool.
axiom mem_def (x:'a) (X:'a set):
  mem x (elems X) <=> mem x X.

op cpMem(X:'a set): 'a cpred = lambda x, mem x X.

lemma count_mem (x:'a) (X:'a set):
  (count x (elems X) = 1) <=> mem x X
by [].

lemma count_nmem (x:'a) (X:'a set):
  (count x (elems X) = 0) <=> !mem x X
by [].

lemma count_set (x:'a) (X:'a set):
  (count x (elems X) = 1) \/ (count x (elems X) = 0)
by [].

(** Equality *)
pred (==) (X1 X2:'a set) = forall x, mem x X1 <=> mem x X2.

lemma perm_eq: forall (X Y:'a set),
  (elems X <-> elems Y) => X == Y.
proof strict.
by intros=> X Y X_Y; delta (==) beta=> x;
   rewrite -2!count_mem X_Y //.
qed.

(* Extension is an equivalence relation *)
lemma nosmt eq_refl: forall (X:'a set), X == X by [].
lemma nosmt eq_symm: forall (X Y:'a set), X == Y => Y == X by [].
lemma nosmt eq_tran: forall (X Y Z:'a set), X == Y => Y == Z => X == Z by [].

(* And we can use it as equality *)
axiom set_ext: forall (X1 X2:'a set), X1 == X2 => X1 = X2.

lemma elems_eq : forall (s t:'a set),
  elems s = elems t <=> s = t.
proof strict.
by intros=> s t; (split=> h;
     first apply set_ext=> x;rewrite - !mem_def);
   rewrite h //.
qed.

(** Inclusion *)
pred (<=) (X1 X2:'a set) = forall x, mem x X1 => mem x X2.

(* Inclusion is a partial order *)
lemma nosmt leq_refl: forall (X:'a set),
  X <= X
by trivial.

lemma nosmt leq_asym: forall (X Y:'a set),
  X <= Y => Y <= X => X = Y.
proof strict.
by intros=> X Y X_leq_Y Y_leq_X; apply set_ext=> x;
   split; [ apply X_leq_Y | apply Y_leq_X ].
qed.

lemma nosmt leq_tran: forall (X Y Z:'a set),
  X <= Y => Y <= Z => X <= Z.
proof strict.
by intros=> X Y Z X_leq_Y Y_leq_Z x x_in_X;
   apply Y_leq_Z=> //; apply X_leq_Y=> //.
qed.

pred (>=) (X1 X2:'a set) = X2 <= X1.
pred (<) (X1 X2:'a set) = X1 <= X2 /\ X1 <> X2.
pred (>) (X1 X2:'a set) = X2 < X1.

(** empty *)
op empty:'a set.
axiom mem_empty: forall (x:'a), !(mem x empty).

lemma elems_empty: elems<:'a> empty = [].
proof strict.
by rewrite nil_nmem=> x; rewrite -List.count_mem nnot;
   apply Logic.eq_sym; rewrite count_nmem; apply mem_empty.
qed.

lemma empty_elems_nil: forall (X:'a set),
  X = empty <=> elems X = [].
proof strict.
by intros=> X; (split=> h; first rewrite h; apply elems_empty);
   apply set_ext; delta (==) beta=> x; rewrite -mem_def h;
   split; apply absurd=> _; [ apply mem_nil | apply mem_empty ].
qed.

lemma empty_nmem: forall (X:'a set),
  (forall (x:'a), !(mem x X)) <=> X = empty.
proof strict.
intros=> X; split=> h.
  by apply set_ext; delta (==) beta=> x; split;
     apply absurd=> _; [apply h | apply mem_empty].
  by subst X=> x; apply mem_empty.
qed.

lemma empty_leq: forall (X:'a set), empty <= X.
proof strict.
by intros=> X; delta (<=) beta=> x;
   apply absurd=> _; apply mem_empty.
qed.

(** single *)
op single:'a -> 'a set.
axiom mem_single_eq: forall (x:'a),
  mem x (single x).
axiom mem_single_neq: forall (x x':'a),
  x <> x' => !mem x (single x').

lemma single_nempty: forall (x:'a),
  single x <> empty by [].

lemma mem_single: forall (x y:'a),
  mem x (single y) <=> (x = y).
proof strict.
intros=> x y; split;
  last intros=> ->; apply mem_single_eq.
case (x = y)=> x_y //; apply absurd=> _; apply mem_single_neq=> //.
qed.

(** pick *)
op pick:'a set -> 'a.
axiom pick_def: forall (X:'a set),
  pick X = hd (elems X).

lemma mem_pick: forall (X:'a set),
  X <> empty => mem (pick X) X.
proof strict.
intros=> X; rewrite pick_def;
elim/list_case_eq (elems X).
  by rewrite -empty_elems_nil //.
  by intros=> x l; rewrite -mem_def=> -> _;
     rewrite hd_cons mem_cons //.
qed.

lemma pick_single: forall (x:'a set),
  pick (single x) = x.
proof strict.
by intros=> x; rewrite -mem_single; apply mem_pick; apply single_nempty.
qed.

(** add *)
op add:'a -> 'a set -> 'a set.
axiom mem_add: forall (x y:'a) (X:'a set),
 (mem x (add y X)) = (mem x X \/ x = y).

lemma add_in_id: forall (x:'a) (X:'a set),
  mem x X => X = add x X
by (intros=> x X x_in_X; apply set_ext; smt).

lemma leq_add: forall (x:'a) X, X <= add x X by [].

lemma elems_add_in: forall (x:'a) (X:'a set),
  mem x X => elems (add x X) = elems X
by [].

lemma elems_add_nin: forall (x:'a) (X:'a set),
  !mem x X => elems (add x X) <-> x::(elems X)
by [].

(** rm *)
op rm:'a -> 'a set -> 'a set.
axiom mem_rm_eq: forall (x:'a) (X:'a set),
  !(mem x (rm x X)).
axiom mem_rm_neq: forall (x x':'a) (X:'a set),
  x <> x' => mem x (rm x' X) = mem x X.

lemma mem_rm: forall (x x':'a) (X:'a set),
  mem x (rm x' X) = (mem x X /\ x <> x').
intros x x' X; case (x = x')=> x_x'.
  by subst x'; logic; apply neqF; apply mem_rm_eq.
  by logic; apply mem_rm_neq.
save.

lemma mem_rm_left: forall (x x':'a) (X:'a set),
  mem x (rm x' X) => mem x X by [].

lemma mem_rm_right: forall (x x':'a) (X:'a set),
  mem x (rm x' X) => x <> x' by [].


lemma rm_nin_id: forall (x:'a) (X:'a set),
  !(mem x X) => X = rm x X
by (intros=> x X x_nin_X; apply set_ext; smt).

lemma rm_rmE : forall x y (xs:'a set), rm x (rm y xs) = rm y (rm x xs).
proof strict.
intros=> x y xs; apply set_ext=> x';
rewrite !mem_rm !andA (andC (x' <> y)) //.
save.

lemma elems_rm: forall (x:'a) (X:'a set),
  elems (rm x X) <-> rm x (elems X)
by [].

lemma rm_leq: forall (x:'a) (X:'a set), rm x X <= X by [].

lemma rm_add_eq: forall (x:'a) X,
  rm x (add x X) = rm x X.
proof strict.
intros=> x X; apply set_ext=> x';
rewrite 2!mem_rm mem_add orDand (rw_eq_sym x' x);
cut ->: (x = x' /\ !x = x') = false; first by case (x = x')=> h /= //.
by trivial.
qed.

lemma rm_add_neq: forall (x x':'a) X,
  x <> x' => rm x (add x' X) = add x' (rm x X).
proof strict.
intros=> x x' X x_x'; apply set_ext;
delta (==); beta=> x0;
case (x = x0)=> x_x0.
  by subst x0; smt.
  by rewrite mem_rm_neq; smt.
qed.

lemma add_rm_in: forall (x:'a) (X:'a set),
  mem x X => add x (rm x X) = X.
proof strict.
intros=> x X x_in_X; apply set_ext; apply perm_eq;
apply (perm_trans (x::(elems (rm x X)))); first apply elems_add_nin; apply mem_rm_eq.
apply (perm_trans (x::(rm x (elems X)))); first apply perm_cons; apply elems_rm.
smt.
qed.

lemma add_destruct: forall (x:'a) (X:'a set),
  (exists (X':'a set), !mem x X' /\ X = add x X') <=> mem x X
by [].

lemma rm_single: forall (x:'a),
  rm x (single x) = empty.
proof strict.
intros=> x; apply set_ext=> x'; case (x' = x)=> x_x'.
  by subst x'; split; apply absurd; intros=> _;[ apply mem_rm_eq | apply mem_empty ].
  by rewrite mem_rm_neq ?(rw_eq_sym x x') //; split;
     apply absurd; intros=> _; [ apply mem_single_neq | apply mem_empty ].
qed.

(** induction *)
axiom set_comp: forall (p:('a set) cpred),
  p empty =>
  (forall (s:'a set), s <> empty => p (rm (pick s) s) => p s) =>
  forall s, p s.

lemma set_ind: forall (p:('a set) cpred),
  p empty =>
  (forall x (s:'a set), !mem x s => p s => p (add x s)) =>
  forall s, p s.
proof strict.
intros=> p p0 IH s; apply set_comp=> // s' p_nempty p_pick;
rewrite -(add_rm_in (pick s')); first apply mem_pick=> //.
apply IH=> //; apply mem_rm_eq.
qed.

(** card *)
op card:'a set -> int.
axiom card_def: forall (X:'a set),
  card X = length (elems X).

lemma card_empty: card empty<:'a> = 0 by [].

lemma card_nempty: forall (X:'a set),
  X <> empty => 0 < card X.
proof strict.
intros=> X nempty; cut h: exists x, mem x X; smt.
qed.

lemma card_add_in: forall (x:'a) (X:'a set),
  mem x X => card (add x X) = card X
by [].

lemma card_add_nin: forall (x:'a) (X:'a set),
  !(mem x X) => card (add x X) = card X + 1.
proof strict.
intros=> x X x_nin_X;
rewrite 2!card_def (perm_length (elems (add x X)) (x::(elems X))).
  by apply elems_add_nin=> //.
  by rewrite length_cons; smt.
qed.

lemma card_rm_in: forall (x:'a) (X:'a set),
  mem x X => card (rm x X) = card X - 1
by [].

lemma card_rm_nin: forall (x:'a) (X:'a set),
  !(mem x X) => card (rm x X) = card X
by [].

lemma card_single: forall (x:'a),
  card (single x) = 1.
proof strict.
intros=> x; cut h: card (single x) - 1 = 0; last smt.
rewrite -(card_rm_in x) ?rm_single ?card_empty //; apply mem_single_eq.
qed.

(** union *)
op union:'a set -> 'a set -> 'a set.
axiom mem_union: forall x (X1 X2:'a set),
  mem x (union X1 X2) <=> (mem x X1 \/ mem x X2).

lemma unionC: forall (X1 X2:'a set),
  union X1 X2 = union X2 X1.
proof strict.
by intros=> X1 X2; apply set_ext=> x; rewrite 2!mem_union orC //.
qed.

lemma unionA: forall (X1 X2 X3:'a set),
  union (union X1 X2) X3 = union X1 (union X2 X3).
proof strict.
by intros=> X1 X2 X3; apply set_ext=> x; rewrite !mem_union orA //.
qed.

lemma union0s: forall (X:'a set),
  union empty X = X.
proof strict.
intros=> X; apply set_ext=> x; rewrite mem_union; split.
  by intros=> [empty | x_in_X] //; generalize empty; apply absurd=> _; apply mem_empty.
  by intros=> x_in_X; right.
qed.

lemma unionLs: forall (X1 X2:'a set),
  X1 <= union X1 X2.
proof strict.
by intros=> X1 X2 x x_in_X1; rewrite mem_union; left.
qed.

lemma unionK: forall (X:'a set),
  union X X = X.
proof strict.
by intros=> X; apply set_ext=> x; rewrite mem_union orK.
qed.

(** inter *)
op inter:'a set -> 'a set -> 'a set.
axiom mem_inter: forall x (X1 X2:'a set),
  mem x (inter X1 X2) <=> (mem x X1 /\ mem x X2).

lemma interC: forall (X1 X2:'a set),
  inter X1 X2 = inter X2 X1.
proof strict.
by intros=> X1 X2; apply set_ext=> x; rewrite !mem_inter andC.
qed.

lemma interA: forall (X1 X2 X3:'a set),
  inter (inter X1 X2) X3 = inter X1 (inter X2 X3).
proof strict.
by intros=> X1 X2 X3; apply set_ext=> x; rewrite !mem_inter andA.
qed.

lemma interGs: forall (X1 X2:'a set),
  inter X1 X2 <= X1.
proof strict.
by intros=> X1 X2 x; rewrite mem_inter=> [x_in_X1 _] //.
qed.

lemma interK: forall (X:'a set),
  inter X X = X.
proof strict.
by intros=> X; apply set_ext=> x; rewrite mem_inter=> //=.
qed.

lemma inter0s: forall (X:'a set),
  inter empty X = empty.
proof strict.
by intros=> X; apply set_ext=> x; rewrite mem_inter; split=> //;
    apply absurd=> _; apply mem_empty.
qed.

(** all *)
op all:'a cpred -> 'a set -> bool.
axiom all_def: forall (p:'a cpred) (X:'a set),
  all p X <=> (forall x, mem x X => p x).

(** any *)
op any:'a cpred -> 'a set -> bool.
axiom any_def: forall (p:'a cpred) (X:'a set),
  any p X <=> (exists x, mem x X /\ p x).

(** filter *)
op filter:'a cpred -> 'a set -> 'a set.
axiom mem_filter: forall x (p:'a cpred) (X:'a set),
  mem x (filter p X) <=> (mem x X /\ p x).

lemma filter_cpTrue: forall (X:'a set),
  filter cpTrue X = X.
proof strict.
by intros=> X; apply set_ext=> x; rewrite mem_filter //.
qed.

lemma filter_cpEq_in: forall (x:'a) (X:'a set),
  mem x X => filter ((=) x) X = single x.
proof strict.
intros=> x X x_in_X; apply set_ext=> x';
rewrite mem_filter; case (x = x').
  by intros=> <-; simplify; split=> _ //; apply mem_single_eq.
  by rewrite rw_eq_sym => x_x'; simplify; apply mem_single_neq.
qed.

lemma card_filter_cpEq: forall (x:'a) (X:'a set),
  mem x X => card (filter ((=) x) X) = 1.
proof strict.
by intros=> x X x_in_X; rewrite filter_cpEq_in ?card_single //.
qed.

lemma leq_filter: forall (p:'a cpred) (X:'a set),
  filter p X <= X.
proof strict.
by intros=> p X x; rewrite mem_filter=> [x_in_X _] //.
qed.

(* fold *)
op fold : ('a -> 'b -> 'b) -> 'b -> 'a set -> 'b.

axiom fold_empty: forall (f:'a -> 'b -> 'b) (e:'b),
  fold f e empty = e.

axiom fold_rm_pick: forall (f:'a -> 'b -> 'b) (e:'b) xs,
    fold f e xs = f (pick xs) (fold f e (rm (pick xs) xs)).

lemma fold_set_list:
  forall (f:'a -> 'b -> 'b) (e:'b) xs,
    (forall a b X, f a (f b X) = f b (f a X)) =>
      fold f e xs = List.fold_right f e (elems xs).
intros=> f e xs C; elim/set_comp xs;
  first by rewrite fold_empty elems_empty fold_right_nil.
intros s nempty Hind; elim/list_case_eq (elems s);
  first by apply absurd=> _;rewrite -elems_empty elems_eq.
intros=> x l' h.
cut xval : pick s = x;first rewrite pick_def h hd_cons //.
subst x.
rewrite h fold_rm_pick fold_right_cons Hind //.
congr => //.
apply fold_permC;first assumption.
rewrite (_:l' = rm (pick s) (elems s)).
rewrite h rm_cons //.
apply elems_rm.
save.

lemma foldC: forall (x:'a) (f:'a -> 'b -> 'b) (z:'b) (xs:'a set),
  (forall a b X, f a (f b X) = f b (f a X)) =>
    mem x xs =>
    fold f z xs = f x (fold f z (rm x xs)).
intros=> ? ? ? ? C M.
rewrite ! fold_set_list;first 2 assumption.
rewrite (foldC x f z (elems xs));first assumption.
rewrite mem_def //.
rewrite (fold_permC f z (elems (rm x xs)) (rm x (elems xs))) //.
apply elems_rm.
save.

(* map *)
op img : ('a -> 'b) -> 'a set -> 'b set.
axiom img_def: forall (y:'b) (f:'a -> 'b) (xs:'a set),
  mem y (img f xs) <=> exists x, f x = y /\ mem x xs.

lemma mem_img : forall (x:'a) (f:'a -> 'b) (xs:'a set),
  mem x xs => mem (f x) (img f xs)
by (intros=> ? ? ?;rewrite (img_def (f x))=> ?;exists x => //).  

lemma img_empty : forall (f:'a -> 'b),
  (img f empty) = empty.
intros ?.
rewrite -empty_nmem => y.
cut ? : !(exists x, (lambda x, f x = y /\ mem x empty) x);first apply (nexists (lambda x, f x = y /\ mem x empty) _)=> x;beta;apply nand;right;apply mem_empty.
generalize H.
apply absurd.
simplify.
elim (img_def y f empty).
intros ? ?;assumption.
save.

lemma img_rm : forall (f:'a -> 'b) (xs:'a set) (x:'a),
  img f (rm x xs) = (if (forall x', mem x' xs => f x = f x' => x = x') then rm (f x) (img f xs) else img f xs).
intros ? ? ?.
apply set_ext=> y.
rewrite img_def.

case (forall (x' : 'a), mem x' xs => f x = f x' => x = x')=> ?.

rewrite mem_rm.
rewrite img_def.

split.

intros=> [a];intros => [h1 h2];split;first exists a;split;[ |apply (mem_rm_left _ x)];trivial.
cut ? : !(x = a);[
rewrite rw_eq_sym;apply (mem_rm_right _ _ xs);assumption h2|
generalize H0;rewrite -h1 (rw_eq_sym (f a)); apply absurd;simplify;apply H;apply (mem_rm_left _ x);trivial].

intros=> [h h1];generalize h=>[a];intros => [h2 h3];exists a;split;trivial.
rewrite mem_rm;split;first trivial.
by cut ? : !(f a = f x);[rewrite h2|generalize H0;apply absurd;simplify=> ->];trivial.


rewrite img_def.

split.

by intros=> [a];intros=> [h1 h2];exists a;(split;last apply (mem_rm_left _ x));trivial.

intros=> [a];intros=> [h1 h2].

cut [b] : (exists (x' : 'a), !(mem x' xs => f x = f x' => x = x'));first (apply (ex_for (lambda x',
!(mem x' xs => f x = f x' => x = x')) _));apply H.
clear H.
rewrite (rw_imp (mem b xs)).
rewrite (rw_imp (f x = f b)).
rewrite -rw_nor.
rewrite -rw_nor.
simplify.
intros=> [? ?];generalize H0;intros=> [? ?].

case (a=x)=> ?.
  exists b.
  split.
    by rewrite -H0 -h1;congr;rewrite rw_eq_sym;apply H2.
    by (rewrite mem_rm_neq;first rewrite rw_eq_sym);trivial.
  exists a.
  split.
    apply h1.
    rewrite mem_rm_neq.    
      apply H2.
      apply h2.
save.

theory Interval.

op interval : int -> int -> int set.
axiom interval_neg : forall (x y:int), x > y => interval x y = empty.
axiom interval_pos : forall (x y:int), x <= y => interval x y = add y (interval x (y-1)).

lemma mem_interval : forall (x y a:int), (mem a (interval x y)) <=> (x <= a <= y).
  intros x y a.
  case (x <= y)=> h;last smt.
  rewrite (_ : y = (y-x+1)-1+x);first smt.
  elimT Int.Induction.induction (y-x+1);[smt| |smt].
  simplify.
  intros j hh hrec.
  rewrite interval_pos;first smt.
  rewrite (_:j - 1 + x - 1=j - 1 - 1 + x);first smt.
  rewrite mem_add hrec.
  smt.
save.

lemma card_interval_max : forall x y, card (interval x y) = max (y - x + 1) 0.
  intros x y.
  case (x <= y);last smt.
  intros h.
  rewrite (_:interval x y=interval x (x+(y-x+1)-1));first smt.
  rewrite (_:max (y - x + 1) 0 = y-x+1);first smt.
  apply (Int.Induction.induction (lambda i, card (interval x (x+i-1)) = i) _ _ (y-x+1) _);[smt| |smt].
  simplify.
  intros j hh hrec.
  rewrite (interval_pos x (x+j-1) _);smt.
save.

lemma dec_interval : forall (x y:int),
    x <= y =>
    (img (lambda (x : int), x-1) (rm x (interval x y)) =
    (rm y (interval x y))
    ).
  intros x y h.
  apply set_ext=> a.
  rewrite img_def.
  rewrite ! mem_rm ! mem_interval.
  split.
  intros=> /= [x0] [h1].
  subst.
  smt.
  intros=> hh.
  exists (a+1).
  simplify.
  rewrite ! mem_rm ! mem_interval.
  smt.
save.

end Interval.

require import Real.
require import Distr.


(* General result regarding cpMem *)
lemma mu_cpMem : 
forall (s : 'a set, d : 'a distr, bd : real),
(forall (x : 'a), mu_x d x = bd) =>
mu d (cpMem s) = (card s)%r * bd.
proof.
 intros s;elimT set_ind s.
 intros d bd Hmu_x.
 rewrite (mu_eq d _ Fun.cpFalse).
  simplify Fun.(==) cpMem cpFalse;smt.
 rewrite mu_false card_empty //; smt.
 clear s;intros x s Hnmem IH d bd Hmu_x.
 cut ->: (card (add x s))%r * bd = 
          bd + (card s)%r * bd. 
  rewrite card_add_nin //=;smt.
 rewrite (mu_eq d _ (Fun.cpOr ((=) x) (cpMem s))).
 simplify Fun.(==) cpMem cpOr;smt.
 rewrite mu_or.
 cut ->: (mu d (Fun.cpAnd ((=) x) (cpMem s)) =
          mu d (Fun.cpFalse)).
  apply mu_eq;simplify Fun.(==) cpMem cpFalse;smt.
 rewrite mu_false (IH d bd _);first assumption.
 cut ->: (mu d ((=) x) = mu_x d x).
  simplify mu_x=> //.
 rewrite Hmu_x;smt.
save.


(* Uniform distribution on a (finite) set *)
theory Duni.
  op duni: 'a set -> 'a distr.

  axiom supp_def: forall (x:'a) X, in_supp x (duni X) <=> mem x X.

  axiom mu_def: forall (X:'a set) P, 
    !X = empty => mu (duni X) P = (card (filter P X))%r / (card X)%r. 

  axiom mu_def_empty: forall (P:'a cpred), mu (duni empty) P = 0%r.

  axiom mu_x_def_in: forall (x:'a) (X:'a set), 
    mem x X => mu_x (duni X) x = 1%r / (card X)%r. 

  axiom mu_x_def_notin: forall (x:'a) (X:'a set), 
    !mem x X => mu_x (duni X) x = 0%r.

  lemma weight_def: forall (X:'a set), 
    weight (duni X) = if X = empty then 0%r else 1%r.
  proof.
    intros X; case (X = empty); intros H.
    smt. 
    delta weight; simplify. 
    rewrite (mu_def<:'a> X Fun.cpTrue _).
    assumption.
    rewrite (filter_cpTrue<:'a> X).
    cut W: ((card X)%r <> 0%r); smt.
  qed.
end Duni.

theory Dinter_uni.
  import Interval.
  op dinter i j = Duni.duni (interval i j).

  lemma supp_def: forall (i j x:int),
    in_supp x (dinter i j) <=> i <= x <= j
  by [].

  lemma mu_def_z: forall (i j:int) (p:int cpred),
    j < i =>
    mu (dinter i j) p = 0%r
  by [].

  lemma mu_def_nz: forall (i j:int) (p:int cpred),
    i <= j =>
    mu (dinter i j) p =
      (card (filter p (interval i j)))%r / (card (interval i j))%r
  by [].

  (* We would like to generalize things like this:
  axiom mu_def : forall (i j:int) (p:int cPred),
    mu (dinter i j) p = (sum i j p)%r / (j - i + 1)%r.
  *)

  lemma mu_x_def_in : forall (i j x:int),
    in_supp x (dinter i j) =>
    mu_x (dinter i j) x = 1%r / (j - i + 1)%r.
  proof strict.
  intros=> i j; case (i <= j).
    by intros=> i_leq_j x; rewrite supp_def=> [i_x x_j];
       delta mu_x beta; rewrite mu_def_nz //;
       rewrite card_filter_cpEq ?mem_interval // card_interval_max; delta max beta;
       rewrite (_: j - i + 1 < 0 = false) //=; first smt.
    by intros=> i_j x; apply absurd=> _; rewrite supp_def; smt.
  qed.

  lemma mu_x_def_nin: forall (i j x:int),
    !in_supp x (dinter i j) => mu_x (dinter i j) x = 0%r
  by [].

  lemma dinter_is_dinter: forall i j, dinter i j = Distr.Dinter.dinter i j.
  proof strict.
  intros=> i j; rewrite -mu_ext=> x; case (in_supp x (dinter i j))=> supp_x.
    rewrite mu_x_def_in // Distr.Dinter.mu_x_def_in; smt. (* cut in_supp dinter = in_supp dinter_uni *)
    rewrite mu_x_def_nin // Distr.Dinter.mu_x_def_notin; smt.
  qed.

  lemma weight_def : forall (i j:int), 
    weight (dinter i j) = if i <= j then 1%r else 0%r
  by [].
  
  lemma mu_in_supp : forall (i j : int),
    i <= j => 
    mu (dinter i j) (lambda x, i <= x <= j) = 1%r.
  proof.
    intros i j H.
    rewrite -(mu_in_supp_eq (dinter i j) Fun.cpTrue);smt.
  save.
end Dinter_uni.

(** Restriction of a distribution (sub-distribution) *)
theory Drestr.
  op drestr: 'a distr -> 'a set -> 'a distr.
 
  axiom supp_def: forall (x:'a) d X, 
    in_supp x (drestr d X) <=> in_supp x d /\ !mem x X.
  
  axiom mu_x_def_notin: forall (x:'a) d (X:'a set), 
    in_supp x d => !mem x X => mu_x (drestr d X) x = mu_x d x.

  lemma mu_x_def_in: forall (x:'a) d (X:'a set), 
    in_supp x d => mem x X => mu_x (drestr d X) x = 0%r by [].

  axiom weight_def: forall (d:'a distr) X, 
    weight (drestr d X) = weight d - mu d (cpMem X).
end Drestr.

(** Scaled restriction of a distribution *)
theory Dexcepted.
  op (\) (d:'a distr, X:'a set) : 'a distr = Dscale.dscale (Drestr.drestr d X).

  lemma supp_def : forall (x:'a) d X,
    (in_supp x (d \ X) => (in_supp x d /\ !mem x X)) /\
    ((in_supp x d /\ !mem x X) => in_supp x (d \ X)).
  proof.
  intros d X x;split.
    intros in_supp;split;smt.
    intros in_supp_nmem;smt.
  save.
    
  lemma mu_x_def : forall (x:'a) d X,
    mu_x (d \ X) x =
    (in_supp x (d \ X)) ? mu_x d x / (weight d - mu d (cpMem X)) : 0%r.
  proof.
    intros x d X; rewrite /(\).
    case (weight d - mu d (cpMem X) = 0%r)=> weight.
      by rewrite /mu_x Dscale.mu_x_def_0 ?Drestr.weight_def //
                 /in_supp
                 (_: (0%r < mu_x (Dscale.dscale (Drestr.drestr d X)) x) = false)=> //=;
         first smt.
      by smt.
  qed.

  lemma mu_weight_def : forall (d:'a distr) X,
    weight (d \ X) = (weight d = mu d (cpMem X)) ? 0%r : 1%r
  by [].
    
  lemma lossless_restr : forall (d : 'a distr) X,
    weight d = 1%r =>
    mu d (cpMem X) < 1%r =>
    Distr.weight (d \ X) = 1%r. 
  proof.
   intros s d Hll Hmu; simplify (\);
   (rewrite Distr.Dscale.weight_pos;last smt);
   rewrite Drestr.weight_def;smt.
  save.
end Dexcepted.
