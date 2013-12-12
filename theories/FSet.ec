require import Int.
require import Fun.
require import List.
  import PermutationLists.

type 'a set.

(** We use a list of elements as core specification *)
op elems:'a set -> 'a list.
axiom unique_elems (X:'a set): unique (elems X).

(** mem *)
op mem:'a -> 'a set -> bool.
axiom mem_def (x:'a) (X:'a set):
  mem x (elems X) <=> mem x X.

op cpMem(X:'a set): ('a -> bool) = fun x, mem x X.

lemma nosmt count_mem (x:'a) (X:'a set):
  (count x (elems X) = 1) <=> mem x X
by [].

lemma nosmt count_nmem (x:'a) (X:'a set):
  (count x (elems X) = 0) <=> !mem x X
by [].

lemma nosmt count_set (x:'a) (X:'a set):
  (count x (elems X) = 1) \/ (count x (elems X) = 0)
by [].

(** Equality *)
pred (==) (X1 X2:'a set) = forall x, mem x X1 <=> mem x X2.

lemma perm_eq (X Y:'a set):
  (elems X <-> elems Y) => X == Y.
proof strict.
by intros=> X_Y; delta (==) beta=> x;
   rewrite -2!count_mem X_Y //.
qed.

(* Extension is an equivalence relation *)
lemma nosmt eq_refl (X:'a set): X == X by trivial.
lemma nosmt eq_symm (X Y:'a set): X == Y => Y == X by [].
lemma nosmt eq_tran (X Y Z:'a set): X == Y => Y == Z => X == Z by [].

(* And we can use it as equality *)
axiom set_ext (X1 X2:'a set): X1 == X2 => X1 = X2.

lemma elems_eq (s t:'a set):
  elems s = elems t <=> s = t.
proof strict.
split=> h; last by rewrite h.
by apply set_ext=> x;rewrite - !mem_def; rewrite h.
qed.

(** Inclusion *)
pred (<=) (X1 X2:'a set) = forall x, mem x X1 => mem x X2.

(* Inclusion is a partial order *)
lemma nosmt leq_refl (X:'a set): X <= X by trivial.

lemma nosmt leq_asym (X Y:'a set):
  X <= Y => Y <= X => X = Y.
proof strict.
by intros=> X_leq_Y Y_leq_X; apply set_ext=> x;
   split; [apply X_leq_Y | apply Y_leq_X].
qed.

lemma nosmt leq_tran (Y X Z:'a set):
  X <= Y => Y <= Z => X <= Z.
proof strict.
by intros=> X_leq_Y Y_leq_Z x x_in_X;
   apply Y_leq_Z=> //; apply X_leq_Y=> //.
qed.

pred (>=) (X1 X2:'a set) = X2 <= X1.
pred (<) (X1 X2:'a set) = X1 <= X2 /\ X1 <> X2.
pred (>) (X1 X2:'a set) = X2 < X1.

(** empty *)
op empty:'a set.
axiom mem_empty (x:'a): !(mem x empty).

lemma elems_empty: elems<:'a> empty = [].
proof strict.
by rewrite nil_nmem=> x; rewrite -List.count_mem nnot;
   apply Logic.eq_sym; rewrite count_nmem; apply mem_empty.
qed.

lemma empty_elems_nil (X:'a set):
  X = empty <=> elems X = [].
proof strict.
split=> h; first by rewrite h; apply elems_empty.
by apply set_ext; delta (==) beta=> x; rewrite -mem_def h;
   split; apply absurd=> _; [ apply mem_nil | apply mem_empty ].
qed.

lemma empty_nmem (X:'a set):
  (forall (x:'a), !(mem x X)) <=> X = empty.
proof strict.
split=> h; last by subst X=> x; apply mem_empty.
by apply set_ext; delta (==) beta=> x; split;
   apply absurd=> _; [apply h | apply mem_empty].
qed.

lemma empty_leq (X:'a set): empty <= X.
proof strict.
by simplify (<=)=> x; apply absurd=> _;
   apply mem_empty.
qed.

(** single *)
op single:'a -> 'a set.
axiom mem_single_eq (x:'a): mem x (single x).
axiom mem_single_neq (x x':'a):
  x <> x' => !mem x (single x').

lemma nosmt single_nempty (x:'a):
  single x <> empty by [].

lemma mem_single (x y:'a):
  mem x (single y) <=> (x = y).
proof strict.
split; last by intros=> ->; apply mem_single_eq.
by case (x = y)=> x_y //;
   apply absurd=> _; apply mem_single_neq=> //.
qed.

(** pick *)
op pick:'a set -> 'a.
axiom pick_def (X:'a set):
  pick X = hd (elems X).

lemma mem_pick (X:'a set):
  X <> empty => mem (pick X) X.
proof strict.
rewrite pick_def;
elim/list_case_eq (elems X).
  by rewrite -empty_elems_nil //.
  by intros=> x l; rewrite -mem_def=> -> _;
     rewrite hd_cons mem_cons //.
qed.

lemma pick_single (x:'a):
  pick (single x) = x.
proof strict.
by rewrite -mem_single mem_pick // single_nempty.
qed.

(** add *)
op add:'a -> 'a set -> 'a set.
axiom mem_add (x y:'a) (X:'a set):
 (mem x (add y X)) = (mem x X \/ x = y).

lemma add_in_id (x:'a) (X:'a set):
  mem x X => X = add x X.
proof strict.
by intros=> x_in_X; apply set_ext=> x';
   rewrite mem_add; split=> x_X; [left | elim x_X].
qed.

lemma nosmt leq_add (x:'a) X: X <= add x X by [].

lemma nosmt elems_add_in (x:'a) (X:'a set):
  mem x X => elems (add x X) = elems X
by [].

lemma elems_add_nin (x:'a) (X:'a set):
  !mem x X => elems (add x X) <-> x::(elems X).
proof strict.
rewrite -count_nmem=> x_nin_X x'; rewrite count_cons; case (x = x')=> /=.
  by intros=> <-; rewrite x_nin_X /= count_mem mem_add; right.
  intros=> x_neq_x'; elim (count_set x' X).
    by intros=> x'_in_X; rewrite x'_in_X; generalize x'_in_X; rewrite 2!count_mem mem_add=> x'_in_X; left.
    by intros=> x'_nin_X; rewrite x'_nin_X; generalize x'_nin_X; rewrite 2!count_nmem mem_add=> x'_in_X; smt.
qed.

lemma add_add_comm (a b:'a) s:
  add a (add b s) = add b (add a s).
proof -strict.
  apply set_ext => x.
  by rewrite !mem_add !orA (orC (x = b)).
qed.

(** disjoint *)
op disjoint : 'a set -> 'a set -> bool.
axiom disjoint_spec (s1 s2:'a set) : 
   disjoint s1 s2 <=> forall x, !(mem x s1 /\ mem x s2).

(** rm *)
op rm:'a -> 'a set -> 'a set.
axiom mem_rm_eq (x:'a) (X:'a set):
  !(mem x (rm x X)).
axiom mem_rm_neq (x x':'a) (X:'a set):
  x <> x' => mem x (rm x' X) = mem x X.

lemma mem_rm (x x':'a) (X:'a set):
  mem x (rm x' X) = (mem x X /\ x <> x').
proof strict.
case (x = x')=> x_x'.
  by subst x'=> /=; apply neqF; apply mem_rm_eq.
  by intros=> /=; apply mem_rm_neq.
qed.

lemma nosmt mem_rm_left (x x':'a) (X:'a set):
  mem x (rm x' X) => mem x X by [].

lemma nosmt mem_rm_right (x x':'a) (X:'a set):
  mem x (rm x' X) => x <> x' by [].


lemma rm_nin_id (x:'a) (X:'a set):
  !(mem x X) => X = rm x X.
proof strict.
intros=> x_nin_X; apply set_ext=> x'; rewrite mem_rm; split=> //.
by intros=> x'_in_X; split=> //; generalize x'_in_X; apply absurd.
qed.

lemma rm_rmE x y (xs:'a set): rm x (rm y xs) = rm y (rm x xs).
proof strict.
by apply set_ext=> x'; rewrite !mem_rm !andA (andC (x' <> y)) //.
qed.

lemma elems_rm (x:'a) (X:'a set):
  elems (rm x X) <-> rm x (elems X).
proof strict.
intros=> x'; elim (count_set x' (rm x X))=> x'_rmX.
  by rewrite x'_rmX; generalize x'_rmX; rewrite count_mem mem_rm=> [x'_in_X x'_neq_x];
     apply eq_sym; rewrite count_rm_neq ?count_mem //; smt.
  rewrite x'_rmX; generalize x'_rmX; rewrite count_nmem mem_rm -rw_nand /=; intros=> [x'_nin_X | x_eq_x'].
    apply eq_sym; case (x = x').
      by intros=> ->; rewrite count_rm_nin ?mem_def // count_nmem.
      by intros=> x_neq_x'; rewrite count_rm_neq // count_nmem.
    subst x'; apply eq_sym; case (mem x X)=> x_X.
      by rewrite count_rm_in ?mem_def //; cut ->: (count x (elems X)) = 1 by (by rewrite count_mem)=> //=.
      by rewrite count_rm_nin ?mem_def //; rewrite count_nmem.
qed.

lemma nosmt rm_leq (x:'a) (X:'a set): rm x X <= X by [].

lemma rm_add_eq (x:'a) X:
  rm x (add x X) = rm x X.
proof strict.
by apply set_ext=> x'; rewrite 2!mem_rm mem_add orDand (rw_eq_sym x' x);
   cut ->: (x = x' /\ !x = x') = false by (by case (x = x')=> h).
qed.

lemma rm_add_neq (x x':'a) X:
  x <> x' => rm x (add x' X) = add x' (rm x X).
proof strict.
intros=> x_x'; apply set_ext; simplify (==)=> x0;
case (x = x0)=> x_x0.
  by subst x0; smt.
  by rewrite mem_rm_neq; smt.
qed.

lemma add_rm_in (x:'a) (X:'a set):
  mem x X => add x (rm x X) = X.
proof strict.
intros=> x_in_X; apply set_ext; apply perm_eq;
apply (perm_trans (x::(elems (rm x X)))); first apply elems_add_nin; apply mem_rm_eq.
apply (perm_trans (x::(rm x (elems X)))); first apply perm_cons; apply elems_rm.
smt.
qed.

lemma nosmt add_destruct (x:'a) (X:'a set):
  (exists (X':'a set), !mem x X' /\ X = add x X') <=> mem x X
by [].

lemma rm_single (x:'a):
  rm x (single x) = empty.
proof strict.
apply set_ext=> x'; case (x' = x)=> x_x'.
  by subst x'; split; apply absurd; intros=> _;[ apply mem_rm_eq | apply mem_empty ].
  by rewrite mem_rm_neq ?(rw_eq_sym x x') //; split;
     apply absurd; intros=> _; [ apply mem_single_neq | apply mem_empty ].
qed.

(** induction *)
axiom set_comp (p:'a set-> bool):
  p empty =>
  (forall (s:'a set), s <> empty => p (rm (pick s) s) => p s) =>
  forall s, p s.

lemma set_ind (p:'a set -> bool):
  p empty =>
  (forall x (s:'a set), !mem x s => p s => p (add x s)) =>
  forall s, p s.
proof strict.
intros=> p0 IH s; apply set_comp=> // s' p_nempty p_pick;
rewrite -(add_rm_in (pick s')); first apply mem_pick=> //.
apply IH=> //; apply mem_rm_eq.
qed.

(** card *)
op card:'a set -> int.
axiom card_def (X:'a set):
  card X = length (elems X).

lemma nosmt card_empty: card empty<:'a> = 0 by [].

lemma card_nempty (X:'a set):
  X <> empty => 0 < card X.
proof strict.
intros=> nempty; cut h: exists x, mem x X; smt.
qed.

lemma nosmt card_add_in (x:'a) (X:'a set):
  mem x X => card (add x X) = card X
by [].

lemma card_add_nin (x:'a) (X:'a set):
  !(mem x X) => card (add x X) = card X + 1.
proof strict.
intros=> x_nin_X;
rewrite 2!card_def (perm_length (elems (add x X)) (x::(elems X))).
  by apply elems_add_nin=> //.
  by rewrite length_cons; smt.
qed.

lemma nosmt card_rm_in (x:'a) (X:'a set):
  mem x X => card (rm x X) = card X - 1
by [].

lemma nosmt card_rm_nin (x:'a) (X:'a set):
  !(mem x X) => card (rm x X) = card X
by [].

lemma card_single (x:'a):
  card (single x) = 1.
proof strict.
cut h: card (single x) - 1 = 0; last smt.
by rewrite -(card_rm_in x) ?rm_single ?card_empty //; apply mem_single_eq.
qed.

(** of_list *)
op of_list (l:'a list) = List.fold_right add empty l.

lemma of_list_nil : of_list [] = empty <:'a>.
proof -strict.
  by rewrite /of_list List.fold_right_nil.
qed.

lemma of_list_cons (a:'a) l : of_list (a::l) = add a (of_list l).
   by rewrite /of_list List.fold_right_cons.
qed.

lemma mem_of_list (x:'a) l : List.mem x l = mem x (of_list l).
proof -strict.
 rewrite /of_list;elimT list_ind l. 
   rewrite fold_right_nil;smt.
 intros {l} y xs;rewrite fold_right_cons;smt.
qed.

lemma card_of_list (l:'a list) :
   card (of_list l) <= List.length l.
proof -strict.
  rewrite /of_list;elimT list_ind l.
   by rewrite fold_right_nil card_empty length_nil => //.
  intros => {l} x xs H; rewrite fold_right_cons length_cons.  
  case (mem x (fold_right add empty xs))=> Hin; 
     [rewrite card_add_in // | rewrite card_add_nin //];smt.
qed.

(** union *)
op union:'a set -> 'a set -> 'a set.
axiom mem_union x (X1 X2:'a set):
  mem x (union X1 X2) <=> (mem x X1 \/ mem x X2).

lemma unionC (X1 X2:'a set):
  union X1 X2 = union X2 X1.
proof strict.
by apply set_ext=> x; rewrite 2!mem_union orC //.
qed.

lemma unionA (X1 X2 X3:'a set):
  union (union X1 X2) X3 = union X1 (union X2 X3).
proof strict.
by apply set_ext=> x; rewrite !mem_union orA //.
qed.

lemma union0s (X:'a set): union empty X = X.
proof strict.
apply set_ext=> x; rewrite mem_union; split.
  by intros=> [empty | x_in_X] //; generalize empty; apply absurd=> _; apply mem_empty.
  by intros=> x_in_X; right.
qed.

lemma unionLs (X1 X2:'a set): X1 <= union X1 X2.
proof strict.
by intros=> x x_in_X1; rewrite mem_union; left.
qed.

lemma unionK (X:'a set): union X X = X.
proof strict.
by apply set_ext=> x; rewrite mem_union orK.
qed.

lemma union_add (x:'a) s1 s2: union (add x s1) s2 = add x (union s1 s2).
proof -strict. 
  apply set_ext => y;rewrite mem_add mem_union mem_add mem_union;smt.
qed.

(** inter *)
op inter:'a set -> 'a set -> 'a set.
axiom mem_inter x (X1 X2:'a set):
  mem x (inter X1 X2) <=> (mem x X1 /\ mem x X2).

lemma interC (X1 X2:'a set):
  inter X1 X2 = inter X2 X1.
proof strict.
by apply set_ext=> x; rewrite !mem_inter andC.
qed.

lemma interA (X1 X2 X3:'a set):
  inter (inter X1 X2) X3 = inter X1 (inter X2 X3).
proof strict.
by apply set_ext=> x; rewrite !mem_inter andA.
qed.

lemma interGs (X1 X2:'a set): inter X1 X2 <= X1.
proof strict.
by intros=> x; rewrite mem_inter=> [x_in_X1 _] //.
qed.

lemma interK (X:'a set): inter X X = X.
proof strict.
by apply set_ext=> x; rewrite mem_inter.
qed.

lemma inter0s (X:'a set): inter empty X = empty.
proof strict.
by apply set_ext=> x; rewrite mem_inter; split=> //;
    apply absurd=> _; apply mem_empty.
qed.

(** all *)
op all:('a -> bool) -> 'a set -> bool.
axiom all_def (p:('a -> bool)) (X:'a set):
  all p X <=> (forall x, mem x X => p x).

(** any *)
op any:('a -> bool) -> 'a set -> bool.
axiom any_def (p:('a -> bool)) (X:'a set):
  any p X <=> (exists x, mem x X /\ p x).

(** filter *)
op filter:('a -> bool) -> 'a set -> 'a set.
axiom mem_filter x (p:('a -> bool)) (X:'a set):
  mem x (filter p X) <=> (mem x X /\ p x).

lemma filter_cpTrue (X:'a set):
  filter cpTrue X = X.
proof strict.
by apply set_ext=> x; rewrite mem_filter.
qed.

lemma filter_cpEq_in (x:'a) (X:'a set):
  mem x X => filter ((=) x) X = single x.
proof strict.
intros=> x_in_X; apply set_ext=> x';
rewrite mem_filter; case (x = x').
  by intros=> <-; simplify; split=> _ //; apply mem_single_eq.
  by rewrite rw_eq_sym => x_x'; simplify; apply mem_single_neq.
qed.

lemma card_filter_cpEq (x:'a) (X:'a set):
  mem x X => card (filter ((=) x) X) = 1.
proof strict.
by intros=> x_in_X; rewrite filter_cpEq_in ?card_single.
qed.

lemma leq_filter (p:('a -> bool)) (X:'a set):
  filter p X <= X.
proof strict.
by intros=> x; rewrite mem_filter=> [x_in_X _].
qed.

lemma filter_empty (p:'a -> bool):
  filter p empty = empty.
proof strict.
by apply set_ext=> x;
   rewrite mem_filter -(nnot (mem x empty)) mem_empty.
qed.

lemma rm_filter x (p:'a -> bool) (s:'a set):
  rm x (filter p s) = filter p (rm x s).
proof strict.
by apply set_ext=> a;
   rewrite mem_filter mem_rm mem_filter mem_rm.
qed.

(* fold *)
op fold : ('a -> 'b -> 'b) -> 'b -> 'a set -> 'b.

axiom fold_empty (f:'a -> 'b -> 'b) (e:'b):
  fold f e empty = e.

axiom fold_rm_pick (f:'a -> 'b -> 'b) (e:'b) xs:
  xs <> empty =>
  fold f e xs = f (pick xs) (fold f e (rm (pick xs) xs)).

lemma fold_set_list (f:'a -> 'b -> 'b) (e:'b) xs:
  (forall a b X, f a (f b X) = f b (f a X)) =>
    fold f e xs = List.fold_right f e (elems xs).
proof strict.
intros=> C; elim/set_comp xs;
  first by rewrite fold_empty elems_empty fold_right_nil.
intros s nempty Hind; elim/list_case_eq (elems s);
  first by apply absurd=> _;rewrite -elems_empty elems_eq.
intros=> x l' h.
cut xval : pick s = x;first rewrite pick_def h hd_cons //.
subst x.
rewrite h fold_rm_pick // fold_right_cons Hind //.
congr => //.
apply fold_permC; first assumption.
rewrite (_:l' = rm (pick s) (elems s)).
rewrite h rm_cons //.
apply elems_rm.
qed.

lemma foldC (x:'a) (f:'a -> 'b -> 'b) (z:'b) (xs:'a set):
  (forall a b X, f a (f b X) = f b (f a X)) =>
    mem x xs =>
    fold f z xs = f x (fold f z (rm x xs)).
intros=> C M.
rewrite !fold_set_list; first 2 assumption.
rewrite (foldC x f z (elems xs)); first assumption.
rewrite mem_def //.
rewrite (fold_permC f z (elems (rm x xs)) (rm x (elems xs))) //.
apply elems_rm.
qed.

(* map *)
op img : ('a -> 'b) -> 'a set -> 'b set.
axiom img_def (y:'b) (f:'a -> 'b) (xs:'a set):
  mem y (img f xs) <=> exists x, f x = y /\ mem x xs.

lemma mem_img (x:'a) (f:'a -> 'b) (xs:'a set):
  mem x xs => mem (f x) (img f xs).
proof strict.
by rewrite (img_def (f x))=> ?;exists x.
qed.

lemma img_empty (f:'a -> 'b): (img f empty) = empty.
proof strict.
rewrite -empty_nmem => y.
cut ? : !(exists x, (fun x, f x = y /\ mem x empty) x);first apply (nexists (fun x, f x = y /\ mem x empty) _)=> x;beta;apply nand;right;apply mem_empty.
generalize H.
apply absurd.
simplify.
elim (img_def y f empty).
intros ? ?;assumption.
qed.

lemma img_add (x:'a) s (f:'a -> 'b): 
   img f (add x s) = add (f x) (img f s).
proof -strict.
  apply set_ext => z.
  rewrite !img_def mem_add.
  split; [intros [w ] | intros [H | H]].
    rewrite mem_add => [<- [H | H]].
      by left;apply mem_img.
    by subst.
    generalize H;rewrite img_def => [x' [H1 H2]];exists x'.
    by rewrite mem_add;smt.
  by exists x;subst => /=;smt.
qed.


lemma img_rm (f:'a -> 'b) (xs:'a set) (x:'a):
  img f (rm x xs) = (if (forall x', mem x' xs => f x = f x' => x = x') then rm (f x) (img f xs) else img f xs).
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

cut [b] : (exists (x' : 'a), !(mem x' xs => f x = f x' => x = x'));first (apply (ex_for (fun x',
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
qed.

theory Interval.

op interval : int -> int -> int set.
axiom interval_neg (x y:int): x > y => interval x y = empty.
axiom interval_pos (x y:int): x <= y => interval x y = add y (interval x (y-1)).

lemma mem_interval (x y a:int): (mem a (interval x y)) <=> (x <= a <= y).
proof strict.
  case (x <= y)=> x_le_y;last smt.
  cut ->: y = (y - x + 1) - 1 + x;first smt.
  elim/Int.Induction.induction (y - x + 1);[smt| |smt].
  intros j j_pos IH.
  rewrite interval_pos;first smt.
  rewrite mem_add.
  rewrite (_:j + 1 - 1 + x - 1 = j - 1 + x);first smt.
  rewrite IH.
  smt.
qed.

lemma interval_single (i:int) :
   interval i i = add i empty.
proof -strict.
  rewrite interval_pos // interval_neg //; smt.
qed.

lemma interval_addl (i j : int) : 
    i <= j =>
    interval i j = add i (interval (i+1) j).  
proof -strict.
 intros Hle;cut -> : j = (j - i) + i;first smt.
 elim /Int.Induction.induction (j-i) => /=;last smt.
   by rewrite interval_single interval_neg //;first smt.
 clear j Hle => j Hle Heq.
 rewrite (interval_pos i (j + 1 + i));first smt.
 rewrite (interval_pos (i+1));first smt.
 cut -> : j+1+i-1 = j+i;first smt.
 by rewrite Heq;apply add_add_comm.
qed.

lemma card_interval_max x y: card (interval x y) = max (y - x + 1) 0.
proof strict.
  case (x <= y);last smt.
  intros h.
  rewrite (_:interval x y=interval x (x+(y-x+1)-1));first smt.
  rewrite (_:max (y - x + 1) 0 = y-x+1);first smt.
  elim/Int.Induction.induction (y-x+1);[smt| |smt].
  intros j hh hrec.
  rewrite (interval_pos x (x+(j+1)-1) _);smt.
qed.

lemma dec_interval (x y:int):
    x <= y =>
    (img (fun (x : int), x-1) (rm x (interval x y)) =
    (rm y (interval x y))
    ).
proof strict.
  intros=> x_leq_y.
  apply set_ext=> a.
  rewrite img_def.
  rewrite ! mem_rm ! mem_interval.
  split.
  intros=> /= [x0] [h1].
  subst.
  smt.
  intros=> hh /=.
  exists (a+1).
  rewrite ! mem_rm ! mem_interval.
  smt.
qed.

end Interval.

require import Real.
require import Distr.

lemma mu_cpMem_le (s:'a set): forall (d:'a distr) (bd:real),
  (forall (x : 'a), mem x s => mu_x d x <= bd) =>
    mu d (cpMem s) <= (card s)%r * bd.
proof strict.
  elimT set_ind s.
    intros d bd Hmu_x.
    rewrite (mu_eq d _ Fun.cpFalse).
      by intros x;rewrite /cpMem /cpFalse /= rw_neqF;apply mem_empty.
    by rewrite mu_false card_empty //.
  intros {s} x s Hnmem IH d bd Hmu_x.
  rewrite (_: (card (add x s))%r * bd = 
          bd + (card s)%r * bd); first by rewrite card_add_nin //=;ringeq.
  rewrite (mu_eq d _ (Fun.cpOr ((=) x) (cpMem s))).
    by intros z;rewrite /cpMem /cpOr mem_add orC (rw_eq_sym z).
  rewrite mu_disjoint.
   by rewrite /cpAnd /cpOr /cpFalse /cpMem => z /=;smt.
  (cut ->: (mu d ((=) x) = mu_x d x)) => //.
  apply addleM.
    by apply Hmu_x; first rewrite mem_add.   
  by apply (IH _ bd) => //;intros z Hz;apply Hmu_x;rewrite mem_add;left.
qed.

lemma mu_cpMem_ge (s:'a set): forall (d:'a distr) (bd:real),
  (forall (x : 'a), mem x s => mu_x d x >= bd) =>
    mu d (cpMem s) >= (card s)%r * bd.
proof strict.
  elimT set_ind s.
    intros d bd Hmu_x.
    rewrite (mu_eq d _ Fun.cpFalse).
      by intros x;rewrite /cpMem /cpFalse /= rw_neqF;apply mem_empty.
    by rewrite -le_ge mu_false card_empty //.
  intros {s} x s Hnmem IH d bd Hmu_x.
  rewrite (_: (card (add x s))%r * bd = 
          bd + (card s)%r * bd); first by rewrite card_add_nin //=;ringeq.
  rewrite (mu_eq d _ (Fun.cpOr ((=) x) (cpMem s))).
    by intros z;rewrite /cpMem /cpOr mem_add orC (rw_eq_sym z).
  rewrite mu_disjoint.
   by rewrite /cpAnd /cpOr /cpFalse /cpMem => z /=;smt.
  (cut ->: (mu d ((=) x) = mu_x d x)) => //.
  apply addgeM.
    by apply Hmu_x; first rewrite mem_add.   
  by apply (IH _ bd) => //;intros z Hz;apply Hmu_x;rewrite mem_add;left.
qed.

lemma mu_cpMem (s:'a set): forall (d:'a distr) (bd:real),
  (forall (x : 'a), mem x s => mu_x d x = bd) =>
    mu d (cpMem s) = (card s)%r * bd.
proof strict.
  intros d bd Hmu; rewrite eq_le_ge;split.
    by apply mu_cpMem_le => x H;rewrite Hmu.
  by apply mu_cpMem_ge => x H;rewrite Hmu // -le_ge.
qed.

lemma mu_Lmem_card (l:'a list) (d:'a distr) (bd:real):
  (forall (x : 'a), List.mem x l => mu_x d x = bd) =>
  mu d (fun x, List.mem x l) = (card (of_list l))%r * bd. 
proof -strict.  
  intros Hmu; rewrite (mu_eq _ _ (cpMem (of_list l))). 
    by intros x;rewrite /cpMem => /=; apply mem_of_list.
  apply mu_cpMem => x. rewrite -mem_of_list;apply Hmu.
qed.

lemma mu_Lmem_le_card (l:'a list) (d:'a distr) (bd:real):
  (forall (x : 'a), List.mem x l => mu_x d x <= bd) =>
  mu d (fun x, List.mem x l) <= (card (of_list l))%r * bd. 
proof -strict.  
  intros Hmu; rewrite (mu_eq _ _ (cpMem (of_list l))). 
    by intros x;rewrite /cpMem => /=; apply mem_of_list.
  apply mu_cpMem_le => x. rewrite -mem_of_list;apply Hmu.
qed.

lemma mu_Lmem_le_length (l:'a list) (d:'a distr) (bd:real):
  (forall (x : 'a), List.mem x l => mu_x d x <= bd) =>
  mu d (fun x, List.mem x l) <= (length l)%r * bd. 
proof -strict.
  elimT list_case l.
    intros _; rewrite length_nil (mu_eq _ _ (cpFalse)).
      by intros x; rewrite /cpFalse /= rw_neqF;apply mem_nil.
    by rewrite mu_false.
  intros x l0 Hmu.
  cut Hbd : 0%r <= bd.
    by cut H := Hmu x _; [ by rewrite mem_cons | smt].
  generalize (x :: l0) Hmu => {l x l0} l Hmu. 
  apply (Real.Trans _ ((card (of_list l))%r * bd)).
    by apply mu_Lmem_le_card.
  cut H := card_of_list l; smt.
qed.

(* Uniform distribution on a (finite) set *)
theory Duni.
  op duni: 'a set -> 'a distr.

  axiom supp_def (x:'a) X: in_supp x (duni X) <=> mem x X.

  axiom mu_def (X:'a set) P:
    !X = empty => mu (duni X) P = (card (filter P X))%r / (card X)%r. 

  axiom mu_def_empty (P:('a -> bool)): mu (duni empty) P = 0%r.

  axiom mu_x_def_in (x:'a) (X:'a set):
    mem x X => mu_x (duni X) x = 1%r / (card X)%r. 

  axiom mu_x_def_notin (x:'a) (X:'a set):
    !mem x X => mu_x (duni X) x = 0%r.

  lemma weight_def (X:'a set):
    weight (duni X) = if X = empty then 0%r else 1%r.
  proof strict.
  case (X = empty)=> H.
    smt.
    simplify weight; rewrite mu_def // (filter_cpTrue<:'a> X).
    cut W: ((card X)%r <> 0%r); smt.
  qed.
end Duni.

theory Dinter_uni.
  import Interval.
  op dinter i j = Duni.duni (interval i j).

  lemma nosmt supp_def (i j x:int):
    in_supp x (dinter i j) <=> i <= x <= j
  by [].

  lemma nosmt mu_def_z (i j:int) (p:(int -> bool)):
    j < i =>
    mu (dinter i j) p = 0%r
  by [].

  lemma nosmt mu_def_nz (i j:int) (p:(int -> bool)):
    i <= j =>
    mu (dinter i j) p =
      (card (filter p (interval i j)))%r / (card (interval i j))%r.
  proof strict.
  by intros=> i_leq_j; rewrite /dinter Duni.mu_def; smt.
  qed.

  lemma mu_x_def_in (i j x:int):
    in_supp x (dinter i j) =>
    mu_x (dinter i j) x = 1%r / (j - i + 1)%r.
  proof strict.
  case (i <= j).
    by intros=> i_leq_j; rewrite supp_def=> [i_x x_j];
       delta mu_x beta; rewrite mu_def_nz //;
       rewrite card_filter_cpEq ?mem_interval // card_interval_max; delta max beta;
       rewrite (_: j - i + 1 < 0 = false) //=; first smt.
    by intros=> i_j; apply absurd=> _; rewrite supp_def; smt.
  qed.

  lemma nosmt mu_x_def_nin (i j x:int):
    !in_supp x (dinter i j) => mu_x (dinter i j) x = 0%r
  by [].

  lemma dinter_is_dinter i j: dinter i j = Distr.Dinter.dinter i j.
  proof strict.
  apply pw_eq=> x; case (in_supp x (dinter i j))=> supp_x.
    rewrite mu_x_def_in // Distr.Dinter.mu_x_def_in; smt. (* cut in_supp dinter = in_supp dinter_uni *)
    rewrite mu_x_def_nin // Distr.Dinter.mu_x_def_notin; smt.
  qed.

  lemma nosmt weight_def (i j:int):
    weight (dinter i j) = if i <= j then 1%r else 0%r
  by [].
  
  lemma mu_in_supp (i j : int):
    i <= j => 
    mu (dinter i j) (fun x, i <= x <= j) = 1%r.
  proof strict.
  by intros=> H;
     rewrite -(mu_in_supp_eq (dinter i j) cpTrue);
     try apply fun_ext; smt.
  qed.
end Dinter_uni.

(** Restriction of a distribution (sub-distribution) *)
theory Drestr.
  op drestr: 'a distr -> 'a set -> 'a distr.
 
  axiom supp_def (x:'a) d X:
    in_supp x (drestr d X) <=> in_supp x d /\ !mem x X.
  
  axiom mu_x_def_notin (x:'a) d (X:'a set):
    in_supp x d => !mem x X => mu_x (drestr d X) x = mu_x d x.

  lemma nosmt mu_x_def_in (x:'a) d (X:'a set):
    in_supp x d => mem x X => mu_x (drestr d X) x = 0%r by [].

  axiom weight_def (d:'a distr) X:
    weight (drestr d X) = weight d - mu d (cpMem X).
end Drestr.

(** Scaled restriction of a distribution *)
theory Dexcepted.
  op (\) (d:'a distr, X:'a set) : 'a distr = Dscale.dscale (Drestr.drestr d X).

  lemma supp_def (x:'a) d X:
    (in_supp x (d \ X) => (in_supp x d /\ !mem x X)) /\
    ((in_supp x d /\ !mem x X) => in_supp x (d \ X)).
  proof strict.
  by rewrite /(\) Dscale.supp_def Drestr.supp_def.
  qed.
    
  lemma mu_x_def (x:'a) d X:
    mu_x (d \ X) x =
    (in_supp x (d \ X)) ? mu_x d x / (weight d - mu d (cpMem X)) : 0%r.
  proof strict.
    rewrite /(\); case (weight d - mu d (cpMem X) = 0%r)=> weight.
      by rewrite /mu_x Dscale.mu_def_0 ?Drestr.weight_def //
                 /in_supp
                 (_: (0%r < mu_x (Dscale.dscale (Drestr.drestr d X)) x) = false)=> //=;
         first smt.
      by smt.
  qed.

  lemma nosmt mu_weight_def (d:'a distr) X:
    weight (d \ X) = (weight d = mu d (cpMem X)) ? 0%r : 1%r.
  proof strict.
  (* cut weight_cpMem: mu d (cpMem X) <= weight d by (by rewrite /weight mu_sub). *)
  case (weight d = mu d (cpMem X))=> weight_d //=.
    by rewrite /weight /(\) Dscale.mu_def_0 // Drestr.weight_def weight_d; smt.
    by rewrite /(\) Dscale.weight_pos // Drestr.weight_def; smt.
  qed.
    
  lemma lossless_restr (d:'a distr) X:
    weight d = 1%r =>
    mu d (cpMem X) < 1%r =>
    Distr.weight (d \ X) = 1%r. 
  proof strict.
   intros Hll Hmu; simplify (\);
   (rewrite Distr.Dscale.weight_pos;last smt);
   rewrite Drestr.weight_def;smt.
  qed.
end Dexcepted.
