require import Logic.
require import Int.
require import Fun.

(*** Type Definition is imported from Why3 *)
import why3 "list" "List"
   op "Nil" as "__nil";
   op "Cons" as "::".

(*** Recursion and Induction Principles *)
(** Recursion principle *)
op list_rect: 'b -> ('a -> 'a list -> 'b -> 'b) -> 'a list -> 'b.
axiom list_rect_nil: forall v f,
  list_rect<:'b,'a> v f [] = v.
axiom list_rect_cons: forall v f x xs,
  list_rect<:'b,'a> v f (x::xs) = f x xs (list_rect v f xs).

(** Induction principle. *)
(* We cannot prove it from list_rect because
   types and terms are disjoint. *)
axiom list_ind: forall (p:('a list) cpred),
  p [] =>
  (forall x xs, p xs => p (x::xs)) =>
  (forall xs, p xs).

(*** Destructors (partially specified) *)
(** Head *)
op hd: 'a list -> 'a.
axiom hd_cons: forall (x:'a) xs, hd (x::xs) = x.

(** Tail *)
op tl: 'a list -> 'a list.
axiom tl_cons: forall (x:'a) xs, tl (x::xs) = xs.

(*** General Lemmas *)
(** List case analysis *)
lemma list_case: forall (p: 'a list cpred), 
    p [] => 
    (forall x l, p (x::l)) =>
    (forall l, p l)
by [].

lemma list_case_eq: forall (p: 'a list cpred) (l:'a list),
    (l = [] => p l) =>
    (forall x l', l = x::l' => p l) =>
    p l.
intros=> p l.
elim/list_case l => //.
intros=> x l' _ h.
apply (h x l').
qed.

(** Constructor Disjointness *)
lemma nil_neq_cons: forall (x:'a) xs, [] <> x::xs by [].

(** Datatype *)
lemma list_destruct: forall (xs:'a list),
  xs = [] \/ (exists (y:'a) ys, xs = y::ys)
by [].

(** A lemma on hd and tail *)
lemma hd_tl_cons: forall (xs:'a list),
  xs <> [] => (hd xs)::(tl xs) = xs.
proof strict.
intros=> xs; elim/list_ind xs=> // x xs' IH h {h};
rewrite hd_cons tl_cons=> //.
qed.

(*** Operator Specifications *)
(** Fold *)
op fold_right:('a -> 'b -> 'b) -> 'b -> 'a list -> 'b.
axiom fold_right_nil: forall (f:'a -> 'b -> 'b) (e:'b),
  fold_right f  e [] = e.
axiom fold_right_cons: forall (f:'a -> 'b -> 'b) (e:'b) x xs,
  fold_right f e (x::xs) = f x (fold_right f e xs).

(** mem *)
op mem:'a -> 'a list -> bool.
axiom mem_nil: forall (x:'a), !(mem x []).
axiom mem_cons: forall (y x:'a) xs,
  mem y (x::xs) = ((y = x) \/ mem y xs).

(* Lemmas *)
lemma mem_consE: forall (x:'a) xs, mem x (x::xs) by [].
lemma mem_consNE: forall (x y:'a) xs, x <> y => mem y (x::xs) = mem y xs by [].
lemma memM_cons : forall (x y:'a) xs, mem y xs => mem y (x::xs) by [].
lemma mem_hd: forall (xs:'a list), xs <> [] => mem (hd xs) xs by [].
lemma nil_nmem: forall (xs:'a list), xs = [] <=> (forall x, !mem x xs) by [].

(*** length *)
op length:'a list -> int.
op __abs:'a list -> int  = length. (* notation *)
axiom length_nil: length<:'a> [] = 0.
axiom length_cons: forall (x:'a) xs, length (x::xs) = 1 + length xs.

(* Lemmas *)
lemma length_nneg: forall (xs:'a list), 0 <= length xs.
proof strict.
intros=> xs; elim/list_ind xs; first smt.
by intros=> x xs' len_xs'_nneg; rewrite length_cons; smt.
qed.

lemma length_cons_pos: forall (x:'a) xs, 0 < length (x::xs) by [].

lemma length0_nil: forall (xs:'a list), length xs = 0 => xs = [].
proof strict.
intros=> xs; elim/list_ind xs=> //; smt.
qed.

(** append *)
op (++):'a list -> 'a list -> 'a list.
axiom app_nil: forall (ys:'a list), [] ++ ys = ys.
axiom app_cons: forall (x:'a) xs ys, (x::xs) ++ ys = x::(xs ++ ys).

(* Lemmas *)
lemma appCcons: forall (x:'a) xs ys, (x::xs) ++ ys = x::(xs ++ ys) by [].

lemma app_nilR: forall (xs:'a list), xs ++ [] = xs.
proof strict.
by intros=> xs; elim/list_ind xs; smt.
qed.

lemma appA: forall (xs ys zs:'a list),
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
proof strict.
by intros=> xs ys zs; elim/list_ind xs; smt.
qed.

lemma length_app: forall (xs ys:'a list),
  length (xs ++ ys) = length xs + length ys.
proof strict.
by intros=> xs ys; elim/list_ind xs; smt.
qed.

lemma mem_app: forall (y:'a) xs ys,
  (mem y xs \/ mem y ys) = mem y (xs ++ ys).
proof strict.
intros=> y xs ys; elim/list_ind xs; first smt.
intros=> x xs' IH.
by rewrite appCcons 2!mem_cons orA IH.
qed.

(** rev *)
op rev: 'a list -> 'a list.
axiom rev_nil: rev<:'a> [] = [].
axiom rev_cons: forall (x:'a) xs, rev (x::xs) = (rev xs) ++ (x::[]).

(* Lemmas *)
lemma rev_app: forall (xs ys:'a list),
  rev (xs ++ ys) = (rev ys) ++ (rev xs).
proof strict.
intros=> xs; elim/list_ind xs=> {xs}.
  by intros=> ys; rewrite rev_nil app_nil app_nilR //.
  by intros=> x xs IH ys; rewrite appCcons 2!rev_cons -appA IH //.
qed.

lemma rev_rev: forall (xs:'a list),
  rev (rev xs) = xs.
proof strict.
intros=> xs; elim/list_ind xs=> {xs}.
  by rewrite 2!rev_nil //.
  by intros=> x xs IH; rewrite rev_cons rev_app IH rev_cons
                               rev_nil app_nil appCcons app_nil //.
qed.

(** all *)
pred all(p:'a cpred) xs = forall x, mem x xs => p x.

(* Direct inductive definition *)
lemma all_nil: forall (p:'a cpred), all p [] by [].
lemma all_cons: forall (p:'a cpred) x xs, all p (x::xs) = ((p x) /\ all p xs) by [].

(* Lemmas *)
lemma all_app: forall (p:'a cpred) xs ys, all p (xs ++ ys) = (all p xs /\ all p ys) by [].

(** forallb *)
op forallb:'a cpred -> 'a list -> bool.
axiom forallb_nil: forall (p:'a cpred), forallb p [].
axiom forallb_cons: forall (p:'a cpred) x xs,
  forallb p (x::xs) = ((p x) /\ forallb p xs).

(* Lemmas *)
lemma forallb_eq_all: forall (p:'a cpred) xs, all p xs <=> forallb p xs.
proof strict.
intros=> p xs; elim/list_ind xs; first smt.
by intros=> y ys IH; rewrite all_cons forallb_cons IH.
qed.

(** any *)
pred any (p:'a cpred) xs = exists x, mem x xs /\ p x.

(* Direct inductive definition *)
lemma any_nil: forall (p:'a cpred), !(any p []) by [].
lemma any_cons: forall (p:'a cpred) x xs, any p (x::xs) = ((p x) \/ any p xs) by [].

(* Lemmas *)
lemma any_app: forall (p:'a cpred) xs ys, any p (xs ++ ys) = (any p xs \/ any p ys) by [].

(** existsb *)
op existsb:'a cpred -> 'a list -> bool.
axiom existsb_nil: forall (p:'a cpred), !(existsb p []).
axiom existsb_cons: forall (p:'a cpred) x xs,
  existsb p (x::xs) = ((p x) \/ existsb p xs).

(* Lemmas *)
lemma existsb_eq_any: forall (p:'a cpred) xs, any p xs <=> existsb p xs.
proof strict.
intros=> p xs; elim/list_ind xs; first smt.
by intros=> y ys IH; rewrite any_cons existsb_cons IH.
qed.

(** filter *)
op filter:'a cpred -> 'a list -> 'a list.
axiom filter_nil: forall (p:'a cpred), filter p [] = [].
axiom filter_cons: forall (p:'a cpred) x xs,
  filter p (x::xs) = let rest = filter p xs in
                     if p x then x::rest else rest.

(* Lemmas *)
lemma filter_consT: forall (p:'a cpred) x xs,
  p x => filter p (x::xs) = x::(filter p xs)
by [].

lemma filter_consF: forall (p:'a cpred) x xs,
  !(p x) => filter p (x::xs) = filter p xs
by [].

lemma filter_mem: forall (p:'a cpred) x xs,
  mem x (filter p xs) = (mem x xs /\ p x).
proof strict.
intros=> p x xs; elim/list_ind xs; first smt.
intros=> x' xs' IH; case (p x')=> p_x'.
  by rewrite filter_consT // 2!mem_cons; smt.
  by rewrite filter_consF // mem_cons;smt.
qed.

lemma filter_app: forall (p:'a cpred) xs ys,
  filter p (xs ++ ys) = filter p xs ++ filter p ys.
proof strict.
by intros=> p xs ys; elim/list_ind xs; smt.
qed.

lemma length_filter: forall (p:'a cpred) xs,
  length (filter p xs) <= length xs.
proof strict.
by intros=> p xs; elim/list_ind xs; smt.
qed.

lemma all_filter: forall (p:'a cpred) xs,
  all p (filter p xs)
by [].

lemma filter_imp: forall (p q:'a cpred) xs,
  p <= q =>
  forall x, mem x (filter p xs) => mem x (filter q xs)
by [].

(** map *)
op map:('a -> 'b) -> 'a list -> 'b list.
axiom map_nil: forall (f:'a -> 'b), map f [] = [].
axiom map_cons: forall (f:'a -> 'b) x xs,
  map f (x::xs) = (f x)::(map f xs).

(* Lemmas *)
lemma map_in: forall (f:'a -> 'b) x xs,
  mem x xs => mem (f x) (map f xs).
by intros=> f x xs; elim/list_ind xs; smt.
qed.

lemma mapO: forall (f:'a -> 'b) (g:'b -> 'c) (h:'a -> 'c) xs,
  (forall x, g (f x) = h x) =>
  map g (map f xs) = map h xs.
proof strict.
by intros=> f g h xs fOg; elim/list_ind xs; smt.
qed.

lemma map_app: forall (f:'a -> 'b) xs ys,
  map f (xs ++ ys) = map f xs ++ map f ys.
proof strict.
by intros f xs ys; elim/list_ind xs; smt.
qed.

lemma length_map: forall (f:'a -> 'b) xs,
  length (map f xs) = length xs.
proof strict.
by intros f xs; elim/list_ind xs; smt.
qed.

(** nth *)
require import Option.
require import Pair.

op nth:'a list -> int -> 'a option.
axiom nth_nil: forall n, nth<:'a> [] n = None.
axiom nth_cons0: forall (x:'a) xs,
  nth (x::xs) 0 = Some x.
axiom nth_consN: forall (x:'a) xs n,
  0 <> n =>
  nth (x::xs) n = nth xs (n - 1).

(* Lemmas *)
lemma nth_neg: forall (xs:'a list) n, n < 0 => nth xs n = None.
proof strict.
intros=> xs; elim/list_ind xs; first smt.
by clear xs=> x xs IH n n_neg; rewrite nth_consN 1?IH; smt.
qed.

lemma nth_geq_len: forall (xs:'a list) n, length xs <= n => nth xs n = None.
proof strict.
intros=> xs; elim/list_ind xs; first smt.
by clear xs=> x xs IH n n_len; rewrite nth_consN 1?IH; smt.
qed.

(** nth_default *)
op nth_default (xs:'a list) (dv:'a) n =
  let r = nth xs n in
  if (r <> None)
  then proj r
  else dv.

(** count *)
op count:'a -> 'a list -> int.
axiom count_nil: forall (x:'a), count x [] = 0.
axiom count_cons: forall (x y:'a) xs,
  count y (x::xs) = count y xs + if (x = y) then 1 else 0.

(* Lemmas *)
lemma nosmt count_consE: forall (x:'a) xs, count x (x::xs) = 1 + count x xs by [].
lemma nosmt count_consNE: forall (x y:'a) xs, x <> y => count y (x::xs) = count y xs by [].

lemma count_nneg: forall (x:'a) (xs:'a list),
  0 <= count x xs.
proof strict.
intros=> x xs; generalize x; elim/list_ind xs=> x {xs}.
  by rewrite count_nil; smt. (* reflexivity of Int.(<=) *)
  intros=> xs IH x'; rewrite count_cons; smt. (* 0 <= x => 0 <= y => 0 <= y + x *)
qed.

lemma count_mem: forall (x:'a) (xs:'a list),
  0 <> count x xs <=> mem x xs.
proof strict.
intros=> x xs; generalize x; elim/list_ind xs=> x {xs}.
  rewrite count_nil; simplify; apply mem_nil.
  intros=> xs IH x'; rewrite count_cons; smt.
qed.

(** unique *)
op unique:'a list -> bool.
axiom unique_nil: unique<:'a> [].
axiom unique_cons: forall (x:'a) xs, unique (x::xs) = (unique xs /\ !mem x xs).

(* Lemmas *)
lemma unique_count: forall (xs:'a list),
  unique xs <=> (forall x, count x xs <= 1).
proof strict.
intros=> xs; split.
  elim/list_ind xs=> {xs}.
    by intros=> h x {h}; rewrite count_nil; smt.
    intros=> x xs IH; rewrite unique_cons -count_mem;
    simplify; intros=> [u_xs x_nin_xs] x'; case (x = x')=> x_x'.
      by subst x'; rewrite count_consE -x_nin_xs; smt.
      by rewrite count_consNE //; apply IH=> //.
  elim/list_ind xs=> {xs}.
    by intros=> h {h}; apply unique_nil.
    by intros=> x xs IH count_xs; rewrite unique_cons; split; smt.
qed.

(** rm *)
op rm:'a -> 'a list -> 'a list.
axiom rm_nil: forall (x:'a), rm x [] = [].
axiom rm_cons: forall (y x:'a) xs, rm y (x::xs) = ((x = y) ? xs : (x::rm y xs)).

(* Lemmas *)
lemma nosmt rm_consE: forall (x:'a) xs, rm x (x::xs) = xs by [].
lemma nosmt rm_consNE: forall (x y:'a) xs, x <> y => rm y (x::xs) = x::(rm y xs) by [].

lemma length_rm: forall (x:'a) xs,
  mem x xs =>
  length (rm x xs) = length xs - 1.
proof strict.
intros=> x xs; elim/list_ind xs=> {xs}.
  by apply absurd=> h {h}; apply mem_nil.
  intros=> x' xs IH x_in_xs; rewrite length_cons; case (x' = x)=> x_x'.
    by subst x'; rewrite rm_consE; smt.
    by generalize x_in_xs; rewrite mem_consNE // rm_consNE // length_cons=> x_in_xs; rewrite IH //; smt.
qed.

lemma count_rm_in: forall (x:'a) (xs:'a list),
  mem x xs =>
  count x (rm x xs) = count x xs - 1.
proof strict.
intros=> x xs; generalize x; elim/list_ind xs=> x {xs}.
  apply absurd=> _; apply mem_nil.
  intros=> xs IH y x'; rewrite rm_cons (rewrite_if (count y)); smt.
qed.

lemma count_rm_nin: forall (x:'a) (xs:'a list),
  !mem x xs =>
  count x (rm x xs) = count x xs.
proof strict.
intros=> x xs; generalize x; elim/list_ind xs=> x {xs}.
  intros=> h {h}; rewrite rm_nil //.
  intros=> xs IH x'; rewrite mem_cons; smt.
qed.

lemma count_rm_neq: forall (x y:'a) (xs:'a list),
  y <> x =>
  count x (rm y xs) = count x xs.
proof strict.
intros=> x y xs; elim/list_ind xs=> {xs}.
  rewrite rm_nil //.
  intros=> x' xs IH x_y; smt.
qed.

theory PermutationLists.
  (** Equality up to permutation *)
  pred (<->) (xs xs':'a list) =
    forall (x:'a), count x xs = count x xs'.

  lemma perm_refl: forall (xs:'a list), xs <-> xs by [].
  lemma perm_symm: forall (xs ys:'a list), xs <-> ys => ys <-> xs by [].
  lemma perm_trans: forall (ys xs zs:'a list), xs <-> ys => ys <-> zs => xs <-> zs by [].

  lemma perm_nil: forall (xs:'a list),
    xs <-> [] =>
    xs = [].
  proof strict.
  intros=> xs; delta (<->) beta=> xs_nil;
  cut h: forall (x:'a), count x xs = 0.
    by intros=> x; rewrite -(count_nil x) xs_nil //.
    smt. (* TODO: Add lemmas to count *)
  qed.

  lemma perm_cons: forall x (xs ys:'a list),
    xs <-> ys =>
    (x::xs) <-> (x::ys)
  by [].

lemma perm_rm: forall x (xs ys:'a list),
  xs <-> ys =>
  (rm x xs) <-> (rm x ys).
proof strict.
intros=> x xs ys; case (mem x xs).
  intros=> x_in_xs xs_ys; cut x_in_ys: mem x ys; first by rewrite -count_mem -(xs_ys x) count_mem //.
    delta (<->) beta=> x'; case (x = x')=> x_x'.
      subst x'; rewrite count_rm_in // count_rm_in // xs_ys //.
      rewrite count_rm_neq // count_rm_neq // xs_ys //.
  intros=> x_nin_xs xs_ys; cut x_nin_ys: !mem x ys; first by rewrite -count_mem -(xs_ys x) count_mem //.
    delta (<->) beta=> x'; case (x = x')=> x_x'.
      subst x'; rewrite count_rm_nin // count_rm_nin // xs_ys //.
      rewrite count_rm_neq // count_rm_neq // xs_ys //.
qed.

lemma foldC: forall (x:'a) (f:'a -> 'b -> 'b) (z:'b) (xs:'a list),
    (forall a b X, f a (f b X) = f b (f a X)) =>
    mem x xs =>
    fold_right f z xs = f x (fold_right f z (rm x xs)).
proof strict.
intros=> x f z xs C; elim/list_ind xs=> {xs}; first smt.
  intros=> x' xs IH.
  rewrite fold_right_cons.
  case (x' = x)=> x_x';first subst x';rewrite rm_consE //.
  rewrite mem_consNE=> // x_in_xs.
  by rewrite rm_consNE // fold_right_cons IH // C //.
qed.

lemma foldCA: forall (f:'a -> 'a -> 'a) (z x:'a) (xs:'a list),
  (forall x y, f x y = f y x) =>
  (forall x y z, f x (f y z) = f (f x y) z) =>
  mem x xs =>
  fold_right f z xs = f x (fold_right f z (rm x xs)).
proof strict.
intros f z x xs C A.
apply foldC=> a b c.
rewrite A (C a) -A //.
qed.

lemma fold_permC: forall (f:'a -> 'b -> 'b) (z:'b) (xs ys:'a list),
  (forall a b X, f a (f b X) = f b (f a X)) =>
  xs <-> ys =>
  fold_right f z xs = fold_right f z ys.
proof strict.
intros=> f z xs ys C;generalize ys; elim/list_ind xs=> {xs}.
  by intros=> ys nil_ys; rewrite (perm_nil ys); [apply perm_symm=> // | trivial ].
  intros=> x xs IH ys xs_ys; rewrite fold_right_cons (foldC x _ _ ys); first assumption.
  rewrite -count_mem -xs_ys; smt.
     congr=> //; cut rm_xs_ys: xs <-> rm x ys;
       first by rewrite -(rm_consE x xs); apply perm_rm=> //.
      rewrite (IH (rm x ys))=> //.
qed.

lemma fold_perm: forall (f:'a -> 'a -> 'a) (z:'a) (xs ys:'a list),
  (forall x y, f x y = f y x) =>
  (forall x y z, f x (f y z) = f (f x y) z) =>
  xs <-> ys =>
  fold_right f z xs = fold_right f z ys.
proof strict.
intros f z x xs C A.
apply fold_permC=> a b c.
rewrite A (C a) -A //.
qed.

(** Properties of unique lists up to permutation *)
lemma perm_unique: forall (xs ys:'a list),
  xs <-> ys =>
  unique xs =>
  unique ys
by [].

lemma cons_nin: forall (x:'a) (xs ys:'a list),
  unique ys =>
  x::xs <-> ys =>
  !mem x xs
by [].

lemma perm_length: forall (xs ys:'a list),
  xs <-> ys =>
  length xs = length ys.
proof strict.
intros=> xs; elim/list_ind xs=> {xs}.
  smt.
  intros=> x xs IH ys xs_ys.
    rewrite length_cons (IH (rm x ys)).
      by rewrite -(rm_consE x xs); apply perm_rm=> //. (* This should become a lemma *)
      by rewrite length_rm; smt.
qed.
end PermutationLists.
