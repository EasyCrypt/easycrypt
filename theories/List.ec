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
intros=> xs; elimT list_ind xs=> // x xs' IH h {h};
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
lemma mem_eq: forall (x:'a) xs, mem x (x::xs) by [].
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
intros=> xs; elimT list_ind xs; first smt.
by intros=> x xs' len_xs'_nneg; rewrite length_cons; smt.
qed.

lemma length_cons_pos: forall (x:'a) xs, 0 < length (x::xs) by [].

lemma length0_nil: forall (xs:'a list), length xs = 0 => xs = [].
proof strict.
intros=> xs; elimT list_ind xs=> //; smt.
qed.

(** append *)
op (++):'a list -> 'a list -> 'a list.
axiom app_nil: forall (ys:'a list), [] ++ ys = ys.
axiom app_cons: forall (x:'a) xs ys, (x::xs) ++ ys = x::(xs ++ ys).

(* Lemmas *)
lemma appCcons: forall (x:'a) xs ys, (x::xs) ++ ys = x::(xs ++ ys) by [].

lemma app_nilR: forall (xs:'a list), xs ++ [] = xs.
proof strict.
by intros=> xs; elimT list_ind xs; smt.
qed.

lemma appA: forall (xs ys zs:'a list),
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
proof strict.
by intros=> xs ys zs; elimT list_ind xs; smt.
qed.

lemma length_app: forall (xs ys:'a list),
  length (xs ++ ys) = length xs + length ys.
proof strict.
by intros=> xs ys; elimT list_ind xs; smt.
qed.

lemma mem_app: forall (y:'a) xs ys,
  (mem y xs \/ mem y ys) = mem y (xs ++ ys).
proof strict.
intros=> y xs ys; elimT list_ind xs; first smt.
intros=> x xs' IH.
by rewrite appCcons 2!mem_cons orA IH.
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
intros=> p xs; elimT list_ind xs; first smt.
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
intros=> p xs; elimT list_ind xs; first smt.
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
intros=> p x xs; elimT list_ind xs; first smt.
intros=> x' xs' IH; case (p x')=> p_x'.
  by rewrite filter_consT // 2!mem_cons; smt.
  by rewrite filter_consF // mem_cons;smt.
qed.

lemma filter_app: forall (p:'a cpred) xs ys,
  filter p (xs ++ ys) = filter p xs ++ filter p ys.
proof strict.
by intros=> p xs ys; elimT list_ind xs; smt.
qed.

lemma length_filter: forall (p:'a cpred) xs,
  length (filter p xs) <= length xs.
proof strict.
by intros=> p xs; elimT list_ind xs; smt.
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
by intros=> f x xs; elimT list_ind xs; smt.
qed.

lemma mapO: forall (f:'a -> 'b) (g:'b -> 'c) (h:'a -> 'c) xs,
  (forall x, g (f x) = h x) =>
  map g (map f xs) = map h xs.
proof strict.
by intros=> f g h xs fOg; elimT list_ind xs; smt.
qed.

lemma map_app: forall (f:'a -> 'b) xs ys,
  map f (xs ++ ys) = map f xs ++ map f ys.
proof strict.
by intros f xs ys; elimT list_ind xs; smt.
qed.

lemma length_map: forall (f:'a -> 'b) xs,
  length (map f xs) = length xs.
proof strict.
by intros f xs; elimT list_ind xs; smt.
qed.

(** unique *)
op unique:'a list -> bool.
axiom unique_nil: unique<:'a> [].
axiom unique_cons: forall (x:'a) xs, unique (x::xs) = (unique xs /\ !mem x xs).

(* Lemmas *)
  (* TODO *)

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
intros=> xs; elimT list_ind xs; first smt.
by clear xs=> x xs IH n n_neg; rewrite nth_consN 1?IH; smt.
qed.

lemma nth_geq_len: forall (xs:'a list) n, length xs <= n => nth xs n = None.
proof strict.
intros=> xs; elimT list_ind xs; first smt.
by clear xs=> x xs IH n n_len; rewrite nth_consN 1?IH; smt.
qed.

(** nth_default *)
op nth_default (xs:'a list) (dv:'a) n =
  let r = nth xs n in
  if (r <> None)
  then proj r
  else dv.
