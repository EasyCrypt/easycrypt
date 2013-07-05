require import Logic.
require import Int.
require import Fun.

(** Type Definition is imported from Why3 *)
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
axiom list_ind: forall (P:('a list) cpred),
  (P []) =>
  (forall x xs, P xs => P (x::xs)) =>
  (forall ys, P ys).

(** Destructors (partially specified) *)
(* Head *)
op hd: 'a list -> 'a.
axiom hd_cons: forall (x:'a) xs, hd (x::xs) = x.

(* Tail *)
op tl: 'a list -> 'a list.
axiom tl_cons: forall (x:'a) xs, tl (x::xs) = xs.

(*** General Lemmas *)
(** List case analysis *)
lemma list_case: forall (p: 'a list -> bool), 
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
by intros=> xs; elim/list_ind xs=> // x xs' IH h {h};
   rewrite hd_cons tl_cons=> //.
qed.

(*** Derived Constructions *)
(** fold_right *)
op fold_right (f:'a -> 'b -> 'b) (v:'b): 'a list -> 'b =
  list_rect v (lambda x xs, f x).

(* Direct inductive definition *)
lemma fold_right_nil: forall (f:'a -> 'b -> 'b) (v:'b),
  fold_right f  v [] = v.
proof strict.
by intros=> f v;
   delta fold_right beta; rewrite list_rect_nil=> //.
qed.

lemma fold_right_cons: forall (f:'a -> 'b -> 'b) (v:'b) x xs,
  fold_right f v (x::xs) = f x (fold_right f v xs).
proof strict.
by intros=> f v x xs;
   delta fold_right beta; rewrite list_rect_cons; beta=> //.
qed.

(** mem *)
op mem(x:'a) = fold_right (lambda y intl, (x = y) \/ intl) false.

(* Direct inductive definition *)
lemma mem_nil: forall (x:'a), !(mem x []) by [].
lemma mem_cons: forall (y x:'a) xs,
  mem y (x::xs) = ((y = x) \/ mem y xs).
proof strict.
by intros=> y x xs; delta mem; beta; smt.
qed.

(*** length *)
op length = fold_right (lambda (x:'a) l, l + 1) 0.
op __abs:'a list -> int  = length. (* notation *)

(* Direct inductive definition *)
lemma length_nil: length<:'a> [] = 0 by [].
lemma length_cons: forall (x:'a) xs, length (x::xs) = 1 + length xs by [].

(** append *)
op (++)(xs ys:'a list): 'a list = fold_right (::) ys xs.

(* Direct inductive definition *)
lemma app_nil: forall (ys:'a list), [] ++ ys = ys by [].
lemma app_cons: forall (x:'a) xs ys, (x::xs) ++ ys = x::(xs ++ ys) by [].

(** rev *)
op rev = fold_right<:'a list,'a> (lambda x xs, xs ++ (x::[])) [].

(* Direct inductive definition *)
lemma rev_nil: rev<:'a> [] = [] by [].

lemma rev_cons: forall (x:'a) xs, rev (x::xs) = (rev xs) ++ (x::[]).
proof strict.
intros=> x xs; delta rev beta; rewrite fold_right_cons; beta=> //.
qed.

(** all *)
pred all(p:'a cpred) xs = forall x, mem x xs => p x.

(* Direct inductive definition *)
lemma all_nil: forall (p:'a cpred), all p [] by [].
lemma all_cons: forall (p:'a cpred) x xs, all p (x::xs) = ((p x) /\ all p xs) by [].

(** forallb *)
op forallb(p:'a cpred) = fold_right (lambda x r, (p x) /\ r) true.

(* Direct inductive definition *)
lemma forallb_nil: forall (p:'a cpred), forallb p [] by [].
lemma forallb_cons: forall (p:'a cpred) x xs, forallb p (x::xs) = ((p x) /\ forallb p xs).
proof strict.
by intros=> p x xs; delta forallb; beta; smt.
qed.

(** any *)
pred any (p:'a cpred) xs = exists x, mem x xs /\ p x.

(* Direct inductive definition *)
lemma any_nil: forall (p:'a cpred), !(any p []) by [].
lemma any_cons: forall (p:'a cpred) x xs, any p (x::xs) = ((p x) \/ any p xs) by [].

(** existsb *)
op existsb (p:'a cpred) = fold_right (lambda x r, (p x) \/ r) false.

(* Direct inductive definition *)
lemma existsb_nil: forall (p:'a cpred), !(existsb p []) by [].
lemma existsb_cons: forall (p:'a cpred) x xs, existsb p (x::xs) = ((p x) \/ existsb p xs).
proof strict.
by intros=> p x xs; delta existsb; beta; smt.
qed.

(** filter *)
op filter (p:'a cpred) = fold_right (lambda x r, if p x then x::r else r) [].

(* Direct inductive definition *)
lemma filter_nil: forall (p:'a cpred),
  filter p [] = [].
proof strict.
by intros=> p;
   delta filter beta; rewrite fold_right_nil; beta=> //.
qed.

lemma filter_cons: forall (p:'a cpred) x xs,
  filter p (x::xs) = let rest = filter p xs in
                     if p x then x::rest else rest.
proof strict.
by intros=> p x xs;
   delta filter beta; rewrite fold_right_cons; beta=> //.
qed.

(** map *)
op map (f:'a -> 'b) = fold_right (lambda x xs, (f x)::xs) [].

(* Direct inductive definition *)
lemma map_nil: forall (f:'a -> 'b), map f [] = [] by [].
lemma map_cons: forall (f:'a -> 'b) x xs,
  map f (x::xs) = (f x)::(map f xs)
by [].

(** nth *)
require import Option.
require import Pair.
op nth (xs:'a list) =
  fold_right (lambda (x:'a) (r:'a option -> int -> 'a option) (y:'a option) (n:int),
                if n = 0 then Some x else (r y (n - 1)))
             (lambda y n, y) xs None.


(* Direct inductive definition *)
lemma nth_nil: forall n, nth<:'a> [] n = None by [].
lemma nth_cons0: forall (x:'a) xs,
  nth (x::xs) 0 = Some x by [].
lemma nth_consN: forall (x:'a) xs n,
  0 <> n =>
  nth (x::xs) n = nth xs (n - 1) by [].

(** count *)
op count (x:'a) =
  list_rect 0 (lambda y xs n, n + ((x = y) ? 1 : 0)).

(** Direct inductive definition *)
lemma count_nil: forall (x:'a), count x [] = 0 by [].

lemma count_cons: forall (x y:'a) xs,
  count y (x::xs) = count y xs + (if (x = y) then 1 else 0)
by [].

(** unique *)
op unique: 'a list cpred =
  list_rect true (lambda x xs v, v /\ !mem x xs).

(* Direct inductive definition *)
lemma unique_nil: unique<:'a> []
by (delta unique beta; rewrite list_rect_nil=> //).

lemma unique_cons: forall (x:'a) xs,
  unique (x::xs) = (unique xs /\ !mem x xs).
proof strict.
by intros=> x xs;
   delta unique beta; rewrite list_rect_cons; beta=> //.
qed.

(** rm *)
op rm (x:'a) (xs:'a list) =
  list_rect [] (lambda y ys v, if (x = y) then ys else y::v) xs.

lemma rm_nil: forall (x:'a), rm x [] = [] by [].
lemma rm_cons: forall (x y:'a) xs,
  rm y (x::xs) = ((x = y) ? xs : (x::rm y xs))
by [].

(** Equality up to permutation *)
pred (<->) (xs xs':'a list) =
  forall (x:'a), count x xs = count x xs'.

lemma toto: forall (a b c:bool), (a \/ b) \/ c.
