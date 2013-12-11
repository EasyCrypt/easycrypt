require import Logic.
require import Int.
require import Fun.

require        List.
import List.Core.

op default:'a.

(** Destructors (partially specified) *)
(* Head *)
op hd (xs:'a list) =
  list_rect default (fun x xs v, x) xs.

lemma hd_cons (x:'a) xs: hd (x::xs) = x.
proof strict.
by rewrite /hd list_rect_cons.
qed.

(* Tail *)
op tl (xs:'a list) =
  list_rect (default::[]) (fun x xs v, xs) xs.
lemma tl_cons (x:'a) xs: tl (x::xs) = xs.
proof strict.
by rewrite /tl list_rect_cons.
qed.

(*** Derived Constructions *)
(** fold_right *)
op fold_right (f:'a -> 'b -> 'b) (v:'b): 'a list -> 'b =
  list_rect v (fun x xs, f x).

(* Direct inductive definition *)
lemma fold_right_nil (f:'a -> 'b -> 'b) (v:'b):
  fold_right f  v [] = v.
proof strict.
by rewrite /fold_right list_rect_nil.
qed.

lemma fold_right_cons (f:'a -> 'b -> 'b) (v:'b) x xs:
  fold_right f v (x::xs) = f x (fold_right f v xs).
proof strict.
by rewrite /fold_right list_rect_cons.
qed.

(** mem *)
op mem(x:'a) = fold_right (fun y intl, (x = y) \/ intl) false.

(* Direct inductive definition *)
lemma mem_nil (x:'a): !(mem x []).
proof strict.
by rewrite /mem fold_right_nil.
qed.

lemma mem_cons (y x:'a) xs:
  mem y (x::xs) = ((y = x) \/ mem y xs).
proof strict.
by rewrite /mem fold_right_cons.
qed.

(*** length *)
op length = fold_right (fun (x:'a) l, l + 1) 0.
op __abs:'a list -> int  = length. (* notation *)

(* Direct inductive definition *)
lemma length_nil: length<:'a> [] = 0.
proof strict.
by rewrite /length fold_right_nil.
qed.

lemma length_cons (x:'a) xs: length (x::xs) = 1 + length xs.
proof strict.
by rewrite /length fold_right_cons /=; smt. (* x + 1 = 1 + x *)
qed.

(** append *)
op (++)(xs ys:'a list): 'a list = fold_right (::) ys xs.

(* Direct inductive definition *)
lemma app_nil (ys:'a list): [] ++ ys = ys.
proof strict.
by rewrite /(++) fold_right_nil.
qed.

lemma app_cons (x:'a) xs ys: (x::xs) ++ ys = x::(xs ++ ys).
proof strict.
by rewrite /(++) fold_right_cons.
qed.

(** rev *)
op rev = fold_right<:'a list,'a> (fun x xs, xs ++ (x::[])) [].

(* Direct inductive definition *)
lemma rev_nil: rev<:'a> [] = [].
proof strict.
by rewrite /rev fold_right_nil.
qed.

lemma rev_cons (x:'a) xs: rev (x::xs) = (rev xs) ++ (x::[]).
proof strict.
by rewrite /rev fold_right_cons.
qed.

(** all *)
pred all(p:'a cpred) xs = forall x, mem x xs => p x.

(* Direct inductive definition *)
lemma all_nil (p:'a cpred): all p [].
proof strict.
rewrite /all=> x; apply absurd=> _; apply mem_nil.
qed.

lemma all_cons (p:'a cpred) x xs:
  all p (x::xs) = ((p x) /\ all p xs).
proof strict.
rewrite /all rw_eq_iff; split.
  intros=> Hxxs; split; try (intros=> x' x'_in_xs); apply Hxxs; rewrite mem_cons; [by left | by right].
  intros=> [Hx Hxs] x' x'_in_xxs; case (x' = x)=> x_x'.
    by subst x'.
    by apply Hxs; generalize x'_in_xxs; rewrite mem_cons=> x'_in_xxs; elim x'_in_xxs=> //; by apply absurd.
qed.

(** forallb *)
op forallb (p:'a cpred) = fold_right (fun x r, (p x) /\ r) true.

(* Direct inductive definition *)
lemma forallb_nil (p:'a cpred): forallb p [].
proof strict.
by rewrite /forallb fold_right_nil.
qed.

lemma forallb_cons (p:'a cpred) x xs: forallb p (x::xs) = ((p x) /\ forallb p xs).
proof strict.
by rewrite /forallb fold_right_cons.
qed.

(** any *)
pred any (p:'a cpred) xs = exists x, mem x xs /\ p x.

(* Direct inductive definition *)
lemma any_nil (p:'a cpred): !(any p []) by [].
lemma any_cons (p:'a cpred) x xs:
  any p (x::xs) = ((p x) \/ any p xs).
proof strict.
rewrite /any rw_eq_iff; split.
  intros=> Hxxs; elim Hxxs=> {Hxxs} x' [Hxxs Hxs] //; case (x' = x)=> x'_x.
    by subst x'; left.
    by right; exists x'; split=> //;
       generalize Hxxs; rewrite mem_cons=> Hxxs; elim Hxxs=> //; apply absurd.
   by intros=> [Hx | Hxs]; [exists x | elim Hxs=> {Hxs} x' [Hxs Hx']; exists x']; split;
      rewrite ?mem_cons //; right.
qed.

(** existsb *)
op existsb (p:'a cpred) = fold_right (fun x r, (p x) \/ r) false.

(* Direct inductive definition *)
lemma existsb_nil (p:'a cpred): !(existsb p []).
by rewrite /existsb fold_right_nil.
qed.

lemma existsb_cons (p:'a cpred) x xs:
  existsb p (x::xs) = ((p x) \/ existsb p xs).
proof strict.
by rewrite /existsb fold_right_cons.
qed.

(** filter *)
op filter (p:'a cpred) =
  fold_right (fun x r, if p x then x::r else r) [].

(* Direct inductive definition *)
lemma filter_nil (p:'a cpred):
  filter p [] = [].
proof strict.
by rewrite /filter fold_right_nil.
qed.

lemma filter_cons (p:'a cpred) x xs:
  filter p (x::xs) = let rest = filter p xs in
                     if p x then x::rest else rest.
proof strict.
by rewrite /filter fold_right_cons.
qed.

(** map *)
op map (f:'a -> 'b) = fold_right (fun x xs, (f x)::xs) [].

(* Direct inductive definition *)
lemma map_nil (f:'a -> 'b): map f [] = [].
proof strict.
by rewrite /map fold_right_nil.
qed.

lemma map_cons (f:'a -> 'b) x xs:
  map f (x::xs) = (f x)::(map f xs).
proof strict.
by rewrite /map fold_right_cons.
qed.

(** nth *)
require import Option.
require import Pair.
op nth (xs:'a list) =
  fold_right (fun (x:'a) (r:'a option -> int -> 'a option) (y:'a option) (n:int),
                if n = 0 then Some x else (r y (n - 1)))
             (fun y n, y) xs None.


(* Direct inductive definition *)
lemma nth_nil n: nth<:'a> [] n = None by [].
lemma nth_cons0 (x:'a) xs: nth (x::xs) 0 = Some x by [].
lemma nth_consN (x:'a) xs n:
  0 <> n =>
  nth (x::xs) n = nth xs (n - 1) by [].

(** count *)
op count (x:'a) =
  list_rect 0 (fun y xs n, n + ((x = y) ? 1 : 0)).

(** Direct inductive definition *)
lemma count_nil (x:'a): count x [] = 0 by [].

lemma count_cons (x y:'a) xs:
  count y (x::xs) = count y xs + (if (x = y) then 1 else 0).
proof strict.
by rewrite /count list_rect_cons /= (rw_eq_sym x y).
qed.

(** unique *)
op unique: 'a list cpred =
  list_rect true (fun x xs v, v /\ !mem x xs).

(* Direct inductive definition *)
lemma unique_nil: unique<:'a> []
by (rewrite /unique list_rect_nil //).

lemma unique_cons (x:'a) xs:
  unique (x::xs) = (unique xs /\ !mem x xs).
proof strict.
by rewrite /unique list_rect_cons.
qed.

(** rm *)
op rm (x:'a) (xs:'a list) =
  list_rect [] (fun y ys v, if (x = y) then ys else y::v) xs.

lemma rm_nil (x:'a): rm x [] = []
by (rewrite /rm list_rect_nil //).

lemma rm_cons (x y:'a) xs:
  rm y (x::xs) = ((x = y) ? xs : (x::rm y xs)).
proof strict.
by rewrite /rm list_rect_cons /= (rw_eq_sym x y).
qed.

(** Equality up to permutation *)
pred (<->) (xs xs':'a list) =
  forall (x:'a), count x xs = count x xs'.  