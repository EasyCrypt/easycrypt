require import Logic.
require import Int.
require import Fun.

(** Type Definition is imported from Why3 *)
import why3 "list" "List"
   op "Nil" as "__nil";
   op "Cons" as "::".

(** Fold *)
op fold_right: ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b.
axiom fold_right_nil: forall (e:'b) (f:'a -> 'b -> 'b),
  fold_right f  e [] = e.
axiom fold_right_cons: forall (e:'b) (f:'a -> 'b -> 'b) x xs,
  fold_right f e (x::xs) = f x (fold_right f e xs).

(** Destructors (partially specified) *)
(* Head *)
op hd: 'a list -> 'a.
axiom hd_def: forall (x:'a) xs, hd (x::xs) = x.

(* Tail *)
op tl: 'a list -> 'a list.
axiom tl_def: forall (x:'a) xs, tl (x::xs) = xs.

(* Induction Principle (should later be free) *)
axiom list_ind: forall (P:('a list) cPred),
  (P []) =>
  (forall x xs, P xs => P (x::xs)) =>
  (forall ys, P ys).


(********** No more axioms **********)

(** Some Lemmas *)
(* NOTE: The two constructor-related lemmas follow
         from facts hidden in the Why3 theory.
         This may change, for example when we roll
         out our own induction. *)

(** List case analysis *)
lemma list_case : 
  forall (p: 'a list -> bool, l:'a list), 
    (l = [] => p []) => 
    (forall x l', l = x :: l' => p (x :: l')) =>
    p l
by [].

lemma nil_cons: forall (x:'a) xs, x::xs <> [] by [].

lemma destruct_list: forall (xs:'a list),
  xs = [] \/ (exists (y:'a) ys, xs = y::ys).
proof.
 intros xs.
 elimT list_case xs.
  intros H;left;trivial.

  intros y ys H;right.
  exists y;exists ys;trivial.
save.

lemma hd_tl_decomp: forall (xs:'a list),
  xs <> [] => (hd xs)::(tl xs) = xs
by [].

(** Derived Operators *)
(* mem: membership test *)
op (* local *) f_mem(x:'a,y,b): bool = x = y \/ b.

op mem (x:'a): 'a list -> bool = 
  fold_right (f_mem x) false.

lemma mem_nil : forall (x : 'a), mem x [] = false by [].
lemma mem_cons : forall(x y : 'a, xs : 'a list), 
 mem y (x::xs) = (x = y \/ mem y xs).
proof.
 intros x y xs.
 simplify mem.
 cut H: (fold_right (f_mem y) false (x :: xs) = 
   f_mem y x (fold_right (f_mem y) false xs)).
 trivial.
 rewrite H.
 trivial.
save.

lemma mem_eq: forall (x:'a) xs, mem x (x::xs) by [].
lemma mem_cons_mon : forall (x y:'a) xs, mem y xs => mem y (x::xs) by [].
lemma mem_not_nil: forall (y:'a) xs, mem y xs => xs <> [] by [].
lemma mem_hd: forall (xs:'a list), xs <> [] => mem (hd xs) xs by [].
lemma not_mem_empty: forall (xs:'a list), xs = [] <=> (forall x, !mem x xs) by [].

(* length *)
op (* local *) f_length(x:'a, b): int = 1 + b.

(*(lambda x, lambda y, 1 + y)*)
op length (xs:'a list): int = fold_right f_length 0 xs.

lemma length_nil: length<:'a> [] = 0 by [].
lemma length_cons: forall (x:'a) xs, 
  length (x::xs) = 1 + length xs
by [].

lemma length_non_neg: forall (xs:'a list), 0 <= length xs.
proof.
 intros xs.
 elimT list_ind xs.
 simplify length; trivial.
 intros y ys IHys.
 cut H1 : (length (y :: ys) = 1 + length ys).
  trivial.
 rewrite H1;trivial.
save.

lemma length_cons_S : forall (xs:'a list, x: 'a), 
 length (x::xs) = 1 + length xs
by [].

lemma length_cons_nz : forall (xs:'a list, x: 'a), length (x::xs) <> 0 by [].

lemma length_z_nil : forall(xs:'a list), length xs = 0 => xs = [].
proof.
intros xs.
elimT list_ind xs;trivial.
save.


(* append *)

op (++) (xs ys: 'a list) : 'a list = fold_right (::) ys xs.

lemma app_nil: forall (ys:'a list), [] ++ ys = ys by [].
lemma app_cons: forall (x:'a) xs ys, (x::xs) ++ ys = x::(xs ++ ys) by [].

lemma app_nil_right: forall (xs:'a list), xs ++ [] = xs.
proof.
intros xs;elimT list_ind xs;trivial.
save.

lemma app_assoc : forall(xs ys zs:'a list),
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
proof.
intros xs;elimT list_ind xs;trivial.
save.

lemma length_app: forall (xs ys:'a list), 
  length (xs ++ ys) = length xs + length ys.
proof.
intros xs;elimT list_ind xs;trivial.
save.

lemma length_app_comm: forall (xs ys:'a list), 
  length (xs ++ ys) =  length (ys ++ xs)
by [].

lemma mem_app: forall (y:'a) xs ys,
  (mem y xs \/ mem y ys) = mem y (xs ++ ys).
proof.
intros y xs ys;elimT list_ind xs;trivial.
save.

lemma mem_app_comm: forall (y:'a) xs ys,
  mem y (xs ++ ys) = mem y (ys ++ xs)
by [].

(* Liftings from a' Pred to ('a list) Pred *)
pred all (p :'a cPred,xs) = forall x, mem x xs => p x.
pred any (p:'a cPred,xs) = exists x, mem x xs /\ p x.

lemma all_empty: forall (p:'a cPred),  all p [] by [].
lemma any_empty: forall (p:'a cPred), !any p [] by [].

lemma all_app: forall (p:'a cPred) xs ys,
  all p (xs ++ ys) = (all p xs /\ all p ys)
by [].

lemma any_app: forall (p:'a cPred) xs ys,
  any p (xs ++ ys) = (any p xs \/ any p ys)
by [].

(* forallb *)
op (* local *) f_forallb (p:'a -> bool, x, r): bool = 
  (p x) /\ r.
op forallb(p:'a -> bool, xs): bool = 
  fold_right (f_forallb p) true xs.

op (* local *) f_existsb (p:'a -> bool, x, r): bool = 
  (p x) \/ r.
op existsb(p:'a -> bool, xs): bool = 
  fold_right (f_existsb p) false xs.

lemma eq_forallb_all: forall (p:'a -> bool) xs,
  all p xs <=> forallb p xs.
proof.
 intros p xs;elimT list_ind xs.
  trivial.
  intros y ys H.
  cut H1: ((p y /\ all p ys) <=> (p y /\ forallb p ys)).
  trivial.
  split;trivial.
save.

lemma eq_existsb_any: forall (p:'a -> bool) xs,
 any p xs <=> existsb p xs.
proof.
 intros p xs;elimT list_ind xs.
  trivial.
  intros y ys H.
  split.
   simplify any;intros H1;elim H1;clear H1.
   intros x HmemP;elim HmemP;clear HmemP;intros Hmem Hp.
   cut Hor: (x = y \/ mem x ys);trivial.

   trivial. 
save.

(* filter *)
op (* local *) f_filter(p:'a cPred, x, r): 'a list = 
  if (p x) then x::r else r.
op filter(p:'a cPred): 'a list -> 'a list =
  fold_right (f_filter p) [].

lemma filter_nil: forall (p:'a cPred),
  filter p [] = []
by [].
lemma filter_cons: forall (p:'a cPred) x xs,
  filter p (x::xs) = let rest = filter p xs in
                     if p x then x::rest else rest.
proof.
 intros p x xs.
 simplify filter.
 cut Heq : 
  (fold_right (f_filter p) __nil (x :: xs) = 
   (f_filter p x (fold_right (f_filter p) __nil xs))).
  trivial.
  trivial.
save.

lemma filter_mem: forall (x:'a) xs p,
  mem x (filter p xs) = (mem x xs /\ p x).
proof.
 intros x xs P.
 elimT list_ind xs.
 trivial.
 intros y ys H.
 case (P y); intros Hp.
 cut Heq: (filter P (y::ys) = y :: filter P ys).
  trivial. 
 rewrite Heq;trivial.
 cut Heq: (filter P (y::ys) = filter P ys).
  trivial.
 rewrite Heq.
 trivial.
save.

lemma filter_app: forall (xs ys:'a list) p,
  filter p (xs ++ ys) = (filter p xs) ++ (filter p ys).
proof.
 intros xs.
 elimT list_ind xs;trivial.
save.

lemma filter_length: forall (xs:'a list) p,
  length (filter p xs) <= length xs.
proof.
 intros xs.
 elimT list_ind xs;trivial.
save.

lemma filter_all: forall (xs:'a list) p,
  all p (filter p xs)
by [].

lemma filter_imp: forall (p q:'a cPred) xs,
  (forall x, p x => q x) => 
   forall x, mem x (filter p xs) => mem x (filter q xs)
by [].

(* map *)
op (* local *) f_map(f:'a -> 'b, x, xs): 'b list = (f x)::xs.
op map(f:'a -> 'b): 'a list -> 'b list = fold_right (f_map f) [].

lemma map_nil: forall (f: 'a -> 'b), map f [] = [] by [].
lemma map_cons: forall (f: 'a -> 'b) x xs, 
  map f (x::xs) = (f x)::(map f xs)
by [].

pred (* local *) P_map_in(f:'a -> 'b, xs) = 
  forall x, mem x xs => mem (f x) (map f xs).
lemma map_in: forall (x:'a) xs (f:'a -> 'b), 
  mem x xs => mem (f x) (map f xs).
proof.
 intros x xs f.
 elimT list_ind xs;trivial.
save.


lemma map_o: forall xs (f:'a -> 'b) (g:'b -> 'c) (h:'a -> 'c),
  (forall x, g (f x) = h x) => 
  map g (map f xs) = map h xs.
proof.
 intros xs f g h compose.
 elimT list_ind xs;trivial.
save.

lemma map_length: forall (xs:'a list, f:'a -> 'b), 
  length xs = length (map f xs).
proof.
 intros xs f.
 elimT list_ind xs;trivial.
save.

lemma map_app : forall xs ys (f:'a -> 'b),
  map f (xs ++ ys) = map f xs ++ map f ys.
proof.
 intros xs ys f.
 elimT list_ind xs;trivial.
save.

lemma map_ext: forall xs (f g:'a -> 'b),
  (forall x, f x = g x) =>
  map f xs = map g xs.
proof.
 intros xs f g H.
 elimT list_ind xs.
 trivial.
 intros x' xs' IH.
 rewrite (map_cons<:'b, 'a> f x' xs').
 rewrite (map_cons<:'b, 'a> g x' xs').
 rewrite IH.
 rewrite (H x').
 trivial.
save.

op (*local*) f_nth (x, r:'a -> int -> 'a, y, n): 'a =
  if n = 0 then x else (r y (n - 1)). 
op (*local*) e_nth (y, n:int): 'a = y. 
op nth (xs:'a list): 'a -> int -> 'a = fold_right f_nth e_nth xs.

lemma nth_in_or_dv_aux: forall(xs:'a list) dv n, 0 <= n =>
  mem (nth xs dv n) xs \/ nth xs dv n = dv.
proof.
 intros xs.
 elimT list_ind xs.
  trivial.
  
  clear xs;intros x xs H dv n H1.
  case (n = 0);intros Hn.
    rewrite Hn;trivial.
    
  elim (H dv (n-1) _).
   trivial.
   trivial.
   trivial.
save.
