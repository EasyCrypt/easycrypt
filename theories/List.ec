require import Int.
require import Fun.

(** Type Definition is imported from Why3 *)
import why3 "list" "List"
   op "Nil" as "__nil";
   op "Cons" as "::".

op cons(x,xs): 'a list = x::xs.

(** Fold *)
op fold_right: ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b.
axiom fold_right_nil : forall (e:'b) (f:'a -> 'b -> 'b),
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
lemma nil_cons: forall (x:'a) xs, x::xs <> [].

lemma destruct_list: forall (xs:'a list),
  xs = [] \/ (exists (y:'a) ys, xs = y::ys).

lemma hd_tl_decomp: forall (xs:'a list),
  xs <> [] => (hd xs)::(tl xs) = xs.

(** Derived Operators *)
(* mem: membership test *)
op (* local *) f_mem(x:'a,y,b): bool = x = y \/ b.
op mem (x:'a): 'a list -> bool = fold_right (f_mem x) false.

lemma mem_eq: forall (x:'a) xs, mem x (x::xs).
lemma mem_cons: forall (x y:'a) xs, mem y xs => mem y (x::xs).
lemma mem_not_nil: forall (y:'a) xs, mem y xs => xs <> [].
lemma mem_hd: forall (xs:'a list), xs <> [] => mem (hd xs) xs.
lemma not_mem_empty: forall (xs:'a list), xs = [] <=> (forall x, !mem x xs).

(* length *)
op (* local *) f_length(x:'a, b): int = 1 + b.
op length (xs:'a list): int = fold_right f_length 0 xs.

lemma length_nil: length<:'a> [] = 0.
lemma length_cons: forall (x:'a) xs, 
  length (x::xs) = 1 + length xs.

pred (* local *) P_length_non_neg(xs:'a list) =
  0 <= length xs.

lemma length_non_neg: forall (xs:'a list), 0 <= length xs
proof.
 intros xs;cut IH: (P_length_non_neg xs).
 apply list_ind<:'a>(P_length_non_neg,_,_,xs);trivial.
 trivial.
save.

pred (* local *) P_length_z_nil(xs:'a list) = length xs = 0 => xs = [].
lemma length_z_nil : forall(xs:'a list), length xs = 0 => xs = []
proof.
intros xs;cut IH: (P_length_z_nil xs).
apply list_ind<:'a>(P_length_z_nil,_,_,xs);trivial.
trivial.
save.

(* append *)
op [++](xs ys:'a list): 'a list = fold_right [::] ys xs.

lemma app_nil: forall (ys:'a list), [] ++ ys = ys.
lemma app_cons: forall (x:'a) xs ys, (x::xs) ++ ys = x::(xs ++ ys).

op (* local *) P_app_nil_right(xs:'a list): bool = xs ++ [] = xs.
lemma app_nil_right: forall (xs:'a list), xs ++ [] = xs
proof.
intros xs;cut IH: (P_app_nil_right xs).
apply list_ind<:'a>(P_app_nil_right,_,_,xs);trivial.
trivial.
save.

pred (* local *) P_app_assoc(xs:'a list) = forall (ys zs:'a list),
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
lemma app_assoc : forall(xs ys zs:'a list),
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
proof.
intros xs;cut IH: (P_app_assoc xs).
apply list_ind<:'a>(P_app_assoc,_,_,xs);trivial.
trivial.
save.

pred (* local *) P_length_app_aux(xs:'a list) = forall(ys:'a list), 
  length (xs ++ ys) = length xs + length ys.
lemma length_app: forall (xs ys:'a list), 
  length (xs ++ ys) = length xs + length ys
proof.
intros xs;cut IH: (P_length_app_aux xs).
apply list_ind<:'a>(P_length_app_aux,_,_,xs);trivial.
trivial.
save.

lemma length_app_comm: forall (xs ys:'a list), 
  length (xs ++ ys) =  length (ys ++ xs).

pred (* local *) P_mem_app (xs:'a list) = forall (y:'a) ys,
  (mem y xs \/ mem y ys) = mem y (xs ++ ys).
lemma mem_app: forall (y:'a) xs ys,
  (mem y xs \/ mem y ys) = mem y (xs ++ ys)
proof.
intros y xs ys;cut H: (P_mem_app xs).
apply list_ind<:'a>(P_mem_app,_,_,xs);trivial.
trivial.
save.

lemma mem_app_comm: forall (y:'a) xs ys,
  mem y (xs ++ ys) = mem y (ys ++ xs).

(* Liftings from a' Pred to ('a list) Pred *)
pred all (p :'a cPred,xs) = forall x, mem x xs => p x.
pred any (p:'a cPred,xs) = exists x, mem x xs /\ p x.

lemma all_empty: forall (p:'a cPred),  all p [].
lemma any_empty: forall (p:'a cPred), !any p [].

lemma all_app: forall (p:'a cPred) xs ys,
  all p (xs ++ ys) = (all p xs /\ all p ys).

lemma any_app: forall (p:'a cPred) xs ys,
  any p (xs ++ ys) = (any p xs \/ any p ys).

(* forallb *)
op (* local *) f_forallb (p:'a -> bool, x, r): bool = 
  (p x) /\ r.
op forallb(p:'a -> bool, xs): bool = 
  fold_right (f_forallb p) true xs.

op (* local *) f_existsb (p:'a -> bool, x, r): bool = 
  (p x) \/ r.
op existsb(p:'a -> bool, xs): bool = 
  fold_right (f_existsb p) false xs.

pred (* local *) P_eq_forallb_all(p:'a -> bool, xs) =
  all p xs <=> forallb p xs.
lemma eq_forallb_all: forall (p:'a -> bool) xs,
  all p xs <=> forallb p xs
proof.
intros p xs;cut IH: (P_eq_forallb_all p xs).
apply list_ind<:'a>((P_eq_forallb_all p),_,_,xs);trivial.
trivial.
save.

pred (* local *) P_eq_existsb_any(p:'a -> bool, xs) =
  any p xs <=> existsb p xs.
lemma eq_existsb_any: forall (p:'a -> bool) xs,
  any p xs <=> existsb p xs
proof.
intros p xs;cut IH: (P_eq_existsb_any p xs).
apply list_ind<:'a>((P_eq_existsb_any p),_,_,xs);trivial.
trivial.
save.

(* filter *)
op (* local *) f_filter(p:'a cPred, x, r): 'a list = 
  if (p x) then x::r else r.
op filter(p:'a cPred): 'a list -> 'a list =
  fold_right (f_filter p) [].

lemma filter_nil: forall (p:'a cPred),
  filter p [] = [].
lemma filter_cons: forall (p:'a cPred) x xs,
  filter p (x::xs) = let rest = filter p xs in
                     if p x then x::rest else rest.

pred (* local *) P_filter_mem (xs:'a list) = forall (x:'a) p,
  mem x (filter p xs) = (mem x xs /\ p x).
lemma filter_mem: forall (x:'a) xs p,
  mem x (filter p xs) = (mem x xs /\ p x)
proof.
intros x xs ys;cut IH: (P_filter_mem xs).
apply list_ind<:'a>(P_filter_mem,_,_,xs);trivial.
trivial.
save.

pred (* local *) P_filter_app (xs:'a list) = forall (ys:'a list) p,
  filter p (xs ++ ys) = (filter p xs) ++ (filter p ys).
lemma filter_app: forall (xs ys:'a list) p,
  filter p (xs ++ ys) = (filter p xs) ++ (filter p ys)
proof.
intros xs;cut IH: (P_filter_app xs).
apply list_ind<:'a>(P_filter_app,_,_,xs);trivial.
trivial.
save.

pred (* local *) P_filter_length(xs:'a list) = forall p,
  length (filter p xs) <= length xs.
lemma filter_length: forall (xs:'a list) p,
  length (filter p xs) <= length xs
proof.
intros xs;cut IH: (P_filter_length xs).
apply list_ind<:'a>(P_filter_length,_,_,xs);trivial.
trivial.
save.

lemma filter_all: forall (xs:'a list) p,
  all p (filter p xs).
lemma filter_imp: forall (p q:'a cPred) xs,
  (forall x, p x => q x) => 
   forall x, mem x (filter p xs) => mem x (filter q xs).

(* map *)
op (* local *) f_map(f:'a -> 'b, x, xs): 'b list = (f x)::xs.
op map(f:'a -> 'b): 'a list -> 'b list = fold_right (f_map f) [].

lemma map_nil: forall (f: 'a -> 'b), map f [] = [].
lemma map_cons: forall (f: 'a -> 'b) x xs, 
  map f (x::xs) = (f x)::(map f xs).

pred (* local *) P_map_in(f:'a -> 'b, xs) = 
  forall x, mem x xs => mem (f x) (map f xs).
lemma map_in: forall (x:'a) xs (f:'a -> 'b), 
  mem x xs => mem (f x) (map f xs)
proof.
intros x xs f;cut H: (P_map_in f xs).
apply list_ind<:'a>((P_map_in f),_,_,xs);trivial.
trivial.
save.

pred (* local *) P_map_o(f:'a -> 'b, g:'b -> 'c, h, xs) =
  map g (map f xs) = map h xs.

lemma map_o: forall xs (f:'a -> 'b) (g:'b -> 'c) (h:'a -> 'c),
  (forall x, g (f x) = h x) => 
  map g (map f xs) = map h xs
proof.
intros xs f g h compose;cut H0: (P_map_o f g h xs).
apply list_ind<:'a>((P_map_o f g h),_,_,xs);trivial.
trivial.
save.

pred (* local *) P_map_length(f:'a -> 'b, xs:'a list) = 
  length xs = length (map f xs).
lemma map_length: forall (xs:'a list, f:'a -> 'b), 
  length xs = length (map f xs)
proof.
intros xs f;cut H: (P_map_length f xs).
apply list_ind<:'a>((P_map_length f),_,_,xs);trivial.
trivial.
save.

pred (* local *) P_map_app(f:'a -> 'b, xs) = forall ys,
  map f (xs ++ ys) = map f xs ++ map f ys.
lemma map_app : forall xs ys (f:'a -> 'b),
  map f (xs ++ ys) = map f xs ++ map f ys
proof.
intros xs ys f;cut IH: (P_map_app f xs).
apply list_ind<:'a>((P_map_app f),_,_,xs);trivial.
trivial.
save.

pred (* local *) P_map_ext(f:'a -> 'b, g, xs) =
  map f xs = map g xs.
lemma map_ext: forall xs (f g:'a -> 'b),
  (forall x, f x = g x) =>
  map f xs = map g xs
proof.
intros xs f g H;cut IH: (P_map_ext f g xs).
apply list_ind<:'a>((P_map_ext f g),_,_,xs);trivial.
trivial.
save.

op (*local*) f_nth (x, r:'a -> int -> 'a, y, n): 'a =
  if n = 0 then x else (r y (n - 1)). 
op (*local*) e_nth (y, n:int): 'a = y. 
op nth (xs:'a list): 'a -> int -> 'a = fold_right f_nth e_nth xs.

pred (*local*) P_nth_in_or_dv(xs:'a list) = forall(dv:'a, n:int),
  mem (nth xs dv n) xs \/ (nth xs dv n = dv).

lemma nth_in_or_dv_aux: forall(xs:'a list) dv n,
  mem (nth xs dv n) xs \/ nth xs dv n = dv
proof.
intros xs;cut IH: (P_nth_in_or_dv xs).
apply list_ind<:'a>(P_nth_in_or_dv,_,_,xs);trivial.
trivial.
save.
