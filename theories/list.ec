require import Fun.
require import int.
prover "Alt-Ergo" "Vampire" "Z3" "CVC3".
(* constructors *)
import why3 "list" "List"
   op "Nil" as "__nil";
   op "Cons" as "::".



(* partial destructors *)
op hd : 'a list -> 'a.
op tl : 'a list -> 'a list.

op fold_right : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b.

axiom hd_def : forall (x : 'a, xs : 'a list), hd(x::xs) = x.

axiom tl_def : forall (x : 'a, xs : 'a list), tl(x::xs) = xs.

(*list induction and recursion*)
axiom list_ind : forall(P:('a list) Pred),
(P([])) =>
(forall (x :'a, xs : 'a list), P(xs) => P (x::xs)) =>
(forall(ys:'a list), P(ys)).

axiom fold_right_def1 : forall (e : 'b, f : 'a -> 'b -> 'b),
 fold_right f  e [] = e.

axiom fold_right_def2 : forall (e : 'b, f : 'a -> 'b -> 'b, x : 'a, xs : 'a list),
 fold_right f e (x::xs) = f x (fold_right f e xs).

(********** No more axioms **********)

(* basic facts about lists *)
lemma nil_cons : forall (x : 'a ,xs : 'a list), x::xs <> [].

lemma destruct_list : forall (xs : 'a list),
  xs = [] || (exists (y : 'a), exists (ys : 'a list), xs =
  y::ys).

lemma hd_tl_decomp : forall (xs : 'a list), xs <> [] =>
 hd(xs)::tl(xs) = xs.

(* membership test *)

(* local *) op f_mem(x : 'a, y : 'a, b : bool)  : bool = x = y || b.
op mem (x : 'a) :  'a list -> bool = fold_right (f_mem x) false.

lemma mem_eq : forall (x : 'a, xs : 'a list), mem x (x::xs).
lemma mem_cons : forall (x y: 'a) (xs : 'a list), mem y xs => mem y (x::xs).
lemma mem_not_nil : forall (y: 'a, xs : 'a list), mem y xs => xs <> [].
lemma mem_hd : forall (xs : 'a list), xs <> [] => mem (hd xs) xs.
lemma not_mem_empty : forall (xs : 'a list), (forall(x :'a), !mem x xs) => xs = [].

(* length *)

(* local *) op f_length(x : 'a, b : int)  : int = 1 + b.
op length (xs : 'a list) : int = fold_right f_length 0 xs.

lemma length_def1 : length<:'a> [] = 0.
lemma length_def2 : forall (x : 'a, xs : 'a list), 
 length (x::xs) = 1 + length(xs).



(* local *) pred P_length_non_neg(xs : 'a list)  =
 0 <= length(xs).

(* local *) lemma length_non_neg_aux: forall (xs : 'a list), P_length_non_neg(xs)
proof.
 intros xs.
 apply list_ind<:'a>((P_length_non_neg),_,_,xs);trivial.
save.

lemma length_non_neg: forall (xs : 'a list), 0 <= length(xs).

axiom length_z_nil : forall(xs : 'a list), length(xs) = 0 => xs = [].

(* append *)

op [++](xs : 'a list, ys : 'a list) : 'a list = (fold_right ([::]) ys ) xs.

lemma app_def1 : forall (ys : 'a list), []++ys = ys.
lemma app_def2 : forall (x : 'a) (xs ys : 'a list), (x::xs)++ys = x::(xs++ys).

(* facts about append *)

(* local *) op P_app_nil_right(xs : 'a list) : bool = xs ++ [] = xs.

(* local *) lemma app_nil_right_aux : forall (xs :'a list), P_app_nil_right(xs)
proof.
 intros xs.
 apply list_ind<:'a>(P_app_nil_right,_,_,xs);trivial.
save.

lemma app_nil_right : forall (xs :'a list), xs ++ [] = xs.

(* local *) pred P_app_assoc(xs : 'a list) =  forall(ys zs : 'a list),
    (xs++ys)++zs = xs++(ys++zs).

(* local *) lemma app_assoc_aux : forall(xs : 'a list), 
P_app_assoc xs
proof.
intros xs.
apply list_ind<:'a>(P_app_assoc,_,_,xs);trivial.
save.

lemma app_assoc : forall (xs ys zs : 'a list), (xs++ys)++zs = xs++(ys++zs).

(* local *) pred P_length_app_aux(xs : 'a list) = forall(ys : 'a list), 
 length(xs++ys) = length(xs) + length(ys).

(* local *) lemma length_app_aux : forall (xs : 'a list), P_length_app_aux(xs)
proof.
intros xs.
apply list_ind<:'a>((P_length_app_aux),_,_,xs);trivial.
save.

lemma length_app : forall (xs ys : 'a list), 
 length(xs++ys) = length(xs) + length(ys).

lemma length_app_comm : forall (xs ys : 'a list), 
 length(xs++ys) =  length(ys++xs).


(* local *) pred P_mem_app (xs : 'a list) = forall(ys : 'a list, y :'a), 
(mem y xs  || mem y ys) =  mem y (xs++ys).

(* local *) lemma mem_app_aux : forall (xs : 'a list), P_mem_app xs
proof.
intros xs.
apply list_ind<:'a>((P_mem_app),_,_,xs);trivial.
save.

axiom mem_app : forall (xs ys : 'a list) (y :'a), 
   (mem y xs  || mem y ys)  =  mem y (xs++ys).
 
lemma mem_app_comm : forall (xs ys : 'a list) (y :'a),
 mem y (xs++ys) = mem y (ys++xs).

(* two liftings from a' pred  to ('a list) pred *)

pred all (p : 'a Pred,xs : 'a list) =
 forall (x : 'a), mem x xs => p x.

pred any (p : 'a Pred,xs : 'a list) =
 exists (x : 'a), mem x xs && p x.

lemma all_empty : forall (p : 'a Pred), all p [].
lemma any_empty : forall (p : 'a Pred), !any p [].

lemma all_app : forall (p : 'a Pred) (xs ys : 'a list),
all p (xs++ys) = (all p xs && all p ys).

lemma any_app : forall (p : 'a Pred) (xs ys : 'a list),
any p (xs++ys) = (any p xs || any p ys).

(* forallb *)

(* local *) op f_forallb (p : 'a -> bool, x : 'a, r : bool) : bool = 
(p x) && r.

op forallb(p : 'a -> bool, xs : 'a list) : bool = 
 fold_right (f_forallb p) true xs.

(* local *) op f_existsb (p : 'a -> bool, x : 'a, r : bool) : bool = 
(p x) || r.

op existsb(p : 'a -> bool, xs : 'a list) : bool = 
 fold_right (f_existsb p) false xs.

axiom eq_forallb_all : forall (p : 'a -> bool) (xs : 'a list),
all p xs <=> forallb p xs.


axiom eq_existsb_any : forall (p : 'a -> bool) (xs : 'a list),
any p xs <=> existsb p xs.

(* filter *)

(* local *)  op f_filter(p : 'a Pred, x : 'a, r : 'a list) : 'a list = 
 if (p x) then x::r else r.

op filter(p : 'a Pred) : 'a list -> 'a list = fold_right (f_filter p) [].

lemma filter_def1 : forall (p : 'a Pred),
  filter p [] = [].

lemma filter_def2 : forall (p : 'a Pred, x : 'a, xs : 'a list),
  filter p (x::xs) = let rest = filter p xs in
                     if p x then x::rest else rest.

(* local *) pred P_filter_mem (xs : 'a list) = forall (p : 'a Pred, x : 'a),
mem x (filter p xs) = (mem x xs && p x).

(* local *) lemma filter_mem_aux : 
forall (xs : 'a list), P_filter_mem xs
proof.
intros xs.
apply list_ind<:'a>(P_filter_mem,_,_,xs);trivial.
save.

axiom filter_mem : 
forall (xs : 'a list) (p : 'a Pred) (x : 'a), 
mem x (filter p xs) = (mem x xs && p x).

(* local *) pred P_filter_app(xs : 'a list) = 
 forall (ys : 'a list, p : 'a Pred),
filter p (xs++ys) = (filter p xs)++(filter p ys).

(* local *) lemma filter_app_aux : forall (xs : 'a list),
 P_filter_app xs
proof.
intros xs.
apply list_ind<:'a>(P_filter_app,_,_,xs);trivial.
save.

lemma filter_app : forall (xs ys : 'a list) (p : 'a Pred),
filter p (xs++ys) = (filter p xs)++(filter p ys).

(* local *) pred P_filter_length(xs : 'a list) = forall(p : 'a Pred),
length (filter p xs) <= length xs.

(* local *) lemma filter_length_aux : forall(xs : 'a list), P_filter_length xs
proof.
intros xs.
apply list_ind<:'a>(P_filter_length,_,_,xs);trivial.
save.

lemma filter_length : forall(xs : 'a list, p : 'a Pred),
length (filter p xs) <= length xs.

lemma filter_all : forall(xs : 'a list, p : 'a Pred), 
all p (filter p xs).

lemma filter_imp : forall(xs : 'a list) (p q : 'a Pred),
(forall (x : 'a), p x => q x) => 
 forall (x : 'a), mem x (filter p xs) => mem x (filter q xs).


(* list map *)
(* local *) op f_map(f : 'a -> 'b, x : 'a , xs : 'b list) : 'b list = f x :: xs.

op map(f :'a -> 'b) : 'a list -> 'b list = fold_right (f_map f) [].

lemma map_def1 : forall(f : 'a -> 'b),map f [] = [].
lemma map_def2 : forall(f : 'a -> 'b, x : 'a, xs : 'a list ), 
    map f (x::xs) = (f x)::(map f xs).

(* local *)  pred P_map_in(f : 'a -> 'b,xs : 'a list) = 
 forall(x : 'a), mem x xs => mem (f x) (map f xs).

(* local *) lemma map_in_aux : forall (xs : 'a list,f : 'a -> 'b), 
   (P_map_in f) xs 
proof.
intros xs f.
apply list_ind<:'a>((P_map_in f),_,_,xs);trivial.
save.

axiom map_in : forall (xs : 'a list) (x : 'a) (f : 'a -> 'b), mem x xs =>
 mem (f x) (map f xs).

(* local *)  pred P_map_o (f : 'a -> 'b, g : 'b -> 'c, h : 'a -> 'c, 
 xs : 'a list) = map g (map f xs) = map h xs.

(* local *)  lemma map_o_aux : forall (xs : 'a list,f : 'a -> 'b, 
 g : 'b -> 'c, h : 'a -> 'c),
(forall (x : 'a), g (f x) = h x) => P_map_o f g h xs
proof.
intros xs f g h H.
apply list_ind<:'a>((P_map_o f g h),_,_,xs);trivial.
save.

lemma map_o_aux2 : forall (xs : 'a list,f : 'a -> 'b, g : 'b -> 'c, h : 'a -> 'c), 
P_map_o f g h xs =>
map g (map f xs) = map h xs.

lemma map_o : forall (xs : 'a list,f : 'a -> 'b, g : 'b -> 'c, h : 'a -> 'c), 
(forall (x : 'a), g (f x) = h x) => map g (map f xs) = map h xs
proof.
intros xs f g h H.
apply map_o_aux2<:'a,'b,'c>(xs,f,g,h,_).
apply map_o_aux<:'a,'b,'c>(xs,f,g,h,_).
trivial.
save.

pred P_map_length(f : 'a -> 'b, xs : 'a list) = 
        length xs = length (map f xs).

lemma map_length_aux : forall (xs : 'a list, f : 'a -> 'b), 
  P_map_length f xs
proof.
intros xs f.
apply list_ind<:'a>((P_map_length f),_,_,xs);trivial.
save.

lemma map_length : forall (xs : 'a list, f : 'a -> 'b), 
 length xs = length (map f xs).

pred P_map_app(f : 'a -> 'b,xs : 'a list) = 
forall (ys : 'a list), map f (xs ++ ys) = map f xs ++ map f ys.

lemma map_app_aux : forall (xs : 'a list, f : 'a -> 'b),
P_map_app f xs
proof.
intros xs f.
apply list_ind<:'a>((P_map_app f),_,_,xs);trivial.
save.

lemma map_app : forall (xs ys: 'a list) (f : 'a -> 'b),
map f (xs ++ ys) = map f xs ++ map f ys.

pred P_map_ext(f,g : 'a -> 'b,xs: 'a list) = map f xs = map g xs.

lemma map_ext_aux : forall (xs : 'a list, f : 'a -> 'b, g : 'a -> 'b),
(forall (x : 'a), f x = g x)  => P_map_ext f g xs
proof.
intros xs f g H.
apply list_ind<:'a>((P_map_ext f g),_,_,xs);trivial.
save.

lemma map_ext : forall (xs : 'a list, f: 'a -> 'b,g : 'a -> 'b),
(forall (x : 'a), f x = g x) => map f xs = map g xs.


op f_nth (x : 'a, r : ('a -> int -> 'a), y : 'a, n : int) : 'a =
if n = 0 then x else (r y (n - 1)).
 
op e_nth (y : 'a, n : int) : 'a = y.
 
op nth (xs : 'a list) : 'a -> int -> 'a = fold_right f_nth e_nth xs.

lemma nth_in_or_dv : forall(xs : 'a list, dv : 'a, n : int),
  mem (nth xs dv n) xs || nth xs dv n = dv.
