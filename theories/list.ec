require import Fun.
require import int.

(* constructors *)
import why3 "list" "List"
   op "Nil" as "__nil";
   op "Cons" as "::".

lemma nil_cons : forall (x : 'a ,xs : 'a list), x::xs <> [].

lemma destruct_list : forall (xs : 'a list),
  xs = [] || (exists (y : 'a), exists (ys : 'a list), xs =
  y::ys).


(* partial destructors *)
op hd : 'a list -> 'a.
op tl : 'a list -> 'a list.

axiom hd_def : forall (x : 'a, xs : 'a list), hd(x::xs) = x.
axiom tl_def : forall (x : 'a, xs : 'a list), tl(x::xs) = xs.


lemma hd_tl_decomp : forall (xs : 'a list), xs <> [] =>
 hd(xs)::tl(xs) = xs.

(* list induction and recursion*)

axiom list_ind : forall(P:('a list) Pred),
(P([])) =>
(forall (x :'a, xs : 'a list), P(xs) => P (x::xs)) =>
(forall(ys:'a list), P(ys)).


op foldr : 'b -> ('a -> 'b -> 'b) -> 'a list -> 'b.

axiom foldr_def1 : forall (e : 'b, f : 'a -> 'b -> 'b),
 foldr e f [] = e. 

axiom foldr_def2 : forall (e : 'b, f : 'a -> 'b -> 'b, x : 'a, xs : 'a list),
 foldr e f (x::xs) = f x (foldr e f xs). 



(* membership test *)
cnst e_elem : bool = false.
op f_elem(x : 'a, y : 'a, b : bool)  : bool = x = y || b.
op elem (x : 'a) :  'a list -> bool = foldr e_elem (f_elem x).

lemma elem_eq : forall (x : 'a, xs : 'a list), elem x (x::xs).
lemma elem_cons : forall (x, y: 'a, xs : 'a list), elem y xs => elem y (x::xs).
(* lemma elem_singleton : forall (x, y : 'a), elem(x,singleton(y)) => x = y. *)
lemma elem_not_nil : forall (y: 'a, xs : 'a list), elem y xs => xs <> [].
lemma elem_hd : forall (xs : 'a list), xs <> [] => elem (hd xs) xs.
lemma not_elem_empty : forall (xs : 'a list), (forall(x :'a), !elem x xs) => xs = []. 

(* length *)

op f_length(x : 'a, b : int)  : int = 1 + b.
op length(xs : 'a list) : int = foldr 0 f_length xs.

axiom length_def1 : length<:'a>([]) = 0.
axiom length_def2 : forall (x : 'a, xs : 'a list), 
 length (x::xs) = 1 + length(xs).

pred P_length_non_neg(xs : 'a list)  =
 0 <= length(xs).

lemma length_non_neg_aux: forall (xs : 'a list), P_length_non_neg(xs)
proof.
 intros xs.
 apply list_ind<:'a>((P_length_non_neg),_,_,xs);trivial.
save.

lemma length_non_neg: forall (xs : 'a list), 0 <= length(xs).

lemma length_z_nil : forall(xs : 'a list), length(xs) = 0 => xs = [].

(* append *)

op [++](xs : 'a list, ys : 'a list) : 'a list = (foldr ys ([::])) xs.

lemma app_def1 : forall (ys : 'a list), []++ys = ys.
lemma app_def2 : forall (x : 'a, xs, ys : 'a list), (x::xs)++ys = x::(xs++ys).

(* facts about append *)

op P_app_nil_right(xs : 'a list) : bool = xs ++ [] = xs.

lemma app_nil_right_aux : forall (xs :'a list), P_app_nil_right(xs)
proof.
 intros xs.
 apply list_ind<:'a>(P_app_nil_right,_,_,xs);trivial.
save.

lemma app_nil_right : forall (xs :'a list), xs ++ [] = xs.

pred P_app_assoc(xs : 'a list) =  forall(ys,zs : 'a list),
    (xs++ys)++zs = xs++(ys++zs).

lemma app_assoc_aux : forall(xs : 'a list), 
P_app_assoc xs
proof.
intros xs.
apply list_ind<:'a>(P_app_assoc,_,_,xs);trivial.
save.

lemma app_assoc : forall (xs, ys, zs : 'a list), (xs++ys)++zs = xs++(ys++zs).

pred P_length_app_aux(xs : 'a list) = forall(ys : 'a list), 
 length(xs++ys) = length(xs) + length(ys).

lemma length_app_aux : forall (xs : 'a list), P_length_app_aux(xs)
proof.
intros xs.
apply list_ind<:'a>((P_length_app_aux),_,_,xs);trivial.
save.

lemma length_app : forall (xs, ys : 'a list), 
 length(xs++ys) = length(xs) + length(ys).

lemma length_app_comm : forall (xs, ys : 'a list), 
 length(xs++ys) =  length(ys++xs).


pred P_elem_app (xs : 'a list) = forall(ys : 'a list, y :'a), 
(elem y xs  || elem y ys) =  elem y (xs++ys).

lemma elem_app_aux : forall (xs : 'a list), P_elem_app xs
proof.
intros xs.
apply list_ind<:'a>((P_elem_app),_,_,xs);trivial.
save.

lemma elem_app : forall (xs,ys : 'a list,y :'a), 
   (elem y xs  || elem y ys)  =  elem y (xs++ys).
 
lemma elem_app_comm_aux : forall (xs,ys : 'a list,y :'a),
 elem y (xs++ys) = elem y (ys++xs).

(* two liftings from a' pred  to ('a list) pred *)

pred all (p : 'a Pred,xs : 'a list) =
 forall (x : 'a), elem x xs => p x.

pred any (p : 'a Pred,xs : 'a list) =
 exists (x : 'a), elem x xs && p x.

lemma all_empty : forall (p : 'a Pred), all p [].
lemma any_empty : forall (p : 'a Pred), !any p [].

lemma all_app : forall (p : 'a Pred,xs,ys : 'a list),
all p (xs++ys) = (all p xs && all p ys).

lemma any_app : forall (p : 'a Pred,xs,ys : 'a list),
any p (xs++ys) = (any p xs || any p ys).

(* filter *)

op f_filter(p : 'a Pred, x : 'a, r : 'a list) : 'a list = if (p x) then x::r else r.

op filter(p : 'a Pred) : 'a list -> 'a list = foldr [] (f_filter p).

lemma filter_def1 : forall (p : 'a Pred),
  filter p [] = [].

lemma filter_def2 : forall (p : 'a Pred, x : 'a, xs : 'a list),
  filter p (x::xs) = let rest = filter p xs in
                     if p x then x::rest else rest.

pred P_filter_elem (xs : 'a list) = forall (p : 'a Pred, x : 'a),
elem x (filter p xs) = (elem x xs && p x).

lemma filter_elem_aux : 
forall (xs : 'a list), P_filter_elem xs
proof.
intros xs.
apply list_ind<:'a>(P_filter_elem,_,_,xs);trivial.
save.

lemma filter_elem : 
forall (xs : 'a list, p : 'a Pred, x : 'a), 
elem x (filter p xs) = (elem x xs && p x).

pred P_filter_app(xs : 'a list) = forall (ys : 'a list, p : 'a Pred),
filter p (xs++ys) = (filter p xs)++(filter p ys).

lemma filter_app_aux : forall (xs : 'a list),
 P_filter_app xs
proof.
intros xs.
apply list_ind<:'a>(P_filter_app,_,_,xs);trivial.
save.

lemma filter_app : forall (xs, ys : 'a list, p : 'a Pred),
filter p (xs++ys) = (filter p xs)++(filter p ys).

pred P_filter_length(xs : 'a list) = forall(p : 'a Pred),
length (filter p xs) <= length xs.

lemma filter_length_aux : forall(xs : 'a list), P_filter_length xs
proof.
intros xs.
apply list_ind<:'a>(P_filter_length,_,_,xs);trivial.
save.

lemma filter_length : forall(xs : 'a list, p : 'a Pred),
length (filter p xs) <= length xs.

lemma filter_all : forall(xs : 'a list, p : 'a Pred), 
all p (filter p xs).

lemma filter_imp : forall(xs : 'a list, p q : 'a Pred),
(forall (x : 'a), p x => q x) => 
 forall (x : 'a), elem x (filter p xs) => elem x (filter q xs).


(* cnst f : 'a -> 'b. *)

op f_map(f : 'a -> 'b, x : 'a , xs : 'b list) : 'b list = f x :: xs.

op map(f :'a -> 'b) : 'a list -> 'b list = foldr [] (f_map f).

lemma map_def1 : forall(f : 'a -> 'b),map f [] = [].
lemma map_def2 : forall(f : 'a -> 'b, x : 'a, xs : 'a list ), map f (x::xs) = (f x)::(map f xs).

pred P_map_in(f : 'a -> 'b,xs : 'a list) = forall(x : 'a), elem x xs =>
 elem (f x) (map f xs).

lemma map_in_aux : forall (xs : 'a list,f : 'a -> 'b), (P_map_in f) xs 
proof.
intros xs f.
apply list_ind<:'a>((P_map_in f),_,_,xs);trivial.
save.

lemma map_in : forall (xs : 'a list,x : 'a, f : 'a -> 'b), elem x xs =>
 elem (f x) (map f xs).

pred P_map_o (f : 'a -> 'b, g : 'b -> 'c, h : 'a -> 'c, xs : 'a list) =
map g (map f xs) = map h xs.

lemma map_o_aux : forall (xs : 'a list,f : 'a -> 'b, g : 'b -> 'c, h : 'a -> 'c),
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

lemma map_app : forall (xs ys: 'a list, f : 'a -> 'b),
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

