require import Fun.
require import int.

prover 20 1 "Eprover" "Vampire" "Alt-Ergo" "Z3".

(* constructors *)
import why3 "list" "List"
   op "Nil" as "__nil";
   op "Cons" as "::".

(* op singleton (x: 'a) :  'a list = x::__nil. *)

(* lemma singleton_not_nil : forall (x : 'a ), singleton(x) <> __nil. *)
lemma cons_not_nil : forall (x : 'a ,xs : 'a list), x::xs <> __nil.

(* partial destructors *)
op hd : 'a list -> 'a.
op tl : 'a list -> 'a list.

axiom hd_def : forall (x : 'a, xs : 'a list), hd(x::xs) = x.
axiom tl_def : forall (x : 'a, xs : 'a list), tl(x::xs) = xs.

lemma list_inj : forall (xs : 'a list), 
  xs = __nil<:'a> || (exists (y : 'a), exists (ys : 'a list), xs =
  y::ys).

(* lemma hd_tl_decomp : forall (xs : 'a list), xs <> __nil<:'a> => *)
(*  hd(xs)::tl(xs) = xs. *)

(* list induction *)

axiom list_ind : forall(P:('a list) Pred),
((P(__nil)) &&
(forall (x :'a, xs : 'a list), P(xs) => P (x::xs))) =>
(forall(ys:'a list), P(ys)).


(* membership test *)
op elem : ('a * 'a list) -> bool.

axiom elem_def1 : forall (x : 'a), !elem(x,__nil).
axiom elem_def2 : forall (x, y : 'a, xs : 'a list), 
 elem(y,x::xs) = ((x = y) || elem(y,xs)).

lemma elem_cons : forall (x, y: 'a, xs : 'a list), elem(y,xs) => elem(y,x::xs).
(* lemma elem_singleton : forall (x, y : 'a), elem(x,singleton(y)) => x = y. *)
lemma elem_not_nil : forall (y: 'a, xs : 'a list), elem(y,xs) => xs <> __nil<:'a>.
lemma elem_hd : forall (xs : 'a list), xs <> __nil<:'a> => elem(hd(xs),xs).



(* length *)
op length : 'a list -> int.

axiom length_def1 : length<:'a>(__nil) = 0.
axiom length_def2 : forall (x : 'a, xs : 'a list), 
 length (x::xs) = 1 + length(xs).


op P_length_non_neg(xs : 'a list) : bool =
 0 <= length(xs).

lemma length_non_neg: forall (xs : 'a list), P_length_non_neg(xs)
proof.
intros xs.
apply list_ind<:'a>((P_length_non_neg),_,xs).
trivial.

save.


lemma length_z_nil : forall(xs : 'a list), length(xs) = 0 <=> xs = __nil.
lemma length_singleton : forall(x : 'a), length (singleton(x)) = 1.

(* append *)
op [++] : ('a list, 'a list) -> 'a list.

axiom app_def1 : forall (ys : 'a list), __nil++ys = ys.
axiom app_def2 : forall (x : 'a, xs, ys : 'a list), (x::xs)++ys = x::(xs++ys).

axiom app_assoc : forall (xs, ys, zs : 'a list), (xs++ys)++zs = xs++(ys++zs).

axiom length_app : forall (xs, ys : 'a list), 
 length(xs++ys) = length(xs) + length(ys).

axiom elem_app1 : forall(y : 'a, xs, ys : 'a list), 
 elem(y,ys) => elem(y,xs++ys).

axiom elem_app2 : forall(y : 'a, xs, ys : 'a list), 
 elem(y,xs) => elem(y,xs++ys).

axiom elem_app3 : forall(y : 'a, xs, ys : 'a list), 
 elem(y,xs++ys) => (elem(y,xs) || elem(y,ys)).

theory LMap.
type a.
type b.

cnst f : a -> b.

op map : a list -> b list.

axiom map_def1 : map [] = [].
axiom map_def2 : forall(x : a, xs : a list ), map (x::xs) = f(x)::(map(xs)).

axiom map_in : forall (x : a, xs : a list), elem(x,xs) =>
 elem(f(x),map xs).

axiom map_length : forall (xs : a list), length(xs) = length(map(xs)).

axiom map_app : forall(xs, ys : a list), map(xs ++ ys) = map(xs) ++ map(ys).

end LMap.












