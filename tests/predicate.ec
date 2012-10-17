type 'a list'.

cnst nil : 'a list'.

op [::] : ('a, 'a list') -> 'a list' as cons.

op in_list' : ('b, 'b list') -> bool.

type ilist' = int list'.

op icons (x:int, l:ilist') = x::l.

op length : 'a list' -> int.

cnst n : int = length (1::(2::nil)).

(*op toto (x:int) = n + x.*)

pred my_eq (x, y : 'a) = x = y.

pred all_eq (x : 'c, l : 'c list') =
  forall (a : 'c), in_list'(a,l) => x = a.
    
pred all1 (l : int list') = all_eq(1,l).

pred alltrue (l : bool list') = all_eq(true,l).

pred is_true (b:bool) = b.

lemma toto : forall (b:bool), is_true(b) => b.

axiom in_list'_cons1 : forall (a : 'a, l : 'a list'),
   in_list'(a, a::l).

lemma alltrue_fst : forall (x, y : 'a, l : 'a list'),
    all_eq(x, y::l) => x = y.

lemma test : forall (x,y:int), x + y = y + x. 

print axiom.

unset test.

print axiom.

print unset.

print set.

print pred.
