op add : (int, int) -> int.

type 'a list'.

cnst nil : 'a list'.

op cons : ('a, 'a list') -> 'a list'. 

cnst t : 'a.

op cons2 (x, y : 'a, l : 'a list') = cons(x,cons(y,l)).

cnst l1 : int list' = cons2(1,2,nil).
cnst l2 : bool list' = cons2(true,false,nil).

op cons2' (x, y : 'a, l : 'a list') = cons(x,cons(y,l)) as cons2'.
  
op [::] : ('a, 'a list') -> 'a list' as Cons.

op eq1 (x, y : 'a) = x = y. 
op eq2 (x, y : int) = x = y. 
op eq3 (x, y : 'a) = x = y. 

print op.
print cnst.

(* This is not a valid operator *)
op [.] : int -> int.
