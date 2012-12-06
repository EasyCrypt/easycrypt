type 'a list.
cnst nil ['a] : 'a list.
cnst nil' : 'a list.
cnst k : _ = 3.

op cons ['a] : ('a, 'a list) -> 'a list.
op cons' : ('a, 'a list) -> 'a list.
(* This it not allowed *)
(* op cons'' ['a] : ('a, 'b list) -> 'a list. *)
(* Should we allows this *)
op cons''' : ('a, 'b list) -> 'a list.

cnst lk : _ = cons(k, nil).

op cons2 ['a] (x1:'a, x2:'a, l:'a list) : 'a list = 
   cons(x1, cons(x2, l)).

op cons2' (x1:'a, x2:'a, l:'a list) : 'a list = 
   cons(x1, cons(x2, l)). 

op cons2''['a] (x1:'a, x2:_, l:_) : _ = 
  cons(x1, cons(x2, l)). 

op cons2''' (x1:'a, x2:_, l:_) : _ = 
  cons2(x1,x2,l).

op icons2 (x1:int, x2:int, l:int list) : int list = 
   cons2(x1,x2,l).

op icons2' (x1:_, l:_) : _ = 
  icons2(x1,x1,l).


cnst fail : _ = cons(0, cons(true,nil)).





