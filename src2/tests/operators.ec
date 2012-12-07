type 'a list.
cnst nil ['a] : 'a list.
print op nil.
cnst nil' : 'a list.
print op nil'.
cnst k : _ = 3.
print op k.

op cons ['a] : ('a, 'a list) -> 'a list.
print op cons.
op cons' : ('a, 'a list) -> 'a list.
print op cons'.
(* This it not allowed *)
(* op cons'' ['a] : ('a, 'b list) -> 'a list. *)
(* Should we allows this *)
op cons''' : ('a, 'b list) -> 'a list.
print op cons'''.

cnst lk : _ = cons(k, nil).
print op lk.

op cons2 ['a] (x1:'a, x2:'a, l:'a list) : 'a list = 
   cons(x1, cons(x2, l)).
print op cons2.

op cons2' (x1:'a, x2:'a, l:'a list) : 'a list = 
   cons(x1, cons(x2, l)). 
print op cons2'.

op cons2''['a] (x1:'a, x2:_, l:_) : _ = 
  cons(x1, cons(x2, l)). 
print op cons2''.

op cons2''' (x1:'a, x2:_, l:_) : _ = 
  cons2(x1,x2,l).
print op cons2'''.

op icons2 (x1:int, x2:int, l:int list) : int list = 
   cons2(x1,x2,l).
print op icons2.

op icons2' (x1:_, l:_) : _ = 
  icons2(x1,x1,l).
print op icons2'.

cnst fail : _ = cons(0, cons(true,nil)).





