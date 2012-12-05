type 'a list.
cnst nil ['a] : 'a list.
op cons ['a] : ('a, 'a list) -> 'a list.

op cons2['a] (x1:'a, x2:'a, l:'a list) : 'a list = 
  cons(x1, cons(x2, l)).

op icons2 (x1:int, x2:int, l:int list) : int list = 
   cons2(x1,x2,l).

op cons2'['a] (x1:'a, x2:_, l:_) : _ = 
  cons2(x1,x2,l).




