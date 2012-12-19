type 'a t.

op plus ['a] : ('a t, 'a t) -> 'a t.

(* FIXME : fail or success ? *)
op pplus ['a 'b] (x:'a t) : _ = plus(x, x).


 
