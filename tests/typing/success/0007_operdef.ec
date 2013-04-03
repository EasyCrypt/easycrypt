type 'a t.

op (+) : ('a t, 'a t) -> 'a t.

op (++) (x:'a t, y:_) : _ = x + x + y.

op (+++) (x:'a t, y:_) : _ = x + x ++ y.
 
