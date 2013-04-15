type 'a t.

op (+) : 'a t -> 'a t -> 'a t.

op (++) (x y :'a t) = x + x + y.

op (+++) (x:'a t) y = x + x ++ y.
 
