type 'a t.

op plus : ('a t, 'a t) -> 'a t.

op mul2 (x:_) : _ = plus(x,x).