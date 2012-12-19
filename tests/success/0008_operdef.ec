type 'a t.

op plus : ('a t, 'a t) -> 'a t.

(* FIXME: fail or success *)
op mul2 (x:_) : _ = plus(x,x).