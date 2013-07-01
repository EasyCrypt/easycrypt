require import Int.

theory T.
  type t.
end T.

clone T as U with type t <- int.

op myop : int = 0.

theory V.
  type 'a t.

  op x : 'a t.
end V.

clone V as W with type 'b t <- 'b * 'b.

op myop2 : int * int = W.x.
