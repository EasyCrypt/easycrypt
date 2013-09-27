require import Int.

theory T.
  op myop : int -> int -> int -> int.

  op dup(x, y) = myop x y (x - y).

  axiom A : forall x y z, myop x y z = myop y x z.
end T.

op o(x, y, z) = x + y + z.

clone T as U with op myop(x, y, z) = x + y + 2*z.

clone T as V with op myop(x, y, z) <- x + y + 2*z.

clone T as W with op myop <- lambda (x, y, z), x + y + 2*z.

clone T as X with op myop <- o.

clone T as X1 with op myop(x) <- o x.

clone T as X2 with op myop(x, y) <- o y x.
