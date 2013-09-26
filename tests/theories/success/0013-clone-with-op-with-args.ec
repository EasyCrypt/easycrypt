require import Int.

theory T.
  op myop : int -> int -> int.

  op dup = myop.
end T.

clone T as U with op myop(x, y) = x + y.

clone T as V with op myop(x, y) <- x + y.

clone T as W with op myop <- lambda (x, y), x + y.
