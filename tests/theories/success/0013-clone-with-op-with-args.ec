require import Int.

theory T.
  op myop : int -> int -> int.
end T.

clone T as U with op myop(x, y) = x + y.
