require import Int.

theory T.
  pred mypr : bool.
end T.

clone T as U with pred mypr(x : bool) = x && x.
