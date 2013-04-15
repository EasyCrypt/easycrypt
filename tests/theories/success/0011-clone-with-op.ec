require import Int.

theory T.
  op myop : int.
end T.

clone T as U with op myop = 0.
