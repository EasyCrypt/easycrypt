require import Int.

theory T.
  pred mypr.
end T.

clone T as U with pred mypr = true.
