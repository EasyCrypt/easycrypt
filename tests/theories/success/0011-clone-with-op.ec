require import Int.

theory T.
  cnst myop : int.
end T.

clone T as U with cnst myop = 0.
