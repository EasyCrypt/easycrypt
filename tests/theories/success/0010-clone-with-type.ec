require import int.

theory T.
  type t.
end T.

clone T as U with type t = int.

cnst myop : U.t = 0.
