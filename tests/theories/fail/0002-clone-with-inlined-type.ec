require import Int.

theory T.
  type t.
end T.

clone T as U with type t <- int.

type t = U.t.
