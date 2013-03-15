theory T.
  type t.

  op myop : t -> bool.
end T.

theory U.
  clone T as T'.

  op myop' (t : T'.t) : bool = T'.foo t.
end U.
