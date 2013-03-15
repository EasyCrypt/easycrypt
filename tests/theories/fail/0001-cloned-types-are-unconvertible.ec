theory T.
  type t.

  op myop : t -> bool.
end T.

theory U.
  type t' = T.t.

  clone T.

  op myop' (x : t') : bool = T.foo t.
end U.
