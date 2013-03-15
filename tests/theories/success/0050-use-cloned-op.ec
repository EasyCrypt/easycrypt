theory T.
  type t.

  op myop : t -> bool.
end T.

theory U.
  clone T as T'.

  op myop' (t : T'.t) : bool = T'.myop t.
end U.
