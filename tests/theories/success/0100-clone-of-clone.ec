theory T.
  type t.
  op foo: t -> bool.
end T.

theory U.
  clone T.
  type t = T.t.
end U.

theory V.
  clone U.
end V.
