require import Int.

theory T.
  op myopt : unit.

  theory U.
    type t.
  end U.

  theory V.
    op myop : U.t.
  end V.
end T.

clone T as W with
  type U.t    = int,
  op   V.myop = 0.

op i : bool = W.V.myop = 1.
