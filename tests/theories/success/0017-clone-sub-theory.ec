require import Int.

theory T.
  op myopt : unit.

  theory U.
    type t.
  end U.

  theory V.
    theory S.
      op myop : U.t.
    end S.
  end V.
end T.

clone T as W with
  type U.t      = int,
  op   V.S.myop = 0.

op i : bool = W.V.S.myop = 1.
