theory T.
  theory Sub.
    type t.
  end Sub.
end T.

clone T.Sub as U.

type t = U.t.
