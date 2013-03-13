theory T.
  theory Sub.
    type t.
  end Sub.
end T.

clone T as U.

type t = U.Sub.t.
