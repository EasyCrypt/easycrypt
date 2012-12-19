theory T.
  theory U.
    theory V.
      type t.

      require lib.
    end V.
  end U.
end T.

import lib.T2.

type u = T.U.V.t.

import T.

type v = U.V.t.

type 'b w = 'b lib.T1.t.

