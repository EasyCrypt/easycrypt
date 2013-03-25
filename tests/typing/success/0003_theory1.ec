theory T.
  theory U.
    theory V.
      type t.

      require Lib.
    end V.
  end U.
end T.

import Lib.T2.

type u = T.U.V.t.

import T.

type v = U.V.t.

type 'b w = 'b Lib.T1.t.

