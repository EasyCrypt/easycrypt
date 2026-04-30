theory T.
  theory V.
    op foo : int.
  end V.

  theory U = V.
end T.

import T.

op bar : int = U.foo.

print T.
