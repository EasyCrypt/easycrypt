theory T.
  op o : int.
end T.

theory U.
  op o : int.
end U.

import T.
import U.

axiom L : o%T = 0.

op myop : int = o%T.

