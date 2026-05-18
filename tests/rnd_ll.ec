require import AllCore.

fail op[lossless] dC : bool distr.

require import Distr.

op[lossless] dC : bool distr.

module M = { 
  proc p1() = {
    var e1;
    e1 <$ dC;
  }
}.

equiv foo : M.p1 ~ M.p1 : true ==> true.
proc. 
rnd.
abort.