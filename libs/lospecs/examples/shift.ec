require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.



abbrev SWAP_BYTES_256 = W256.of_int 1780731860627700044960722568376592179391279163832551066649583786025356815.


abbrev SWAP_BYTES_128 = W128.of_int 5233100606242806050955395731361295.

abbrev six_i = W8.of_int 40.

print W8.([-]).

module M = {
  proc shift_left_i_256 (w:W256.t, i:W8.t) : W256.t = {

  var h:W128.t;
    var l:W128.t;
    var hl:W256.t;
  var hli:W256.t;
    var hli2:W256.t;
    var hl64i:W256.t;
    var hl64il:W256.t;
  var l64ir:W128.t;
  var aux:W128.t;
    var h2:W128.t;
  var six_i:W8.t;
    var mi:W8.t;

    mi <- -i;
    six_i <- (W8.of_int 64) + mi;
  hli <- VPSLL_4u64 w i;
    hl64i <- VPSRL_4u64 w six_i;
    hl64il <- VPSLLDQ_256 hl64i (W8.of_int 64);
  hli2 <- VPXOR_256 hli hl64il;
    aux <- truncateu128 hl64i;
    l64ir <- VPSRLDQ_128 aux (W8.of_int 64);
    h <- VEXTRACTI128 hli2 (W8.of_int 1);
    h2 <- VPXOR_128 h l64ir;
    l <- truncateu128 hli2;
    hl <- concat_2u128 h2 l;
    return hl;
  }
}.

print VPXOR_256.

print truncateu128.

op shift_left_i (w: W256.t, i: W8.t) : W256.t =
  w `<<` i.

bdep M.shift_left_i_256 shift_left_i 0 0 ["hl"] 16.
