require import Logic.
require import Distr.
require import Bool.
require import Real.

type t.

op b1 : bool.
op b2 : bool.
op e1 : t.
op e2 : t.

module M = {
  var x, y : t
  fun f () : unit = {
    if (b1) {
      x = e1;
    } else {
      x = e2;
    }
  }
}.

lemma foo : bd_hoare [M.f : (b1 => M.y=e1) && (b2 => M.y=e2) && (b1||b2) ==> 
                         M.x=M.y ] [=] [1%r]
proof.
 fun.
 if; wp; skip; trivial.
save.



