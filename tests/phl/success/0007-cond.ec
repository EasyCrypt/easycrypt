require import Logic.

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

lemma foo : hoare [M.f : (b1 => M.y=e1) && (b2 => M.y=e2) && (b1||b2) ==> 
                         M.x=M.y ].
proof.
 fun.
 if; wp; skip;  smt.
save.

