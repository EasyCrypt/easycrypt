require import Logic.

type t.

op e1 : t.
op e2 : t.

module M = {
  var x : t
  fun f (b:bool) : unit = {
    if (b) {
      x = e1;
    } else {
      x = e2;
    }
  }
}.

lemma foo_side : 
  equiv [M.f ~ M.f : b{1} = b{2} ==> M.x{1}=M.x{2} ].
proof.
 fun.
 if {1}.
 if {2}.
 wp;skip;simplify;split.
 wp;skip;trivial.
 rcondf {2} 1.
  intros &m;skip;trivial.
 wp;skip;trivial.
save.

lemma foo : 
  equiv [M.f ~ M.f : b{1} = b{2} ==> M.x{1}=M.x{2} ].
proof.
 fun.
 if.
 intros &m1 &m2 Heq;rewrite Heq;simplify;trivial.
 wp;skip;trivial.
 wp;skip;trivial.
save.




