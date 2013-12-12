require import Logic.

type t.

op e1 : t.
op e2 : t.

module M = {
  var x : t
  proc f (b:bool) : unit = {
    if (b) {
      x = e1;
    } else {
      x = e2;
    }
  }
}.

lemma foo_side : 
  equiv [M.f ~ M.f : b{1} = b{2} ==> M.x{1}=M.x{2} ].
proof -strict.
 proc.
 if {1}.
 if {2}.
 wp;skip;simplify;split.
 wp;skip;smt.
 rcondf {2} 1.
  intros &m;skip;smt.
 wp;skip;smt.
qed.

lemma foo : 
  equiv [M.f ~ M.f : b{1} = b{2} ==> M.x{1}=M.x{2} ].
proof -strict.
 proc.
 if.
 intros &m1 &m2 Heq;rewrite Heq;simplify;smt.
 wp;skip;smt.
 wp;skip;smt.
qed.




