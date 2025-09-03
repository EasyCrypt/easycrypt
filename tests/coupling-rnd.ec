require import AllCore List.
require import Distr DBool DList.
(*---*) import Biased.
require import StdBigop.
(*---*) import Bigreal Bigreal.BRA.

module A = {
  proc f() : bool = {
    var x : bool;
    x <$ dbiased 0.25;
    return x;
  }
  proc g() : bool list = {
    var x : bool list;
    x <$ dlist {0,1} 2;
    return x;
  }
  proc h() : bool = {
    var x : bool;
    x <$ dbiased 0.25;
    return x;
  }
}.

op m (t : bool * bool list) : real =
  if t.`1 = false /\ t.`2 = [false; false] then 0.25
  else if t.`1 = true /\ t.`2 = [true; true] then 0.75
  else 0%r.

op g : (bool * bool list) distr = (Distr.mk m).

lemma l_coupling:
  equiv [ A.f ~ A.g : true ==> res{1} <=> (res{2} = [true; true]) ].
proof.
proc.
rnd g.
+ move => //= a b.
  rewrite supportP.
  rewrite muK //=.
  + admit.
  by smt().
+ rewrite /iscoupling; split.
  + admit.
  + admit.
qed.

op f (x : bool) : bool = x.

lemma l_bijection:
  equiv [ A.f ~ A.h : true ==> res{1} <=> res{2} ].
proof.
proc.
rnd f.
by skip => />.
qed.
