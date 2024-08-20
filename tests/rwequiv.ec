(* -------------------------------------------------------------------- *)
require import AllCore.

(* -------------------------------------------------------------------- *)
module M = {
  proc foo(x : int, y : int) : bool = {
    var r <- true;
    if (x < y) {
      r <- false;
    }
    return r;
  }

  proc bar(x : int, y : int) : bool = {
    var r <- false;
    if (y <= x) {
      r <- true;
    }
    return r;
  }
}.

module N = {
  proc baz(x : int, y : int) : bool = {
    var r1, r2;
    r1 <@ M.bar(x, y);
    r2 <@ M.foo(x, y);
    return r1 = r2;
  }
}.

(* -------------------------------------------------------------------- *)
equiv foo_bar_eq: M.foo ~ M.bar: ={arg} ==> ={res}.
proof.
proc.
by auto=> /#.
qed.

(* -------------------------------------------------------------------- *)
equiv test1: M.foo ~ M.bar: ={arg} ==> ={res}.
proof.
proc*.
rewrite equiv[{1} 1 foo_bar_eq].
by sim.
qed.

(* -------------------------------------------------------------------- *)
equiv test2: M.foo ~ M.bar: ={arg} ==> ={res}.
proof.
proc*.
rewrite equiv[{2} 1 -foo_bar_eq].
by sim.
qed.

(* -------------------------------------------------------------------- *)
equiv test3: M.foo ~ M.bar: ={arg} ==> ={res}.
proof.
proc*.
rewrite equiv[{1} 1 foo_bar_eq (x, y :@ r)].
by sim.
qed.

(* -------------------------------------------------------------------- *)
equiv test4: N.baz ~ N.baz: ={arg} ==> ={res}.
proof.
proc.
rewrite equiv[{1} 2 foo_bar_eq].
rewrite equiv[{2} 1 -foo_bar_eq].
rewrite equiv[{2} 2 foo_bar_eq].
rewrite equiv[{1} 1 -foo_bar_eq].
by sim.
qed.
