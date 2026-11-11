(* [proc change] inside the arm of a [match]: the local equivalence is
   quantified over the locals bound by the arm (here [v], read by the
   original fragment only). *)
require import AllCore.

type t = [A | B of int].

module M = {
  proc f(o : t) : int = {
    var x, z : int;
    x <- 0;
    z <- 0;
    match o with
    | A => { x <- 1; }
    | B v => { z <- v; z <- 1; }
    end;
    return x + z;
  }
}.

lemma L : hoare [M.f : true ==> true].
proof.
proc.
proc change 3#B.:[1..2] : { z <- 1; }.
- move=> v.
  by auto.
by auto.
qed.
