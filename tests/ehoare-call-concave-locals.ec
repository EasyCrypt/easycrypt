(* [call /fc] on an ehoare goal: as for [call], the specification is typed
   in the memories of the called procedure and the invariant in an
   abstract memory, so that the local variables of the caller are not in
   scope (they used to be read as the callee's variables of the same
   name, which proves [false]). *)
require import AllCore Xreal.

module G = { var g : int }.

module M = {
  proc g() = { var y; y <- 0; }

  proc h() = { var y; G.g <- G.g + 1; y <- G.g; }

  proc main() : int = { var y; y <- 1; g(); return y; }

  proc main2() : bool = { var y; G.g <- 0; y <- 0; h(); return y <> G.g; }
}.

(* the specification mentions [y], a local of the caller *)
lemma bad : ehoare [M.main : 0%xr ==> (res = 1)%xr].
proof.
proc.
fail call /(fun x => x) (_ : 0%xr ==> (y = 1)%xr).
abort.

(* the invariant mentions [y], a local of the caller *)
lemma bad_inv : ehoare [M.main2 : 0%xr ==> res%xr].
proof.
proc.
fail call /(fun x => x) (: (y <> G.g)%xr).
abort.

(* globals only: accepted *)
lemma ok : ehoare [M.main2 : 1%xr ==> (G.g = 1)%xr].
proof.
proc.
call /(fun x => x) (_ : (G.g = 0)%xr ==> (G.g = 1)%xr).
+ by proc; auto => &hr /=; have -> : (G.g{hr} + 1 = 1) = (G.g{hr} = 0) by smt().
by auto.
qed.
