(* The `swap` program transformation, through the transformation rule of
   each logic: hoare (with exceptional postconditions), ehoare, phoare and
   equiv (each side, and both sides at once), at the top level and in
   nested blocks (branches of an `if`, body of a `while`, arm of a
   `match`), with relative and absolute offsets, the derived `interleave`,
   and the error paths. Each tactic is a separate sentence, so that the
   goals it leaves can be compared across builds. *)
require import AllCore Xreal.

exception e.

module M = {
  var x, y, z, w : int

  proc f() : unit = {
    x <- 1;
    y <- 2;
    z <- 3;
    w <- 4;
  }

  proc c(b : bool) : unit = {
    if (b) {
      x <- 1;
      y <- 2;
      z <- 3;
    } else {
      y <- 5;
      x <- 6;
    }
    w <- 0;
  }

  proc l() : unit = {
    x <- 0;
    while (x < 10) {
      y <- 1;
      z <- 2;
      x <- x + 1;
    }
  }

  proc n(b : bool) : unit = {
    if (b) {
      while (x < 10) {
        y <- 1;
        z <- 2;
        x <- x + 1;
      }
    }
  }

  proc m(o : int option) : unit = {
    match o with
    | None   => { x <- 0; y <- 1; }
    | Some v => { x <- v; y <- v + 1; z <- 2; }
    end;
  }

  proc d() : unit = {
    x <- 1;
    y <- x;
    x <- 2;
    z <- 3;
  }

  proc nd(o : int option) : unit = {
    match o with
    | None   => { x <- 0; }
    | Some v => { x <- v; y <- x; }
    end;
    while (x < 3) {
      x <- x + 1;
      y <- x;
    }
  }

  proc r() : unit = {
    x <- 1;
    raise e;
    y <- 2;
  }
}.

module N = {
  proc f() : unit = {
    M.w <- 4;
    M.z <- 3;
    M.y <- 2;
    M.x <- 1;
  }

  proc c(b : bool) : unit = {
    if (b) {
      M.z <- 3;
      M.y <- 2;
      M.x <- 1;
    } else {
      M.x <- 6;
      M.y <- 5;
    }
    M.w <- 0;
  }
}.

(* -------------------------------------------------------------------- *)
(* hoare *)
lemma h_top : hoare [M.f : true ==> M.x = 1 /\ M.y = 2 /\ M.z = 3 /\ M.w = 4].
proof.
proc.
swap 1 1.
swap 4 -2.
swap [1..2] 2.
swap [3..4] -2.
swap 1 @3.
swap 2.
swap -1.
auto.
qed.

lemma h_exc :
  hoare [M.f : true ==> M.x = 1 /\ M.y = 2 | e => M.w = 4].
proof.
proc.
swap 1 3.
swap [1..2] 1.
auto.
qed.

lemma h_if : hoare [M.c : true ==> M.w = 0].
proof.
proc.
swap 1.:[1..1] 1.
swap 1.3 -2.
swap 1?1 1.
swap 1.:[2..3] -1.
auto.
qed.

lemma h_while : hoare [M.l : true ==> 10 <= M.x].
proof.
proc.
swap 2.:[1..1] 1.
swap 2.3 -2.
while (true).
- by auto.
by auto => /#.
qed.

lemma h_nested : hoare [M.n : true ==> true].
proof.
proc.
swap 1.1.1 1.
swap 1.1.:[2..3] -1.
swap 1.1.3 @1.
by auto; while (true); auto.
qed.

lemma h_match : hoare [M.m : true ==> true].
proof.
proc.
swap 1#Some.1 1.
swap 1#Some.:[2..3] -1.
swap 1#None.1 1.
by auto.
qed.

lemma h_errors : hoare [M.d : true ==> true].
proof.
proc.
(* not independent: reads / writes / writes what the other writes / reads *)
fail swap 2 1.
fail swap 1 2.
fail swap 1 1.
fail swap 2 -1.
fail swap 3 -1.
(* invalid ranges and offsets *)
fail swap [3..1] 1.
fail swap [1..5] 1.
fail swap 5 1.
fail swap 1 5.
fail swap 4 -4.
fail swap [1..2] @2.
fail swap [1..2] @9.
fail swap @2.
fail swap 1.1 1.
fail swap 1?:[1..1] 1.
(* sided swap on a non-equiv goal *)
fail swap{1} 1 1.
fail swap{2} 1 1.
swap 4 -1.
abort.

lemma h_nested_errors : hoare [M.nd : true ==> true].
proof.
proc.
fail swap 1#Some.1 1.
fail swap 1#Some.2 -1.
fail swap 2.2 -1.
fail swap 2.:[1..2] 1.
fail swap 2?1 1.
fail swap 1#None.1 1.
abort.

lemma h_raise : hoare [M.r : true ==> true | e => true].
proof.
proc.
fail swap 1 1.
fail swap 2 1.
fail swap 3 -1.
fail swap [1..2] 1.
abort.

(* -------------------------------------------------------------------- *)
(* ehoare *)
lemma eh_top : ehoare [M.f : 1%xr ==> (M.x = 1 /\ M.w = 4)%xr].
proof.
proc.
swap 1 1.
swap [3..4] -2.
fail swap{1} 1 1.
auto.
qed.

lemma eh_nested : ehoare [M.c : 1%xr ==> (M.w = 0)%xr].
proof.
proc.
swap 1.1 1.
swap 1?:[1..1] 1.
fail swap 1.1 @4.
auto.
qed.

lemma eh_errors : ehoare [M.d : 1%xr ==> 1%xr].
proof.
proc.
fail swap 1 1.
fail swap 2 -1.
fail swap [1..3] 2.
abort.

(* -------------------------------------------------------------------- *)
(* phoare *)
lemma ph_top : phoare [M.f : true ==> M.x = 1 /\ M.w = 4] = 1%r.
proof.
proc.
swap 1 1.
swap [3..4] -2.
fail swap{2} 1 1.
auto.
qed.

lemma ph_le : phoare [M.c : true ==> M.w = 0] <= 1%r.
proof.
proc.
swap 1.:[1..2] 1.
swap 1?1 1.
auto.
qed.

lemma ph_ge : phoare [M.l : true ==> true] >= 0%r.
proof.
proc.
swap 2.1 1.
auto.
qed.

lemma ph_errors : phoare [M.d : true ==> true] = 1%r.
proof.
proc.
fail swap 1 1.
fail swap 2 -1.
fail swap 1.1 1.
abort.

(* -------------------------------------------------------------------- *)
(* equiv *)
lemma e_sides : equiv [M.f ~ N.f : true ==> ={M.x, M.y, M.z, M.w}].
proof.
proc.
swap{1} 1 3.
swap{2} 4 -3.
swap{1} [1..2] 2.
swap{2} [3..4] -2.
swap{1} 1 @4.
swap{2} -1.
auto.
qed.

lemma e_both : equiv [M.f ~ M.f : true ==> ={M.x, M.y, M.z, M.w}].
proof.
proc.
swap 1 1.
swap [2..3] 1.
swap 4 -3.
sim.
qed.

lemma e_nested : equiv [M.c ~ N.c : ={b} ==> ={M.x, M.y, M.w}].
proof.
proc.
swap{1} 1.:[1..2] 1.
swap{1} 1.1 1.
swap{2} 1?1 1.
swap{1} 1?1 1.
swap{2} 1.1 1.
swap{2} 1.3 -1.
by auto => /#.
qed.

lemma e_loop : equiv [M.l ~ M.l : ={M.y, M.z} ==> ={M.x, M.y, M.z}].
proof.
proc.
swap{1} 2.1 1.
swap{2} 2.2 -1.
sim.
qed.

lemma e_loop_nested : equiv [M.n ~ M.n : ={b, M.x, M.y, M.z} ==> ={M.x, M.y, M.z}].
proof.
proc.
swap{1} 1.1.1 1.
swap{2} 1.1.:[2..2] -1.
sim.
qed.

lemma e_match : equiv [M.m ~ M.m : ={o, M.z} ==> ={M.x, M.y, M.z}].
proof.
proc.
swap{1} 1#Some.1 1.
swap{2} 1#Some.:[2..2] -1.
swap 1#None.1 1.
sim.
qed.

lemma e_errors : equiv [M.d ~ M.r : true ==> true].
proof.
proc.
fail swap{1} 1 1.
fail swap{1} 2 -1.
fail swap{1} [1..5] 1.
fail swap{1} 1 @1.
fail swap{2} 1 1.
fail swap{2} 3 -1.
fail swap{2} 1.1 1.
fail swap 1 1.
abort.

(* -------------------------------------------------------------------- *)
(* interleave (derived: a sequence of swaps) *)
module I = {
  var a, b, c, d : int

  proc f() : unit = {
    a <- 1;
    b <- 2;
    c <- 3;
    d <- 4;
  }

  proc g() : unit = {
    a <- 1;
    c <- 3;
    b <- 2;
    d <- 4;
  }
}.

lemma h_interleave : hoare [I.f : true ==> I.a = 1 /\ I.d = 4].
proof.
proc.
interleave [1:1] [3:1] 2.
auto.
qed.

lemma e_interleave : equiv [I.f ~ I.g : true ==> ={I.a, I.b, I.c, I.d}].
proof.
proc.
interleave{1} [1:1] [3:1] 2.
fail interleave{2} [3:1] [1:1] 1.
sim.
qed.
