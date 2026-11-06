(* The [inline] tactic, as the [inline] program transformation applied
   through the transformation rule of each logic: every form (by name,
   all, occurrences, code position, with and without [tuple]), every
   logic, both equiv sides, nested positions and the error paths. The
   remaining goals are admitted with [admit. qed.], so that the proof tree
   (and thus the transformation nodes) is rechecked under EC_RECHECK. *)
require import AllCore Xreal.

exception oops of int.

(* -------------------------------------------------------------------- *)
module type T = {
  proc o(x : int) : int
}.

module N = {
  var g : int

  (* parameters and locals named like the caller's variables *)
  proc f(x : int, y : int) : int * int = {
    var z;
    z <- x + y;
    g <- z;
    return (z, x);
  }

  (* a single parameter of tuple type *)
  proc p(xy : int * int) : int = {
    return xy.`1 + xy.`2;
  }

  (* no return value *)
  proc u(x : int) = {
    g <- x;
  }

  (* calls another procedure *)
  proc h(x : int) : int = {
    var r;
    r <@ p(x, x);
    return r;
  }
}.

module O = {
  proc o(x : int) : int = {
    return x;
  }
}.

module M (A : T) = {
  (* calls at the top level, in the branches of an [if], of a [while] and
     of a [match] *)
  proc main(o : int option) : int = {
    var x, y, z, a, b;
    x <- 0;
    y <- 1;
    (x, y) <@ N.f(x, y);
    if (x < y) {
      z <@ N.p(x, y);
    } else {
      N.u(y);
      z <@ N.h(x);
    }
    while (x < 10) {
      (a, b) <@ N.f(x, z);
      x <- x + 1;
    }
    match o with
    | None => { z <@ N.h(z); }
    | Some v => { N.u(v); z <@ A.o(v); }
    end;
    return x + y + z;
  }

  (* a call followed by a raise *)
  proc e(x : int) : int = {
    x <@ N.p(x, x);
    if (x < 0) { raise (oops x); }
    return x;
  }
}.

(* -------------------------------------------------------------------- *)
(* hoare *)
lemma hoare_all (A <: T) : hoare [M(A).main : true ==> true].
proof.
proc; inline *.
admit. qed.

lemma hoare_name (A <: T) : hoare [M(A).main : true ==> true].
proof.
proc; inline N.f N.u.
inline N.h.
inline N.p.
admit. qed.

lemma hoare_minus (A <: T) : hoare [M(A).main : true ==> true].
proof.
proc; inline * - N.f.
inline N - N.h.
admit. qed.

lemma hoare_tuple (A <: T) : hoare [M(A).main : true ==> true].
proof.
proc; inline [tuple] N.f.
admit. qed.

lemma hoare_notuple (A <: T) : hoare [M(A).main : true ==> true].
proof.
proc; inline [-tuple] N.f.
admit. qed.

lemma hoare_occs (A <: T) : hoare [M(A).main : true ==> true].
proof.
proc; inline (2 4) N.
inline (1) N.f.
admit. qed.

lemma hoare_codepos (A <: T) : hoare [M(A).main : true ==> true].
proof.
proc; inline 6#Some.1.
inline 6#None.1.
inline 5.1.
inline 4?2.
inline 4?1.
inline 4.1.
inline 3.
admit. qed.

lemma hoare_exn : hoare [M(O).e : true ==> true | oops v => v < 0].
proof.
proc; inline *.
admit. qed.

lemma hoare_nothing : hoare [N.p : true ==> true].
proof.
proc; inline *.
admit. qed.

lemma hoare_errors (A <: T) : hoare [M(A).main : true ==> true].
proof.
proc.
fail inline{1} *.
fail inline{1} 3.
fail inline 1.
fail inline 6#Some.2.
fail inline A.o.
admit. qed.

(* -------------------------------------------------------------------- *)
(* ehoare: by name or all only *)
lemma ehoare_all (A <: T) : ehoare [M(A).main : (1%xr) ==> (1%xr)].
proof.
proc; inline *.
admit. qed.

lemma ehoare_name (A <: T) : ehoare [M(A).main : (1%xr) ==> (1%xr)].
proof.
proc; inline [-tuple] N.f.
inline N.h N.p.
admit. qed.

lemma ehoare_errors (A <: T) : ehoare [M(A).main : (1%xr) ==> (1%xr)].
proof.
proc.
fail inline (1).
fail inline 3.
fail inline{1} *.
fail inline A.o.
admit. qed.

(* -------------------------------------------------------------------- *)
(* phoare *)
lemma phoare_all (A <: T) : phoare [M(A).main : true ==> true] = 1%r.
proof.
proc; inline *.
admit. qed.

lemma phoare_name (A <: T) : phoare [M(A).main : true ==> true] <= 1%r.
proof.
proc; inline [-tuple] N.f.
inline N.h.
admit. qed.

lemma phoare_occs (A <: T) : phoare [M(A).main : true ==> true] >= 1%r.
proof.
proc; inline (1 3) N.
admit. qed.

lemma phoare_codepos (A <: T) : phoare [M(A).main : true ==> true] = 1%r.
proof.
proc; inline 5.1.
inline 4?1.
inline 6#None.1.
admit. qed.

lemma phoare_errors (A <: T) : phoare [M(A).main : true ==> true] = 1%r.
proof.
proc.
fail inline{2} *.
fail inline 2.
fail inline A.o.
admit. qed.

(* -------------------------------------------------------------------- *)
(* equiv: both sides, one side at a time *)
lemma equiv_all (A <: T) : equiv [M(A).main ~ M(A).main : ={o} ==> true].
proof.
proc; inline *.
admit. qed.

lemma equiv_left (A <: T) : equiv [M(A).main ~ M(A).main : ={o} ==> true].
proof.
proc; inline{1} *.
inline{2} [-tuple] N.f.
inline{2} N - N.f.
admit. qed.

lemma equiv_both_name (A <: T) : equiv [M(A).main ~ M(A).main : ={o} ==> true].
proof.
proc; inline N.f.
admit. qed.

lemma equiv_occs (A <: T) : equiv [M(A).main ~ M(O).main : ={o} ==> true].
proof.
proc; inline{1} (1 4) N.
inline{2} (5) N.
admit. qed.

lemma equiv_codepos (A <: T) : equiv [M(A).main ~ M(O).main : ={o} ==> true].
proof.
proc; inline{1} 5.1.
inline{2} 6#Some.2.
inline{2} 4?2.
inline{1} 3.
admit. qed.

lemma equiv_errors (A <: T) : equiv [M(A).main ~ M(O).main : ={o} ==> true].
proof.
proc.
fail inline (1).
fail inline 3.
fail inline{1} 1.
fail inline{1} 6#Some.2.
fail inline{1} A.o.
admit. qed.
