require import AllCore Distr DBool Xreal.

type t = [A | B of int].

exception oops of int.

module M = {
  var g : int

  proc f(a : int) : int = {
    var x, y, b;
    x <- a;
    b <$ {0,1};
    y <- x + 1;
    if (b) { y <- y + 1; } else { y <- y - 1; }
    match (B y) with
    | A   => { x <- 0; }
    | B z => { x <- z; }
    end;
    return x;
  }

  proc h(a : int) : int = {
    var x;
    x <- a;
    if (x < 0) { raise (oops x); }
    x <- x + 1;
    return x;
  }

  proc e(a : int) : int = {
    var x, b;
    x <- a;
    b <$ {0,1};
    if (b) { x <- x + 1; }
    return x;
  }

  proc w(a : int) : int = {
    var x;
    x <- a;
    while (x < 10) { x <- x + 1; }
    x <- x + 1;
    return x;
  }
}.

(* -------------------------------------------------------------------- *)
(* hoare *)

(* Without position: as far as possible, stopping at the sampling. *)
lemma hoare_wp (a0 : int) : hoare [M.f : a = a0 ==> res = a0 \/ res = a0 + 2].
proof.
proc; wp.
rnd; wp; skip => /> b _; case: b => //=; smt().
qed.

(* With a position: wp of the suffix after the first two instructions. *)
lemma hoare_wp_at (a0 : int) : hoare [M.f : a = a0 ==> res = a0 \/ res = a0 + 2].
proof.
proc; wp 2.
rnd; wp 0; skip => /> b _; case: b => //=; smt().
qed.

(* Nothing to do: the goal is unchanged. *)
lemma hoare_wp_noop : hoare [M.e : true ==> true].
proof.
proc; wp; wp; rnd; wp; skip => //.
qed.

(* Exceptional postconditions: a [raise] has its exceptional post as wp. *)
lemma hoare_wp_raise (a0 : int) :
  hoare [M.h : a = a0 ==> res = a0 + 1 | oops x => x < 0 /\ x = a0].
proof.
proc; wp; skip => /> /#.
qed.

lemma hoare_wp_raise_at (a0 : int) :
  hoare [M.h : a = a0 ==> res = a0 + 1 | oops x => x < 0 /\ x = a0].
proof.
proc; wp 1; wp; skip => /> /#.
qed.

(* A [raise] with no matching exceptional postcondition. *)
lemma hoare_wp_raise_nopost : hoare [M.h : true ==> true].
proof.
proc.
fail wp.
wp 2.
abort.

lemma hoare_wp_errors : hoare [M.f : true ==> true].
proof.
proc.
fail wp 1.           (* remaining: the sampling is not wp-able *)
fail wp 1 1.         (* a pair of positions: equiv only *)
fail wp 7.           (* invalid position *)
wp 2; rnd; wp; skip => //.
qed.

(* -------------------------------------------------------------------- *)
(* ehoare: samplings are wp-able *)

lemma ehoare_wp : ehoare [M.e : (1%xr) ==> (1%xr)].
proof.
proc; wp; skip => &hr /=.
by rewrite EpC dbool_ll.
qed.

lemma ehoare_wp_at : ehoare [M.e : (1%xr) ==> (1%xr)].
proof.
proc; wp 1; wp; skip => &hr /=.
by rewrite EpC dbool_ll.
qed.

lemma ehoare_wp_errors : ehoare [M.e : (1%xr) ==> (1%xr)].
proof.
proc.
fail wp 1 1.
fail wp 9.
abort.

(* A loop is not wp-able. *)
lemma ehoare_wp_while : ehoare [M.w : (1%xr) ==> (1%xr)].
proof.
proc.
fail wp 1.
wp.
abort.

(* -------------------------------------------------------------------- *)
(* bdhoare *)

lemma phoare_wp_eq (a0 : int) :
  phoare [M.f : a = a0 ==> res = a0 \/ res = a0 + 2] = 1%r.
proof.
proc; wp.
rnd; wp; skip => />; smt(dbool_ll).
qed.

lemma phoare_wp_at_ge (a0 : int) :
  phoare [M.f : a = a0 ==> res = a0 + 2] >= (1%r/2%r).
proof.
proc; wp 2.
rnd (fun b => b); wp; skip => />; smt(dboolE).
qed.

lemma phoare_wp_le (a0 : int) :
  phoare [M.f : a = a0 ==> res = a0 + 2] <= (1%r/2%r).
proof.
proc; wp.
rnd (fun b => b); last by smt().
wp; skip => />; smt(dboolE).
qed.

lemma phoare_wp_errors : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
fail wp 1.
fail wp 1 1.
abort.

(* bdhoare wp is one-sided: a [raise] is not wp-able. *)
lemma phoare_wp_raise : phoare [M.h : true ==> true] = 1%r.
proof.
proc.
fail wp 1.
wp.
abort.

(* -------------------------------------------------------------------- *)
(* equiv *)

lemma equiv_wp : equiv [M.f ~ M.f : ={a} ==> ={res}].
proof.
proc; wp.
rnd; wp; skip => />.
qed.

lemma equiv_wp_at : equiv [M.f ~ M.f : ={a} ==> ={res}].
proof.
proc; wp 2 2.
rnd; wp 0 0; skip => />.
qed.

(* Asymmetric: different lengths on each side. *)
lemma equiv_wp_asym : equiv [M.f ~ M.e : ={a} ==> true].
proof.
proc; wp 2 2.
rnd; wp; skip => />.
qed.

lemma equiv_wp_errors : equiv [M.f ~ M.f : ={a} ==> ={res}].
proof.
proc.
fail wp 1.           (* a single position: not for equiv *)
fail wp 1 2.         (* remaining on the left *)
fail wp 2 1.         (* remaining on the right *)
fail wp 7 2.         (* invalid position *)
abort.

(* -------------------------------------------------------------------- *)
(* Not a statement judgement. *)
lemma wp_not_stmt : hoare [M.f : true ==> true].
proof.
fail wp.
fail wp 1.
fail wp 1 1.
abort.
