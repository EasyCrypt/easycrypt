(* The code transformations as program transformations: kill, alias, set
   (`alias p x = e`), set-match (`alias x := pat @ p`), cfold, the split of
   a tuple assignment (`case <-`) and `simplify if`, in every logic (hoare,
   ehoare, phoare, equiv on both sides), at top-level and nested
   positions, and their error paths. Each tactic is a separate sentence,
   so that the goals it leaves can be compared across builds. *)
require import AllCore Distr DBool Xreal.

op d : int distr.
axiom d_ll : is_lossless d.

type t = [A | B of int].

exception oops.

module N = {
  proc h(a : int) : int = {
    return a + 1;
  }
}.

module M = {
  var g : int

  (* straight-line code, a conditional and a match, a loop *)
  proc f(a : int, b : bool, o : t) : int = {
    var x, y, z : int;
    var p : int * int;
    x <- a;
    y <- x + 1;
    z <$ d;
    if (b) {
      z <- y + 1;
      y <- z + y;
    } else {
      z <- 0;
    }
    match o with
    | A => { x <- 2; }
    | B v => { x <- v + y; z <- 3; }
    end;
    p <- (x, y);
    (x, y) <- (y, x);
    while (x < 10) {
      x <- x + 1;
      y <- y + x;
    }
    z <@ N.h(x);
    return x + y;
  }

  (* for kill: dead code, at top-level and nested *)
  proc k(a : int, b : bool) : int = {
    var x, y, z, w : int;
    x <- a;
    y <- x + 1;
    z <- 2;
    if (b) {
      w <- 3;
      z <- w;
    } else {
      w <- 4;
    }
    x <- x + 1;
    return x;
  }

  (* for kill: live code *)
  proc k2(a : int, b : bool) : int = {
    var x, w : int;
    x <- a;
    if (b) {
      w <- 3;
    } else {
      w <- 4;
    }
    x <- x + w;
    return x;
  }

  (* for kill, with an exceptional postcondition *)
  proc ke(a : int) : int = {
    var x : int;
    x <- a;
    g <- 1;
    if (x < 0) { raise oops; }
    return x;
  }

  (* for simplify if: two conditionals over assignments, a nested one *)
  proc s(a : int, b : bool) : int = {
    var x, y : int;
    x <- a;
    if (b) { x <- x + 1; y <- x; } else { y <- 2; }
    if (x < y) { (x, y) <- (y, x); }
    while (0 < x) {
      if (b) { x <- x - 1; } else { x <- x - 2; }
    }
    if (b) { g <- 1; }
    if (b) { x <$ d; }
    if (!b) { x <- 0; } else { x <$ d; }
    return x + y;
  }

  (* for case <-: tuple assignments *)
  proc c(a : int) : int = {
    var x, y : int;
    var p : int * int;
    p <- (a, a + 1);
    (x, y) <- p;
    (x, y) <- (y, a);
    if (0 < x) { (x, y) <- (y + 1, a); }
    return x + y;
  }
}.

(* ==================================================================== *)
(* kill                                                                 *)

lemma hoare_kill : hoare [M.k : true ==> res = 0].
proof.
proc.
kill 2.
by auto.
kill 3.1 ! *.
by auto.
kill 2 ! 2.
by auto.
admit.
qed.

lemma ehoare_kill : ehoare [M.k : 1%xr ==> 1%xr].
proof.
proc.
kill 3.
by auto.
kill 3?1.
by auto.
admit.
qed.

lemma phoare_kill : phoare [M.k : true ==> res = 0] = 1%r.
proof.
proc.
kill 2 ! 2.
by auto.
kill 2.2.
by auto.
admit.
qed.

lemma equiv_kill : equiv [M.k ~ M.k : ={a, b} ==> ={res}].
proof.
proc.
kill {1} 2.
by auto.
kill {2} 4.1 ! 2.
by auto.
kill {2} 2.
by auto.
admit.
qed.

(* The variables read by the exceptional postconditions count: [g]
   cannot be killed when one of them reads it. (Accepted by the builds
   that only look at the main postcondition.) *)
lemma hoare_kill_exn : hoare [M.ke : true ==> true | oops => true].
proof.
proc.
kill 2.
by auto.
by auto.
qed.

lemma hoare_kill_exn_rejected : hoare [M.ke : true ==> true | oops => M.g = 1].
proof.
proc.
fail kill 2.
by auto.
qed.

lemma kill_errors : hoare [M.k2 : true ==> res = 0].
proof.
proc.
fail kill 1.          (* written variable read by the current block *)
fail kill 2.1.        (* written variable read by a parent block *)
fail kill 3.          (* written variable read by the post-condition *)
fail kill 2 ! 3.      (* not enough instructions *)
fail kill 10.         (* invalid code position *)
fail kill 2?3.        (* invalid code position, nested *)
fail kill {1} 2.      (* side on a hoare goal *)
abort.

lemma kill_errors_equiv : equiv [M.k2 ~ M.k2 : ={a, b} ==> ={res}].
proof.
proc.
fail kill 2.          (* no side on an equiv goal *)
fail kill {1} 1.      (* written variable read by the current block *)
fail kill {2} 10.     (* invalid code position *)
abort.

(* ==================================================================== *)
(* alias (assignment, sampling, call) and set                           *)

lemma hoare_alias : hoare [M.f : true ==> true].
proof.
proc.
alias 9.
alias 4.1 with u.
alias 3 with r.
alias 1.
alias 7#B.1 w = y.
alias 6?1 t = 0.
alias 13 e = x + y.
admit.
qed.

lemma ehoare_alias : ehoare [M.f : 1%xr ==> 1%xr].
proof.
proc.
alias 3.
alias 1 t = a.
admit.
qed.

lemma phoare_alias : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
alias 1 with r.
alias 9.1.
alias 1 t = a.
admit.
qed.

lemma equiv_alias : equiv [M.f ~ M.f : ={a, b, o} ==> true].
proof.
proc.
alias {1} 3.
alias {2} 4.1 with u.
alias {2} 9 t = x + 1.
alias {1} 9 t = x + 1.
admit.
qed.

lemma alias_errors : hoare [M.f : true ==> true].
proof.
proc.
fail alias 4.             (* not an assignment, sampling or call *)
fail alias 20.            (* invalid code position *)
fail alias 4?2.           (* invalid code position, nested *)
fail alias 20 t = x.      (* invalid code position (set) *)
fail alias {1} 1.         (* side on a hoare goal *)
abort.

(* ==================================================================== *)
(* set-match                                                            *)

lemma hoare_set_match : hoare [M.f : true ==> true].
proof.
proc.
alias c := (x + _) @ 2.
alias e := (_ + 1) @ 5.1.
alias f := b @ 5.
alias h := (o) @ 7.
admit.
qed.

lemma ehoare_set_match : ehoare [M.f : 1%xr ==> 1%xr].
proof.
proc.
alias c := (_ + 1) @ 2.
admit.
qed.

lemma phoare_set_match : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
alias c := (x, y) @ 6.
admit.
qed.

lemma equiv_set_match : equiv [M.f ~ M.f : ={a, b, o} ==> true].
proof.
proc.
alias {1} c := (x + _) @ 2.
alias {2} c := (_ + y) @ 4.2.
admit.
qed.

lemma set_match_errors : hoare [M.f : true ==> true].
proof.
proc.
fail alias c := (x * _) @ 2.     (* no occurrence *)
fail alias c := (_ < 10) @ 8.    (* while loop *)
fail alias c := a @ 9.           (* no expression *)
fail alias c := a @ 20.          (* invalid code position *)
abort.

(* ==================================================================== *)
(* cfold                                                                *)

lemma hoare_cfold : hoare [M.f : true ==> true].
proof.
proc.
cfold 1.
cfold 3.1 1.
admit.
qed.

lemma hoare_cfold_eager : hoare [M.f : true ==> true].
proof.
proc.
cfold* 1.
admit.
qed.

lemma ehoare_cfold : ehoare [M.f : 1%xr ==> 1%xr].
proof.
proc.
cfold 1 1.
admit.
qed.

lemma phoare_cfold : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
cfold 1.
admit.
qed.

lemma equiv_cfold : equiv [M.f ~ M.f : ={a, b, o} ==> true].
proof.
proc.
cfold {1} 1.
cfold* {2} 2.
admit.
qed.

lemma cfold_errors : hoare [M.f : true ==> true].
proof.
proc.
fail cfold 3.            (* not an assignment *)
fail cfold 1 20.         (* not enough instructions *)
fail cfold 20.           (* invalid code position *)
abort.

(* ==================================================================== *)
(* case <- (split of a tuple assignment)                                *)

lemma hoare_asgn_case : hoare [M.c : true ==> true].
proof.
proc.
case <- 2.
case <- 4.
case <- 6.1.
case <- 1.
admit.
qed.

lemma ehoare_asgn_case : ehoare [M.c : 1%xr ==> 1%xr].
proof.
proc.
case <- 3.
admit.
qed.

lemma phoare_asgn_case : phoare [M.c : true ==> true] = 1%r.
proof.
proc.
case <- 4.1.
admit.
qed.

lemma equiv_asgn_case : equiv [M.c ~ M.c : ={a} ==> true].
proof.
proc.
case <- {1} 2.
case <- {2} 3.
admit.
qed.

lemma asgn_case_errors : hoare [M.c : true ==> true].
proof.
proc.
fail case <- 4.          (* not an assignment *)
abort.

(* ==================================================================== *)
(* simplify if                                                          *)

lemma hoare_simplify_if : hoare [M.s : true ==> true].
proof.
proc.
simplify if 2.
simplify if 4.1.
simplify if 5.
admit.
qed.

lemma hoare_simplify_if_all : hoare [M.s : true ==> true].
proof.
proc.
simplify if.
admit.
qed.

lemma ehoare_simplify_if : ehoare [M.s : 1%xr ==> 1%xr].
proof.
proc.
simplify if 3.
admit.
qed.

lemma phoare_simplify_if : phoare [M.s : true ==> true] = 1%r.
proof.
proc.
simplify if.
admit.
qed.

lemma equiv_simplify_if : equiv [M.s ~ M.s : ={a, b} ==> true].
proof.
proc.
simplify if {1} 2.
simplify if {2}.
admit.
qed.

lemma simplify_if_errors : hoare [M.s : true ==> true].
proof.
proc.
fail simplify if 1.      (* not a conditional *)
fail simplify if 6.      (* then branch: not only assignments *)
fail simplify if 7.      (* else branch: not only assignments *)
fail simplify if 20.     (* invalid code position *)
abort.
