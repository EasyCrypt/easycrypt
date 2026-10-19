(* The program-transformation rules (one per logic), through the `rndsem`
   transformation: hoare, phoare and equiv (both sides, and the two-sided
   `rnd : k k'` form), the reduced (`*`) form, the case where no sampled
   variable is left (a fresh `unit` variable is sampled), and the error
   paths. Each tactic is a separate sentence, so that the goals it leaves
   can be compared across builds. *)
require import AllCore Distr DBool Xreal.

op d : int distr.
axiom d_ll : is_lossless d.

exception e.

module M = {
  var g : int

  proc f() : int = {
    var x, y, z : int;
    y <- 1;
    x <$ d;
    z <- x + y;
    x <- z;
    return x;
  }

  proc t() : int * bool = {
    var x : int;
    var b : bool;
    b <$ {0,1};
    x <$ d;
    (x, b) <- (x + 1, !b);
    return (x, b);
  }

  proc u() : unit = {
    var x : int;
    x <$ d;
    x <- x + 1;
  }

  proc gw() : int = {
    var x : int;
    x <$ d;
    g <- x;
    return x;
  }

  proc c() : int = {
    var x : int;
    x <$ d;
    if (x = 0) x <- 1;
    return x;
  }

  proc w() : int = {
    var x : int;
    x <- 0;
    while (x < 10) x <- x + 1;
    x <$ d;
    x <- x + 1;
    return x;
  }
}.

(* -------------------------------------------------------------------- *)
(* hoare *)
lemma h_full : hoare [M.f : true ==> res - 1 \in d].
proof.
proc.
rndsem 0.
rnd.
by skip => /> v; rewrite supp_dmap => -[x [? ->]] /#.
qed.

lemma h_suffix : hoare [M.f : true ==> res - 1 \in d].
proof.
proc.
rndsem 1.
rnd.
by wp; skip => /> v; rewrite supp_dmap => -[x [? ->]] /#.
qed.

lemma h_reduce : hoare [M.t : true ==> 0 < res.`1 + 1 \/ true].
proof.
proc.
rndsem* 0.
rnd.
by skip.
qed.

lemma h_tuple : hoare [M.t : true ==> true].
proof.
proc.
rndsem 0.
rnd.
by skip.
qed.

lemma h_unit : hoare [M.u : true ==> true].
proof.
proc.
rndsem* 0.
rnd.
by skip.
qed.

lemma h_while : hoare [M.w : true ==> true].
proof.
proc.
rndsem 2.
rnd.
while true.
- by wp; skip.
by wp; skip.
qed.

lemma h_global : hoare [M.gw : true ==> true].
proof.
proc.
rndsem 0.
rnd.
by skip.
qed.

lemma h_errors : hoare [M.c : true ==> true].
proof.
proc.
fail rndsem 0.         (* not straight-line *)
fail rndsem{1} 0.      (* no side on hoare goals *)
fail rndsem 3.         (* invalid position *)
rndsem 2.              (* empty suffix: a fresh unit variable *)
abort.

lemma h_errors_while : hoare [M.w : true ==> true].
proof.
proc.
fail rndsem 0.
fail rndsem 1.
abort.

lemma h_errors_exn : hoare [M.f : true ==> true | e => true].
proof.
proc.
fail rndsem 0.         (* exceptions are not supported *)
abort.

(* -------------------------------------------------------------------- *)
(* phoare *)
lemma bd_full : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
rndsem 0.
rnd.
by skip => />; smt(dmap_ll dbool_ll d_ll).
qed.

lemma bd_suffix : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
rndsem 1.
rnd.
by wp; skip => />; smt(dmap_ll dbool_ll d_ll).
qed.

lemma bd_reduce : phoare [M.t : true ==> true] = 1%r.
proof.
proc.
rndsem* 1.
rnd.
rnd.
by skip => />; smt(dmap_ll dbool_ll d_ll).
qed.

lemma bd_le : phoare [M.u : true ==> true] <= 1%r.
proof.
proc.
rndsem 0.
rnd.
by skip => /> /#.
qed.

lemma bd_errors : phoare [M.c : true ==> true] = 1%r.
proof.
proc.
fail rndsem 0.
fail rndsem{2} 0.
abort.

(* -------------------------------------------------------------------- *)
(* equiv *)
lemma eq_left : equiv [M.f ~ M.f : true ==> ={res}].
proof.
proc.
rndsem{1} 1.
rndsem{2} 1.
rnd.
by wp; skip.
qed.

lemma eq_right_reduce : equiv [M.t ~ M.t : true ==> ={res}].
proof.
proc.
rndsem*{2} 0.
rndsem{1} 0.
rnd.
by skip.
qed.

lemma eq_unit : equiv [M.u ~ M.u : true ==> true].
proof.
proc.
rndsem*{1} 0.
rndsem*{2} 0.
rnd.
by skip.
qed.

lemma eq_rnd_pos : equiv [M.f ~ M.f : true ==> ={res}].
proof.
proc.
rnd : 1 1.
by wp; skip.
qed.

lemma eq_rnd_pos_reduce : equiv [M.t ~ M.t : true ==> res{1}.`1 = res{2}.`1].
proof.
proc.
rnd : *1 *1.
rnd.
by skip.
qed.

lemma eq_rnd_pos_single : equiv [M.f ~ M.f : true ==> ={res}].
proof.
proc.
rnd : *1.
by wp; skip.
qed.

lemma eq_errors : equiv [M.c ~ M.w : true ==> true].
proof.
proc.
fail rndsem 0.         (* side required *)
fail rndsem{1} 0.      (* not straight-line *)
fail rndsem{2} 0.      (* not straight-line *)
fail rnd : 0 2.
rndsem{2} 2.
abort.

(* -------------------------------------------------------------------- *)
(* no rndsem on ehoare goals *)
lemma eh_errors : ehoare [M.f : (1%xr) ==> (1%xr)].
proof.
proc.
fail rndsem 0.
abort.
