(* The `rnd` and `rndsem` tactics, in every logic and form, with their
   failing cases. Each `rnd` is a separate sentence, so that the goals it
   leaves can be compared across builds. *)
require import AllCore Distr DBool Xreal.

op d : int distr.
axiom d_ll : is_lossless d.

exception e.

module H = {
  var g : int

  proc f() : int = {
    var x, y : int;
    y <- 1;
    x <$ d;
    return x + y;
  }

  proc s() : int = {
    var x : int;
    x <$ d;
    return x;
  }

  proc b() : bool = {
    var x : bool;
    x <$ {0,1};
    return x;
  }

  proc t() : int * int = {
    var x, y : int;
    (x, y) <$ d `*` d;
    return (x, y);
  }

  proc nr() : int = {
    var x : int;
    x <$ d;
    x <- x + 1;
    return x;
  }

  proc w() : int = {
    var x : int;
    g <- 0;
    x <$ d;
    return x;
  }

  proc sem() : int = {
    var x, y : int;
    y <- 1;
    x <$ d;
    x <- x + y;
    return x;
  }

  proc semg() : int = {
    var x : int;
    x <$ d;
    g <- x;
    return x;
  }

  proc semc() : int = {
    var x : int;
    x <$ d;
    if (x = 0) x <- 1;
    return x;
  }

  proc z() : int = {
    return 0;
  }

  proc pb() : unit = {
    var x : bool;
    g <- 1;
    x <$ {0,1};
  }

  proc pbx() : bool = {
    var x : bool;
    g <- 1;
    x <$ {0,1};
    return x;
  }
}.

(* -------------------------------------------------------------------- *)
(* hoare *)
lemma hoare_rnd : hoare [H.f : true ==> res - 1 \in d].
proof.
proc.
rnd.
by wp; skip => /> v hv; smt().
qed.

lemma hoare_rnd_single : hoare [H.s : true ==> res \in d].
proof.
proc.
rnd.
by skip => />.
qed.

lemma hoare_rnd_errors : hoare [H.nr : true ==> true].
proof.
proc.
fail rnd.             (* the last instruction is not a sampling *)
fail rnd (fun _ => true).
fail rnd{1}.
abort.

lemma hoare_rnd_exn : hoare [H.s : true ==> true | e => true].
proof.
proc.
fail rnd.             (* exceptions are not supported *)
abort.

(* -------------------------------------------------------------------- *)
(* ehoare *)
lemma ehoare_rnd : ehoare [H.s : (Ep d (fun v => (v = 0)%xr)) ==> (res = 0)%xr].
proof.
proc.
rnd.
by skip.
qed.

lemma ehoare_rnd_errors : ehoare [H.nr : (1%xr) ==> (1%xr)].
proof.
proc.
fail rnd.
fail rnd (fun _ => true).
abort.

(* -------------------------------------------------------------------- *)
(* bdhoare *)

(* (1) <=, no event, the post does not mention the sampled variable. *)
lemma bd_le_indep : phoare [H.pb : true ==> H.g = 2] <= 0%r.
proof.
proc.
rnd.
by hoare; wp; skip.
qed.

(* (2) <=, inferred event; the non-negativity premise is closed. *)
lemma bd_le_infer : phoare [H.pbx : true ==> res] <= 1%r.
proof.
proc.
rnd.
by wp; skip => />; smt(le1_mu).
qed.

(* (2) <=, given event; the non-negativity premise is left open. *)
lemma bd_le_event : phoare [H.pbx : true ==> res] <= (1%r/2%r).
proof.
proc.
rnd (pred1 true).
+ by wp; skip => />; smt(dbool1E).
+ by move=> &hr; smt().
qed.

(* (2) <=, a bound written by the prefix (generalized), whose
   non-negativity premise is not closed. *)
lemma bd_le_dep : phoare [H.pbx : true ==> res] <= (H.g%r / 2%r).
proof.
proc.
rnd (pred1 true).
abort.

(* (3) = and >=, no event, the post does not mention the sampled variable. *)
lemma bd_eq_indep : phoare [H.pb : true ==> H.g = 1] = 1%r.
proof.
proc.
rnd.
by wp; skip => />; apply dbool_ll.
qed.

lemma bd_ge_indep : phoare [H.pb : true ==> H.g = 1] >= 1%r.
proof.
proc.
rnd.
by wp; skip => />; apply dbool_ll.
qed.

(* (4) = and >=, inferred and given event. *)
lemma bd_eq_infer : phoare [H.pbx : true ==> res] = (1%r/2%r).
proof.
proc.
rnd.
by wp; skip => />; smt(dbool1E).
qed.

lemma bd_ge_event : phoare [H.pbx : true ==> res] >= (1%r/2%r).
proof.
proc.
rnd (pred1 true).
by wp; skip => />; smt(dbool1E).
qed.

(* (5) phi d1 d2 d3 d4, without and with event. *)
lemma bd_split : phoare [H.pbx : true ==> res] = (1%r/2%r).
proof.
proc.
rnd true 1%r (1%r/2%r) 0%r 1%r.
abort.

lemma bd_split_event : phoare [H.pbx : true ==> res] <= (1%r/2%r).
proof.
proc.
rnd true 1%r (1%r/2%r) 0%r 1%r (pred1 true).
abort.

(* A tuple sampling: the event cannot be inferred. *)
lemma bd_tuple : phoare [H.t : true ==> res.`1 = 0] <= 1%r.
proof.
proc.
fail rnd.
rnd (fun (p : int * int) => p.`1 = 0).
by skip => />; smt(le1_mu).
qed.

lemma bd_errors : phoare [H.pbx : true ==> res] = (1%r/2%r).
proof.
proc.
fail rnd (pred1 true) (pred1 true).
fail rnd{1}.
fail rnd : 0.
abort.

(* -------------------------------------------------------------------- *)
(* equiv, two-sided *)
lemma eq_rnd_id : equiv [H.b ~ H.b : true ==> ={res}].
proof.
proc.
rnd.
by skip => />.
qed.

lemma eq_rnd_prefix : equiv [H.f ~ H.f : true ==> ={res}].
proof.
proc.
rnd.
by wp; skip => />.
qed.

lemma eq_rnd_bij : equiv [H.b ~ H.b : true ==> res{1} = !res{2}].
proof.
proc.
rnd (fun b => !b).
by skip => />.
qed.

lemma eq_rnd_bij2 : equiv [H.b ~ H.b : true ==> res{1} = !res{2}].
proof.
proc.
rnd (fun b => !b) (fun b => !b).
by skip => />.
qed.

lemma eq_rnd_errors : equiv [H.b ~ H.s : true ==> true].
proof.
proc.
fail rnd.              (* incompatible supports *)
fail rnd{1} (fun b => b).
fail rnd{1} : 0.
abort.

(* two-sided, after rndsem on both sides *)
lemma eq_rnd_pos : equiv [H.sem ~ H.sem : true ==> ={res}].
proof.
proc.
rnd : 1 1.
by wp; skip => />.
qed.

lemma eq_rnd_pos1 : equiv [H.sem ~ H.sem : true ==> ={res}].
proof.
proc.
rnd : *1.
by wp; skip => />.
qed.

(* equiv, one-sided *)
lemma eq_rnd_left : equiv [H.s ~ H.b : true ==> true].
proof.
proc.
rnd{1}.
rnd{2}.
by skip => />; smt(d_ll).
qed.

lemma eq_rnd_right : equiv [H.b ~ H.f : true ==> true].
proof.
proc.
rnd{2}.
wp.
rnd{1}.
by skip => />; smt(d_ll).
qed.

(* auto *)
lemma eq_auto : equiv [H.b ~ H.b : true ==> ={res}].
proof.
proc.
by auto.
qed.

lemma eq_auto_onesided : equiv [H.s ~ H.z : true ==> true].
proof.
proc.
by auto => />; apply d_ll.
qed.

lemma bd_auto : phoare [H.pbx : true ==> true] = 1%r.
proof.
proc.
by auto => />; apply dbool_ll.
qed.

(* -------------------------------------------------------------------- *)
(* rndsem *)
lemma hoare_rndsem : hoare [H.sem : true ==> res - 1 \in d].
proof.
proc.
rndsem 1.
rnd.
wp; skip => /> v.
by rewrite supp_dmap => -[x [? ->]] /#.
qed.

lemma hoare_rndsem_red : hoare [H.sem : true ==> true].
proof.
proc.
rndsem* 0.
rnd.
by skip.
qed.

lemma bd_rndsem : phoare [H.sem : true ==> true] = 1%r.
proof.
proc.
rndsem 0.
rnd.
by skip => />; smt(dmap_ll d_ll).
qed.

lemma eq_rndsem : equiv [H.sem ~ H.sem : true ==> ={res}].
proof.
proc.
rndsem{1} 1.
rndsem*{2} 1.
rnd.
by wp; skip.
qed.

lemma rndsem_global : hoare [H.semg : true ==> true].
proof.
proc.
fail rndsem{1} 0.
rndsem 0.
rnd.
by skip.
qed.

lemma rndsem_errors_if : hoare [H.semc : true ==> true].
proof.
proc.
fail rndsem 0.         (* not straight-line *)
abort.

lemma rndsem_errors_exn : hoare [H.sem : true ==> true | e => true].
proof.
proc.
fail rndsem 0.         (* exceptions are not supported *)
abort.

lemma rndsem_errors_eq : equiv [H.sem ~ H.sem : true ==> true].
proof.
proc.
fail rndsem 0.
abort.

lemma rndsem_errors_eh : ehoare [H.sem : (1%xr) ==> (1%xr)].
proof.
proc.
fail rndsem 0.
abort.
