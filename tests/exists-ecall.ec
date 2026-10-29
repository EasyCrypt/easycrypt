(* The existential rules on program-logic judgements: `elim*`
   (eliminating the existentials of the precondition), `exists*` and
   `exlim` (quantifying the precondition over the values of formulas), in
   every logic, on statements and on procedures; then `ecall` (hoare
   forward and backward, phoare backward, equiv on both sides and on one
   side); and the error paths. Each tactic is a separate sentence, so that
   the goals it leaves can be compared across builds. *)
require import AllCore Xreal.

module M = {
  var g : int

  proc f(x : int) : int = {
    return x + 1;
  }

  proc h(x : int) : int = {
    x <@ f(x);
    x <- x + M.g;
    return x;
  }

  proc k(x : int) : int = {
    var y : int;
    y <- x;
    x <@ f(x);
    return x + y;
  }

  proc u() : unit = {
    M.g <- M.g + 1;
  }
}.

(* ==================================================================== *)
(* elim* *)

(* -------------------------------------------------------------------- *)
(* hoare *)
lemma L_elim_hoareF : hoare [M.f : exists y, x = y /\ 0 <= y ==> 0 < res].
proof.
elim*.
move=> y.
proc.
by auto=> /#.
qed.

(* binders under a conjunction, all eliminated *)
lemma L_elim_hoareS :
  hoare [M.f : (exists y, x = y /\ 0 <= y) /\ (exists z, z = M.g) ==> 0 < res].
proof.
proc.
elim*.
move=> y z.
by auto=> /#.
qed.

(* no existential: the goal is unchanged *)
lemma L_elim_hoare_none : hoare [M.f : 0 <= x ==> 0 < res].
proof.
proc.
elim*.
by auto=> /#.
qed.

(* -------------------------------------------------------------------- *)
(* ehoare *)
lemma L_elim_ehoareF :
  ehoare [M.u : (exists y, M.g = y) `|` (M.g + 1)%xr ==> M.g%xr].
proof.
elim*.
move=> y.
proc.
by auto=> &hr; apply xle_cxr_r.
qed.

lemma L_elim_ehoareS :
  ehoare [M.u : (exists y z, M.g = y /\ z = y) `|` (M.g + 1)%xr ==> M.g%xr].
proof.
proc.
elim*.
move=> y z.
by auto=> &hr; apply xle_cxr_r.
qed.

(* -------------------------------------------------------------------- *)
(* phoare *)
lemma L_elim_bdhoareF :
  phoare [M.f : exists y, x = y /\ 0 <= y ==> 0 < res] = 1%r.
proof.
elim*.
move=> y.
proc.
by auto=> /#.
qed.

lemma L_elim_bdhoareS :
  phoare [M.f : exists y, x = y /\ 0 <= y ==> 0 < res] <= 1%r.
proof.
proc.
elim*.
move=> y.
by auto.
qed.

(* -------------------------------------------------------------------- *)
(* equiv *)
lemma L_elim_equivF :
  equiv [M.f ~ M.f : exists y, x{1} = y /\ x{2} = y ==> ={res}].
proof.
elim*.
move=> y.
proc.
by auto.
qed.

lemma L_elim_equivS :
  equiv [M.f ~ M.f :
    0 <= x{1} /\ (0 <= x{1} => exists y, x{1} = y /\ x{2} = y) ==> ={res}].
proof.
proc.
elim*.
move=> y.
by auto=> /#.
qed.

(* ==================================================================== *)
(* exists* / exlim *)

(* -------------------------------------------------------------------- *)
(* hoare *)
lemma L_intro_hoareF : hoare [M.f : 0 <= x ==> 0 < res].
proof.
exists* x.
elim*.
move=> x0.
proc.
by auto=> /#.
qed.

lemma L_intro_hoareS : hoare [M.f : 0 <= x ==> 0 < res].
proof.
proc.
exlim x, M.g => x0 g0.
by auto=> /#.
qed.

(* -------------------------------------------------------------------- *)
(* ehoare *)
lemma L_intro_ehoareF : ehoare [M.u : (M.g + 1)%xr ==> M.g%xr].
proof.
exists* M.g.
elim*.
move=> g0.
proc.
by auto=> &hr; apply xle_cxr_r.
qed.

lemma L_intro_ehoareS : ehoare [M.u : (M.g + 1)%xr ==> M.g%xr].
proof.
proc.
exlim M.g => g0.
by auto=> &hr; apply xle_cxr_r.
qed.

(* -------------------------------------------------------------------- *)
(* phoare *)
lemma L_intro_bdhoareF : phoare [M.f : 0 <= x ==> 0 < res] = 1%r.
proof.
exlim x => x0.
proc.
by auto=> /#.
qed.

lemma L_intro_bdhoareS : phoare [M.f : 0 <= x ==> 0 < res] = 1%r.
proof.
proc.
exists* x, (x + 1).
elim*.
move=> x0 x1.
by auto=> /#.
qed.

(* -------------------------------------------------------------------- *)
(* equiv *)
lemma L_intro_equivF : equiv [M.f ~ M.f : ={x} ==> ={res}].
proof.
exlim x{1}, x{2} => x1 x2.
proc.
by auto.
qed.

lemma L_intro_equivS : equiv [M.f ~ M.f : ={x} ==> ={res}].
proof.
proc.
exists* x{1}.
elim*.
move=> x1.
by auto.
qed.

(* -------------------------------------------------------------------- *)
(* not a program-logic goal *)
lemma L_exists_err : true.
proof.
fail elim*.
fail exists* 0.
fail exlim 0 => x.
by [].
qed.

(* ==================================================================== *)
(* ecall *)

lemma f_spec (x0 : int) : hoare [M.f : x = x0 ==> res = x0 + 1].
proof. by proc; auto. qed.

lemma f_spec_nox : hoare [M.f : 0 <= x ==> 0 < res].
proof. by proc; auto=> /#. qed.

lemma u_spec : hoare [M.u : true ==> true].
proof. by proc; auto. qed.

lemma f_pspec (x0 : int) : phoare [M.f : x = x0 ==> res = x0 + 1] = 1%r.
proof. by proc; auto. qed.

lemma f_pspec_le (x0 : int) : phoare [M.f : x = x0 ==> res = x0 + 1] <= 1%r.
proof. by proc; auto. qed.

lemma f_espec (x0 : int) :
  equiv [M.f ~ M.f : ={x} /\ x{1} = x0 ==> ={res} /\ res{1} = x0 + 1].
proof. by proc; auto. qed.

exception E.

lemma f_spec_exn (x0 : int) :
  hoare [M.f : x = x0 ==> res = x0 + 1 | E => false].
proof. by proc; auto. qed.

(* -------------------------------------------------------------------- *)
(* hoare, forward: an argument abstracting a program variable, and the
   framing of the precondition *)
lemma L_ecall_fwd : hoare [M.h : 0 <= x /\ M.g = 0 ==> M.g = 0].
proof.
proc.
ecall ->> (f_spec x).
- by move=> x_ &hr />.
move=> x_.
by auto.
qed.

(* hoare, backward *)
lemma L_ecall_bwd : hoare [M.k : 0 <= x ==> 0 < res].
proof.
proc.
ecall (f_spec x).
by auto=> /#.
qed.

(* hoare, backward, no argument *)
lemma L_ecall_bwd_nox : hoare [M.k : 0 <= x ==> 0 < res].
proof.
proc.
ecall (f_spec_nox).
by auto=> /#.
qed.

(* hoare, backward, a contract with an exceptional postcondition *)
lemma L_ecall_bwd_exn : hoare [M.k : 0 <= x ==> 0 < res].
proof.
proc.
ecall (f_spec_exn x).
by auto=> /#.
qed.

(* hoare, errors *)
lemma L_ecall_hoare_err : hoare [M.h : 0 <= x ==> 0 < res].
proof.
proc.
fail ecall{1} (f_spec x).
fail ecall ->> (f_spec_exn x).
fail ecall ->> (u_spec).
fail ecall ->> (f_pspec x).
fail ecall ->> (f_espec x).
fail ecall (f_spec x).
abort.

lemma L_ecall_hoareF_err : hoare [M.h : 0 <= x ==> 0 < res].
proof.
fail ecall (f_spec x).
abort.

(* -------------------------------------------------------------------- *)
(* phoare, backward *)
lemma L_ecall_phoare : phoare [M.k : 0 <= x ==> 0 < res] = 1%r.
proof.
proc.
ecall (f_pspec x).
by auto=> /#.
qed.

(* phoare, errors *)
lemma L_ecall_phoare_err : phoare [M.k : 0 <= x ==> 0 < res] = 1%r.
proof.
proc.
fail ecall{1} (f_pspec x).
fail ecall ->> (f_pspec x).
fail ecall (f_pspec_le x).
fail ecall (u_spec).
fail ecall (f_espec x).
(* a hoare contract passes the contract check, then fails (an anomaly) *)
fail ecall (f_spec x).
abort.

lemma L_ecall_phoare_le_err : phoare [M.k : 0 <= x ==> 0 < res] <= 1%r.
proof.
proc.
fail ecall (f_pspec x).
abort.

(* -------------------------------------------------------------------- *)
(* equiv, both sides *)
lemma L_ecall_equiv : equiv [M.k ~ M.k : ={x} ==> ={res}].
proof.
proc.
ecall (f_espec x{1}).
by auto.
qed.

(* equiv, one side at a time *)
lemma L_ecall_equiv1 : equiv [M.k ~ M.k : ={x} ==> ={res}].
proof.
proc.
ecall{1} (f_pspec x{1}).
ecall{2} (f_pspec x{2}).
by auto=> /#.
qed.

(* equiv, errors *)
lemma L_ecall_equiv_err : equiv [M.k ~ M.k : ={x} ==> ={res}].
proof.
proc.
fail ecall ->> (f_espec x{1}).
fail ecall (f_pspec x{1}).
fail ecall{1} (f_espec x{1}).
fail ecall{1} (u_spec).
fail ecall{1} (f_spec x{1}).
abort.

(* -------------------------------------------------------------------- *)
(* not a hoare, phoare or equiv goal on a statement *)
lemma L_ecall_ehoare_err : ehoare [M.u : (M.g + 1)%xr ==> M.g%xr].
proof.
proc.
fail ecall (u_spec).
abort.
