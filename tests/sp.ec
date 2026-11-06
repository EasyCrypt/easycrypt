require import AllCore Distr DBool Xreal.

exception exn1.

module M = {
  var g : int

  proc h() : int = { return 0; }

  proc f(a : int) : int = {
    var x, y, z, b;
    x <- a;
    (y, z) <- (x + 1, x);
    if (x = 0) { y <- 1; } else { y <- 2; z <- 3; }
    g <- y;
    b <$ {0,1};
    x <- x + 1;
    return x + y + z;
  }

  proc k(a : int) : int = {
    var x;
    x <@ h();
    x <- a;
    return x;
  }

  proc e(a : int) : int = {
    var x;
    x <- a;
    g <- x;
    if (x = 0) { raise exn1; }
    return x;
  }
}.

(* -------------------------------------------------------------------- *)
(* hoare *)

lemma hoare_sp_all : hoare [M.f : 0 <= a ==> 0 < res].
proof.
proc; sp.
(* sp stops at the sampling: 2 instructions are left. *)
seq 1 : (0 <= x /\ 0 < y /\ 0 <= z); first by auto => /> /#.
by wp; skip => /> /#.
qed.

lemma hoare_sp_pos : hoare [M.f : 0 <= a ==> 0 < res].
proof.
proc; sp 2; sp 1; sp 0; sp.
by auto => /> /#.
qed.

(* Bound past the sp-able prefix: no progress allowed. *)
lemma hoare_sp_noprogress : hoare [M.f : 0 <= a ==> 0 < res].
proof.
proc.
fail sp 5.
fail sp 1 1.
sp 4.
fail sp 1.
abort.

(* Nothing to do: the statement starts with a call. *)
lemma hoare_sp_none : hoare [M.k : a = 3 ==> res = 3].
proof.
proc; sp.
by inline *; auto.
qed.

(* Exceptional postconditions are kept. *)
lemma hoare_sp_exn : hoare [M.e : true ==> res <> 0 | exn1 => M.g = 0].
proof.
proc; sp 2.
by auto.
qed.

(* -------------------------------------------------------------------- *)
(* phoare *)

lemma phoare_sp_all : phoare [M.f : 0 <= a ==> 0 < res] = 1%r.
proof.
proc; sp.
by auto => />; smt(dbool_ll).
qed.

lemma phoare_sp_le : phoare [M.f : 0 <= a ==> 0 < res] <= 1%r.
proof.
proc; sp 3; sp.
by wp; rnd; skip => />; smt(mu_bounded).
qed.

lemma phoare_sp_noprogress : phoare [M.f : 0 <= a ==> 0 < res] = 1%r.
proof.
proc.
fail sp 5.
fail sp 1 1.
abort.

(* The bound must not be modified by the targeted statement. *)
lemma phoare_sp_bound : phoare [M.f : 0 <= a ==> 0 < res] = (if M.g = 0 then 1%r else 1%r).
proof.
proc.
fail sp.
fail sp 4.
sp 3.
abort.

(* -------------------------------------------------------------------- *)
(* equiv *)

lemma equiv_sp_all : equiv [M.f ~ M.f : ={a} ==> ={res}].
proof.
proc; sp.
by auto => /> /#.
qed.

lemma equiv_sp_pos : equiv [M.f ~ M.f : ={a} ==> ={res}].
proof.
proc; sp 1 0; sp 0 2; sp 3 2; sp.
by auto => /> /#.
qed.

lemma equiv_sp_asym : equiv [M.k ~ M.f : ={a} ==> true].
proof.
proc; sp.
by inline *; auto.
qed.

lemma equiv_sp_noprogress : equiv [M.f ~ M.f : ={a} ==> ={res}].
proof.
proc.
fail sp 5 0.
fail sp 0 5.
fail sp 1.
abort.

(* -------------------------------------------------------------------- *)
(* unsupported goals *)

lemma ehoare_sp : ehoare [M.f : (1%xr) ==> (1%xr)].
proof.
proc.
fail sp.
fail sp 1.
fail sp 1 1.
abort.

lemma hoareF_sp : hoare [M.f : 0 <= a ==> 0 < res].
proof.
fail sp.
abort.
