(* The `call` tactic in every logic: a `seq` before the call(s) and the
   call rule of the logic on the call alone (the bdhoare rule keeps its
   composite statement). Run with EC_RECHECK=1 to recheck the rules. *)
require import AllCore Distr DBool Xreal.

module G = { var g : int  var b : bool }.

module M = {
  proc f(x : int) : int = { G.g <- G.g + x; return G.g; }

  proc h() = { G.g <- G.g + 1; }

  proc main(y : int) : int = {
    var r;
    G.g <- 0;
    r <@ f(y);
    return r;
  }

  proc single(y : int) : int = {
    var r;
    r <@ f(y);
    return r;
  }

  proc proc_h() = { h(); }

  proc bool_f() : bool = { var b; b <$ {0,1}; return b; }

  proc bool_main() : bool = { var r; G.g <- 0; r <@ bool_f(); return r; }
}.

module type O = { proc o() : unit }.
module type A (O : O) = { proc a() : unit }.

module O = { proc o() = { G.g <- G.g + 1; } }.

module Main (A : A) = {
  proc main() = { G.g <- 0; A(O).a(); }
}.

(* -------------------------------------------------------------------- *)
(* hoare *)
lemma f_spec (z w : int) : hoare [M.f : G.g = z /\ x = w ==> res = z + w /\ G.g = res].
proof. proc; auto. qed.

lemma h_spec : hoare [M.h : true ==> true].
proof. by proc; auto. qed.

lemma bool_f_ll : phoare [M.bool_f : true ==> true] = 1%r.
proof. by proc; auto; rewrite dbool_ll. qed.

lemma hoare_spec : hoare [M.main : 0 <= y ==> 0 <= res].
proof.
proc.
call (_ : 0 <= x /\ 0 <= G.g ==> 0 <= res).
+ by proc; auto => /#.
by auto.
qed.

lemma hoare_lemma (w : int) : hoare [M.main : y = w ==> res = w].
proof.
proc.
call (f_spec 0 w).
by auto => /#.
qed.

lemma hoare_single (w : int) : hoare [M.single : y = w /\ G.g = 0 ==> res = w].
proof.
proc.
call (f_spec 0 w).
by skip => /#.
qed.

lemma hoare_inv_concrete : hoare [M.proc_h : 0 <= G.g ==> 0 <= G.g].
proof.
proc.
call (: 0 <= G.g).
+ by auto => /#.
by auto.
qed.

lemma hoare_inv_abs (A <: A {-G}) : hoare [Main(A).main : true ==> 0 <= G.g].
proof.
proc.
call (: 0 <= G.g).
+ by proc; auto => /#.
by auto.
qed.

(* exceptional postconditions *)
exception E.

module X = {
  proc r(x : int) : int = { if (0 <= x) else raise E; return x; }

  proc m(y : int) : int = { var r; G.g <- y; r <@ r(y); return r; }
}.

lemma hoare_exn : hoare [X.m : true ==> 0 <= res | E => G.g < 0].
proof.
proc.
call (_ : x = G.g ==> 0 <= res | E => G.g < 0).
+ by proc; auto => /#.
by auto.
qed.

lemma hoare_errors : hoare [M.main : true ==> true].
proof.
proc.
fail call{1} (_ : true ==> true).
fail call{1} (: true).
fail call (: G.b, true).
fail call h_spec.
fail call bool_f_ll.
abort.

lemma hoare_not_call : hoare [M.h : true ==> true].
proof.
proc.
fail call (_ : true ==> true).
fail call (: true).
abort.

(* -------------------------------------------------------------------- *)
(* ehoare *)
lemma ehoare_spec : ehoare [M.main : (0 <= y)%xr ==> (0 <= res)%xr].
proof.
proc.
call (_ : (0 <= G.g + x)%xr ==> (0 <= res)%xr).
+ by proc; auto.
by auto.
qed.

lemma ehoare_inv (A <: A {-G}) : ehoare [Main(A).main : 1%xr ==> (G.g < 0)%xr].
proof.
proc.
call (: (G.g < 0)%xr).
+ by proc; auto => &hr /#.
by auto.
qed.

lemma f_espec : ehoare [M.f : (0 <= G.g + x)%xr ==> (0 <= res)%xr].
proof. by proc; auto. qed.

lemma ehoare_concave : ehoare [M.main : (0 <= y)%xr ==> (0 <= res)%xr].
proof.
proc.
call /(fun x => x) f_espec.
by auto.
qed.

lemma ehoare_concave_inv (A <: A {-G}) : ehoare [Main(A).main : 1%xr ==> (G.g < 0)%xr].
proof.
proc.
call /(fun x => x) (: (G.g < 0)%xr).
+ by proc; auto => &hr /#.
by auto.
qed.

lemma ehoare_errors : ehoare [M.main : 1%xr ==> 1%xr].
proof.
proc.
fail call{1} (_ : 1%xr ==> 1%xr).
(* the post-expectation of the procedure must be the one of the goal *)
fail call (_ : 1%xr ==> (res = 0)%xr).
abort.

module N = {
  proc k(y : int) = { G.g <@ M.f(y); }

  proc k2(y : int) = { M.f(y); }
}.

(* only local variables on the left of the call *)
lemma ehoare_glob_lv : ehoare [N.k : 1%xr ==> 1%xr].
proof.
proc.
fail call (_ : 1%xr ==> 1%xr).
abort.

(* no left-value: the post-expectation cannot read [res] *)
lemma ehoare_res_nolv : ehoare [N.k2 : 1%xr ==> 1%xr].
proof.
proc.
fail call (_ : 1%xr ==> (res = 0)%xr).
abort.

(* -------------------------------------------------------------------- *)
(* bdhoare *)
lemma bool_f_spec : phoare [M.bool_f : true ==> res] = (1%r / 2%r).
proof. by proc; rnd; skip => />; rewrite dboolE. qed.

lemma bdhoare_eq : phoare [M.bool_main : true ==> res] = (1%r / 2%r).
proof.
proc.
call bool_f_spec.
by auto.
qed.

lemma bdhoare_le : phoare [M.bool_main : true ==> res] <= (1%r / 2%r).
proof.
proc.
call (_ : true ==> res).
+ proc; rnd; 2: by move=> _ /#.
  by skip => />; rewrite dboolE.
by auto.
qed.

lemma bdhoare_ge : phoare [M.bool_main : true ==> res] >= (1%r / 2%r).
proof.
proc.
call (_ : true ==> res).
+ by proc; rnd; skip => />; rewrite dboolE.
by auto.
qed.

lemma bdhoare_inv : phoare [M.proc_h : 0 <= G.g ==> 0 <= G.g] = 1%r.
proof.
proc.
call (: 0 <= G.g).
+ by auto => /#.
by auto.
qed.

lemma bdhoare_errors : phoare [M.bool_main : true ==> res] = (1%r / 2%r).
proof.
proc.
fail call{1} (_ : true ==> res).
fail call{1} (: true).
fail call (: G.b, true).
fail call h_spec.
fail call bool_f_ll.
abort.

lemma bdhoare_not_call : phoare [M.h : true ==> true] = 1%r.
proof.
proc.
fail call (_ : true ==> true).
abort.

(* the bound cannot depend on local variables (#1189) *)
lemma bdhoare_local_bound : phoare [M.single : true ==> true] <= (b2r (y = 0)).
proof.
proc.
fail call (_ : true ==> true).
abort.

(* -------------------------------------------------------------------- *)
(* equiv, two-sided *)
lemma equiv_spec : equiv [M.main ~ M.main : ={y} ==> ={res}].
proof.
proc.
call (_ : ={x, G.g} ==> ={res}).
+ by proc; auto.
by auto.
qed.

lemma equiv_inv : equiv [M.main ~ M.main : ={y} ==> ={res, G.g}].
proof.
proc.
call (: ={G.g}).
+ by auto.
by auto.
qed.

lemma equiv_inv_abs (A <: A {-G}) : equiv [Main(A).main ~ Main(A).main : ={glob A} ==> ={G.g}].
proof.
proc.
call (: ={G.g}).
+ by proc; auto.
by auto.
qed.

lemma equiv_upto (A <: A {-G}) :
  (forall (O0 <: O{-A}), islossless O0.o => islossless A(O0).a) =>
  equiv [Main(A).main ~ Main(A).main : ={glob A} ==> G.b{2} \/ ={G.g}].
proof.
move=> A_ll; proc.
call (: G.b, ={G.g}).
+ by proc; auto.
+ by move=> &2 _; proc; auto.
+ by move=> _; proc; auto.
by auto => /#.
qed.

lemma equiv_errors : equiv [M.main ~ M.single : true ==> true].
proof.
proc.
fail call{1} (: true).
fail call (f_spec 0 0).
fail call equiv_spec.
fail call (: G.b, true).
abort.

(* -------------------------------------------------------------------- *)
(* equiv, one-sided *)
lemma f_ll : phoare [M.f : true ==> true] = 1%r.
proof. by proc; auto. qed.

lemma equiv_onesided : equiv [M.main ~ M.single : true ==> true].
proof.
proc.
call{1} (_ : true ==> true).
+ by proc; auto.
call{2} (_ : true ==> true).
+ by proc; auto.
by auto.
qed.

lemma equiv_onesided_lemma : equiv [M.main ~ M.single : true ==> true].
proof.
proc.
call{1} f_ll.
call{2} f_ll.
by auto.
qed.

lemma equiv_onesided_errors : equiv [M.main ~ M.single : true ==> true].
proof.
proc.
fail call f_ll.
call{1} f_ll.
fail call{1} f_ll.
fail call{1} (_ : true ==> true).
abort.
