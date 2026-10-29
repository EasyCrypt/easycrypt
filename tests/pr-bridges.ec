require import AllCore Distr DBool.

exception ex.

module M = {
  proc f() : int = {
    var x;
    x <- 1;
    return x;
  }

  proc g(a : int, b : bool) : int = {
    return a;
  }

  proc h(a : int) : bool = {
    var y;
    y <$ {0,1};
    return y;
  }

  proc e() = {
    raise ex;
  }
}.

(* -------------------------------------------------------------------- *)
(* [bypr]: hoare, phoare (each comparison) and equiv, procedure forms.  *)

lemma hoareF_pr : hoare [M.f : true ==> res = 1].
proof.
bypr=> &m /=.
by byphoare=> //; hoare; proc; auto.
qed.

lemma bdhoareF_pr_eq : phoare [M.f : true ==> res = 1] = 1%r.
proof.
bypr=> &m /=.
by byphoare=> //; proc; auto.
qed.

lemma bdhoareF_pr_le (a0 : int) : phoare [M.h : a = a0 ==> res] <= (1%r/2%r).
proof.
bypr=> &m; split=> [/#|h].
byphoare (_: arg = a0 ==> res)=> //.
by proc; rnd; auto=> />; smt(dboolE).
qed.

lemma bdhoareF_pr_ge : phoare [M.g : 0 <= a ==> 0 <= res] >= 1%r.
proof.
bypr=> &m; split=> // hpos.
byphoare (_: 0 <= arg.`1 ==> 0 <= res)=> //.
by proc; auto.
qed.

lemma equivF_pr : equiv [M.g ~ M.g : ={a, b} ==> ={res}].
proof.
bypr (res{1}) (res{2})=> //.
move=> &1 &2 r [] eqa eqb.
by byequiv (_: ={a, b} ==> ={res})=> //; proc; auto.
qed.

lemma pr_errors : hoare [M.f : true ==> res = 1].
proof.
fail bypr (res{1}) (res{2}).
proc.
fail bypr.
abort.

lemma pr_errors_equiv : equiv [M.g ~ M.g : ={a, b} ==> ={res}].
proof.
fail bypr (res{1}) (true).
fail bypr.
abort.

(* -------------------------------------------------------------------- *)
(* [pr_bounded]: statement and procedure forms, premise-free and with a *)
(* premise; [trivial] uses the premise-free forms only.                 *)

lemma bdhoareF_prbounded_le : phoare [M.f : true ==> res = 1] <= 1%r.
proof. by pr_bounded. qed.

lemma bdhoareS_prbounded_le : phoare [M.f : true ==> res = 1] <= 1%r.
proof. by proc; pr_bounded. qed.

lemma bdhoareF_prbounded_ge : phoare [M.f : true ==> res = 1] >= 0%r.
proof. by pr_bounded. qed.

lemma bdhoareS_prbounded_ge : phoare [M.f : true ==> res = 1] >= 0%r.
proof. by proc; pr_bounded. qed.

lemma bdhoareF_prbounded_false : phoare [M.f : true ==> false] = 0%r.
proof. by pr_bounded. qed.

lemma bdhoareS_prbounded_false : phoare [M.f : true ==> false] = 0%r.
proof. by proc; pr_bounded. qed.

lemma bdhoareF_prbounded_le_premise (d : real) :
  1%r <= d => phoare [M.f : true ==> res = 1] <= d.
proof. by move=> hd; pr_bounded=> &m. qed.

lemma bdhoareS_prbounded_ge_premise (d : real) :
  d <= 0%r => phoare [M.f : true ==> res = 1] >= d.
proof. by move=> hd; proc; pr_bounded=> &m. qed.

lemma bdhoare_prbounded_trivial : phoare [M.f : true ==> res = 1] <= 1%r.
proof. by trivial. qed.

lemma prbounded_errors (d : real) : phoare [M.f : true ==> res = 1] = d.
proof.
fail pr_bounded.
proc.
fail pr_bounded.
abort.

lemma prbounded_errors_trivial (d : real) :
  1%r <= d => phoare [M.f : true ==> res = 1] <= d.
proof.
move=> hd.
fail by trivial.
proc.
fail by trivial.
abort.

lemma prbounded_errors_kind : hoare [M.f : true ==> res = 1].
proof.
fail pr_bounded.
abort.

(* -------------------------------------------------------------------- *)
(* [hoare]: in both directions, statement and procedure forms.          *)

lemma hoareF_hoare : hoare [M.f : true ==> res = 1].
proof.
hoare.
by hoare; proc; auto.
qed.

lemma hoareS_hoare : hoare [M.f : true ==> res = 1].
proof.
proc; hoare.
by hoare; auto; smt().
qed.

lemma bdhoareF_hoare_le (d : real) :
  phoare [M.f : true ==> res <> 1] <= (d * d).
proof.
hoare.
+ by move=> &m /=; smt().
by proc; auto.
qed.

lemma bdhoareF_hoare_eq0 : phoare [M.f : true ==> res <> 1] = 0%r.
proof. by hoare; proc; auto. qed.

lemma bdhoareS_hoare_eq0 : phoare [M.f : true ==> res <> 1] = 0%r.
proof. by proc; hoare; auto. qed.

lemma bdhoareS_hoare_ge : phoare [M.f : true ==> res <> 1] >= 0%r.
proof.
proc; hoare.
by auto.
qed.

lemma hoare_errors : equiv [M.f ~ M.f : true ==> ={res}].
proof.
fail hoare.
abort.

lemma hoare_errors_exn : hoare [M.e : true ==> false | ex => true].
proof.
fail hoare.
proc.
fail hoare.
abort.

(* -------------------------------------------------------------------- *)
(* [phoare split]: and / or / not, with and without a change of bound.  *)
(* Statement form only: the surface tactic cannot type its bounds on a  *)
(* procedure goal.                                                      *)

lemma bdhoareS_split_and :
  phoare [M.h : true ==> res /\ true] = (1%r/2%r + 1%r - 1%r).
proof.
proc.
phoare split (1%r/2%r) 1%r 1%r.
+ by rnd; auto=> />; smt(dboolE).
+ by rnd; auto=> />; smt(dbool_ll).
by rnd; auto=> />; smt(dbool_ll).
qed.

lemma bdhoareS_split_and_bound :
  phoare [M.h : true ==> res /\ true] = (1%r/2%r).
proof.
proc.
phoare split (1%r/2%r) 1%r 1%r.
+ by move=> &m /=; smt().
+ by rnd; auto=> />; smt(dboolE).
+ by rnd; auto=> />; smt(dbool_ll).
by rnd; auto=> />; smt(dbool_ll).
qed.

lemma bdhoareS_split_or :
  phoare [M.h : true ==> res \/ !res] = (1%r/2%r + 1%r/2%r - 0%r).
proof.
proc.
phoare split (1%r/2%r) (1%r/2%r) 0%r.
+ by rnd; auto=> />; smt(dboolE).
+ by rnd; auto=> />; smt(dboolE).
by hoare; auto; smt().
qed.

lemma bdhoareS_split_or_bound :
  phoare [M.h : true ==> res \/ !res] = 1%r.
proof.
proc.
phoare split (1%r/2%r) (1%r/2%r).
+ by move=> &m /=; smt().
+ by rnd; auto=> />; smt(dboolE).
+ by rnd; auto=> />; smt(dboolE).
by hoare; auto; smt().
qed.

lemma bdhoareS_split_or_case :
  phoare [M.h : a = 0 ==> res] = (1%r/2%r).
proof.
proc.
phoare split (1%r/2%r) 0%r : (a = 0).
+ by move=> &m /=; smt().
+ by rnd; auto=> />; smt(dboolE).
by hoare; auto; smt().
qed.

lemma bdhoareS_split_not :
  phoare [M.h : true ==> res] = (1%r - 1%r/2%r).
proof.
proc.
phoare split ! 1%r (1%r/2%r).
+ by rnd; auto=> />; smt(dbool_ll).
by rnd; auto=> />; smt(dboolE).
qed.

lemma bdhoareS_split_not_bound :
  phoare [M.h : true ==> res] = (1%r/2%r).
proof.
proc.
phoare split ! 1%r (1%r/2%r).
+ by move=> &m /=; smt().
+ by rnd; auto=> />; smt(dbool_ll).
by rnd; auto=> />; smt(dboolE).
qed.

lemma split_errors : phoare [M.h : true ==> res] = (1%r/2%r).
proof.
fail phoare split (1%r/2%r) 0%r.
proc.
fail phoare split (1%r/2%r) 0%r.
abort.

lemma split_errors_kind : hoare [M.h : true ==> res /\ true].
proof.
fail phoare split 1%r 1%r 1%r.
fail phoare split ! 1%r 1%r.
abort.

(* -------------------------------------------------------------------- *)
(* [hoare split]: statement form.                                       *)

lemma hoareS_split : hoare [M.f : true ==> res = 1 /\ 0 < res].
proof.
proc; hoare split.
+ by auto.
by auto.
qed.

lemma hoare_split_errors : hoare [M.f : true ==> res = 1].
proof.
fail hoare split.
proc.
fail hoare split.
abort.
