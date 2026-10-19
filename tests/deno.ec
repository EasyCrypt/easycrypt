require import AllCore Distr DBool Xreal.

module M = {
  var g : int
  var bad : bool

  proc f(x : int) : int = {
    g <- x;
    return x;
  }

  proc h() : bool = {
    var y;
    y <$ {0,1};
    return y;
  }

  proc u() : bool = {
    var y;
    bad <- false;
    y <$ {0,1};
    if (y) { bad <- true; }
    return y;
  }

  proc v() : bool = {
    var y;
    bad <- false;
    y <$ {0,1};
    if (y) { bad <- true; y <- false; }
    return y;
  }
}.

(* -------------------------------------------------------------------- *)
(* [byphoare]: each comparison, both orientations, cut and proof term.  *)

lemma bdhoare_le &m : Pr[M.h() @ &m : res] <= 1%r / 2%r.
proof.
byphoare (_: true ==> res)=> //.
by proc; rnd; auto=> />; smt(dboolE).
qed.

lemma bdhoare_ge &m : 1%r / 2%r <= Pr[M.h() @ &m : res].
proof.
byphoare=> //.
by proc; rnd; auto=> />; smt(dboolE).
qed.

lemma bdhoare_eq &m : Pr[M.h() @ &m : res] = 1%r / 2%r.
proof.
byphoare=> //.
by proc; rnd; auto=> />; smt(dboolE).
qed.

lemma bdhoare_eq_sym &m : 1%r / 2%r = Pr[M.h() @ &m : res].
proof.
byphoare=> //.
by proc; rnd; auto=> />; smt(dboolE).
qed.

lemma h_half : phoare [M.h : true ==> res] = (1%r / 2%r).
proof. by proc; rnd; auto=> />; smt(dboolE). qed.

lemma bdhoare_pterm &m : Pr[M.h() @ &m : res] = 1%r / 2%r.
proof. by byphoare h_half. qed.

lemma bdhoare_pterm_sym &m : 1%r / 2%r = Pr[M.h() @ &m : res].
proof. by byphoare h_half. qed.

lemma bdhoare_args &m (a : int) : Pr[M.f(a) @ &m : res = a /\ M.g = a] = 1%r.
proof.
byphoare (_: arg = a ==> res = a /\ M.g = a)=> //.
by proc; auto.
qed.

lemma bdhoare_errors &m : Pr[M.h() @ &m : res] < 1%r.
proof.
fail byphoare.
fail byphoare h_half.
abort.

lemma bdhoare_errors_noprob (x : real) : x = x.
proof.
fail byphoare.
abort.

(* -------------------------------------------------------------------- *)
(* [byehoare]: default and explicit cut, proof term, errors.            *)

lemma ehoare_default &m : Pr[M.h() @ &m : res] <= 1%r.
proof.
byehoare=> //.
proc; auto=> &hr /=.
by rewrite Ep_dbool /#.
qed.

lemma ehoare_cut &m (a : int) : Pr[M.f(a) @ &m : res = a] <= 1%r.
proof.
byehoare (_: (arg = a)%xr ==> (res = a)%xr)=> //.
by proc; auto.
qed.

lemma h_ehoare : ehoare [M.h : 1%xr ==> res%xr].
proof. proc; auto=> &hr /=; by rewrite Ep_dbool /#. qed.

lemma ehoare_pterm &m : Pr[M.h() @ &m : res] <= 1%r.
proof. by byehoare h_ehoare. qed.

lemma ehoare_errors &m : 1%r <= Pr[M.h() @ &m : res].
proof.
fail byehoare.
fail byehoare h_ehoare.
abort.

(* -------------------------------------------------------------------- *)
(* [byequiv]: equality (with and without [eq]), inequality, pterm.      *)

lemma equiv_eq &m : Pr[M.f(1) @ &m : res = 1] = Pr[M.f(1) @ &m : res = 1].
proof.
byequiv=> //.
by proc; auto.
qed.

lemma equiv_eq_noeq &m : Pr[M.h() @ &m : res] = Pr[M.h() @ &m : res].
proof.
byequiv [-eq]=> //.
by proc; auto.
qed.

lemma equiv_le &m : Pr[M.u() @ &m : res] <= Pr[M.h() @ &m : res].
proof.
byequiv (_: true ==> res{1} => res{2})=> //.
by proc; wp; rnd; auto=> /#.
qed.

lemma equiv_default_le &m : Pr[M.u() @ &m : res] <= Pr[M.h() @ &m : res].
proof.
byequiv=> //.
by proc; wp; rnd; auto=> /#.
qed.

lemma equiv_args &m (a : int) :
  Pr[M.f(a) @ &m : res = a] = Pr[M.f(a) @ &m : M.g = a].
proof.
byequiv (_: ={arg} /\ arg{1} = a ==> res{1} = a <=> M.g{2} = a)=> //.
by proc; auto.
qed.

lemma uh : equiv [M.u ~ M.h : true ==> ={res}].
proof. by proc; wp; rnd; auto. qed.

lemma equiv_pterm &m : Pr[M.u() @ &m : res] = Pr[M.h() @ &m : res].
proof. by byequiv uh. qed.

lemma equiv_errors &m : Pr[M.u() @ &m : res] < Pr[M.h() @ &m : res].
proof.
fail byequiv.
fail byequiv uh.
abort.

lemma equiv_errors_shape &m : Pr[M.u() @ &m : res] <= 1%r.
proof.
fail byequiv.
fail byequiv uh.
abort.

(* -------------------------------------------------------------------- *)
(* [byequiv] upto bad: [Pr[..] <= Pr[..] + Pr[..: bad]] and             *)
(* [`|Pr[..] - Pr[..]| <= Pr[..: bad]] (with [: bad1]).                 *)

lemma equiv_bad &m :
  Pr[M.u() @ &m : res] <= Pr[M.v() @ &m : res] + Pr[M.v() @ &m : M.bad].
proof.
byequiv=> //.
proc; seq 2 2 : (={y} /\ !M.bad{2}); 1: by auto.
by if; auto=> /#.
qed.

lemma equiv_bad_cut &m :
  Pr[M.u() @ &m : res] <= Pr[M.v() @ &m : res] + Pr[M.v() @ &m : M.bad].
proof.
byequiv (_: true ==> !M.bad{2} => res{1} => res{2})=> //.
proc; seq 2 2 : (={y} /\ !M.bad{2}); 1: by auto.
by if; auto=> /#.
qed.

lemma uv : equiv [M.u ~ M.v : true ==> M.bad{1} = M.bad{2} /\ (!M.bad{2} => ={res})].
proof.
proc; seq 2 2 : (={y} /\ !M.bad{1} /\ !M.bad{2}); 1: by auto.
by if; auto=> /#.
qed.

lemma equiv_bad_pterm &m :
  Pr[M.u() @ &m : res] <= Pr[M.v() @ &m : res] + Pr[M.v() @ &m : M.bad].
proof.
(* the proof term does not match: through the consequence rule *)
byequiv uv=> //.
by move=> &1 &2 /#.
qed.

lemma equiv_bad2 &m :
  `|Pr[M.u() @ &m : res] - Pr[M.v() @ &m : res]| <= Pr[M.v() @ &m : M.bad].
proof.
(* with [eq], the default judgement does not match the rule's: through
   the consequence rule *)
byequiv : M.bad=> //.
+ proc; seq 2 2 : (={y} /\ !M.bad{1} /\ !M.bad{2}); 1: by auto.
  by if; auto=> /#.
by move=> &1 &2 /#.
qed.

lemma equiv_bad2_noeq &m :
  `|Pr[M.u() @ &m : res] - Pr[M.v() @ &m : res]| <= Pr[M.v() @ &m : M.bad].
proof.
byequiv [-eq] : M.bad=> //.
proc; seq 2 2 : (={y} /\ !M.bad{1} /\ !M.bad{2}); 1: by auto.
by if; auto=> /#.
qed.

lemma equiv_bad2_pterm &m :
  `|Pr[M.u() @ &m : res] - Pr[M.v() @ &m : res]| <= Pr[M.v() @ &m : M.bad].
proof.
byequiv uv : M.bad=> //.
by move=> &1 &2 /#.
qed.

lemma equiv_bad2_errors &m :
  `|Pr[M.u() @ &m : res] - Pr[M.v() @ &m : res]| <= Pr[M.u() @ &m : M.bad].
proof.
fail byequiv : M.bad.
abort.
