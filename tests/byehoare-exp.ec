(* `byehoare` on an expectation goal
     Exp[f(a) @ &m : e] <= bd        (e, bd : xreal, xreal order)
   is the denotational rule of the ehoare logic on expectations. It produces
   the subgoals
     ehoare[f : pre ==> post]
     pre{a/params, &m} <= bd         (xreal order, no coercion of bd)
     forall &hr, e <= post           (xreal order, no coercion of e)
   and, unlike the probability form `Pr[..] <= bd` (bd : real), no
   non-negativity side-condition `0%r <= bd`: xreal is non-negative. When no
   pre/post is given, the default pre is `bd` (with the same substitution) and
   the default post is `e` itself. *)
require import AllCore Distr DBool DInterval Xreal.

module M = {
  proc coin() : bool = { var b; b <$ {0,1}; return b; }
  proc unif(x : int) : int = { var r; r <$ [0..x]; return r; }
}.

module G = {
  var c : int
  proc get() : int = { var r; r <$ [0..G.c]; return r; }
}.

(* the expected value of a fair coin, seen as an xreal, is 1/2 *)
ehoare coin_exp : M.coin : (1%r/2%r)%xr ==> res%xr.
proof.
proc; rnd; skip => &hr /=.
rewrite Ep_mu; apply xle_rle; rewrite dboolE /=; smt().
qed.

(* ---- explicit ehoare lemma given as argument ---------------------------- *)
lemma exp_arg &m : Exp[M.coin() @ &m : res%xr] <= (1%r/2%r)%xr.
proof.
byehoare coin_exp.
(* remaining goals:
     (1%r / 2%r)%xr <= (1%r / 2%r)%xr
     forall &hr, res{hr}%xr <= res{hr}%xr
   (no `0%r <= bd` goal) *)
+ done.
+ done.
qed.

(* ---- explicit `(_ : pre ==> post)` cut --------------------------------- *)
lemma exp_cut &m (n : int) :
  0 <= n => Exp[M.unif(n) @ &m : (res%r)%xr] <= (n%r)%xr.
proof.
move=> ge0_n.
byehoare (_ : (0 <= arg) `|` (arg%r)%xr ==> (res%r)%xr).
(* remaining goals:
     ehoare[M.unif : (0 <= arg) `|` arg%xr ==> res%xr]
     (0 <= n) `|` n%xr <= n%xr
     forall &hr, res{hr}%xr <= res{hr}%xr *)
+ proc; rnd; skip => &hr.
  apply xle_cxr_r => ge0_x.
  apply (xle_trans (Ep [0..x{hr}] (fun _ => (x{hr}%r)%xr))).
  + by apply le_Ep => r /supp_dinter hr; apply xle_rle; smt().
  by rewrite EpC (dinter_ll 0 x{hr} ge0_x) smul1m.
+ by apply xle_cxr_l.
+ done.
qed.

(* ---- no argument: default pre = bd, default post = e ------------------- *)
lemma exp_default &m : Exp[M.coin() @ &m : res%xr] <= (1%r/2%r)%xr.
proof.
byehoare.
(* remaining goals:
     ehoare[M.coin : (1%r / 2%r)%xr ==> res%xr]
     (1%r / 2%r)%xr <= (1%r / 2%r)%xr
     forall &hr, res{hr}%xr <= res{hr}%xr *)
+ by conseq coin_exp.
+ done.
+ done.
qed.

(* the default pre is the bound where the memory `&m` is substituted by the
   memory of the procedure: here the bound `G.c{m}%xr` becomes the pre
   `G.c%xr` *)
lemma exp_default_glob &m : Exp[G.get() @ &m : (res%r)%xr] <= (G.c{m}%r)%xr.
proof.
byehoare.
(* remaining goals:
     ehoare[G.get : G.c%xr ==> res%xr]
     G.c{m}%xr <= G.c{m}%xr
     forall &hr, res{hr}%xr <= res{hr}%xr *)
+ proc; rnd; skip => &hr.
  apply (xle_trans (Ep [0..G.c{hr}] (fun _ => (G.c{hr}%r)%xr))).
  + by apply le_Ep => r /supp_dinter hr; apply xle_rle; smt().
  by rewrite EpC weight_dinter; case: (0 <= G.c{hr}) => //= _; rewrite /(%pos) /#.
+ done.
+ done.
qed.

(* ---- the probability form is unchanged --------------------------------- *)
lemma pr_arg &m : Pr[M.coin() @ &m : res] <= 1%r/2%r.
proof.
byehoare coin_exp.
(* remaining goals:
     (1%r / 2%r)%xr <= (1%r / 2%r)%xr
     forall &hr, res{hr}%xr <= res{hr}%xr
     0%r <= 1%r / 2%r
   the last one, the non-negativity of the real bound, is emitted only for
   the probability form *)
+ done.
+ done.
+ by smt().
qed.

lemma pr_default &m : Pr[M.coin() @ &m : res] <= 1%r/2%r.
proof.
byehoare.
+ by conseq coin_exp.
+ done.
+ done.
+ by smt().
qed.

(* `byehoare` only applies to a bound `Exp[..] <= bd` (or `Pr[..] <= bd`),
   not to an equality between expectations *)
lemma exp_not_pr &m : Exp[M.coin() @ &m : res%xr] = Exp[M.coin() @ &m : res%xr].
proof.
fail byehoare.
by [].
qed.
