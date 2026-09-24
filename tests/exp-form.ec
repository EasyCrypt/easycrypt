(* Unit tests for the expectation form of the Pr construct:
     Exp[f(args) @ &m : e]   with e : xreal, of type xreal
   semantically the expectation `Ep d (fun m => e)` of `e` over the output
   distribution `d` of `f`. *)
require import AllCore Distr DInterval Xreal.

module M = { proc f(x : int) : int = { var r; r <$ [0..x]; return r; } }.

(* ---- parsing / printing ------------------------------------------------ *)

(* plain form *)
lemma parse1 &m (x : int) :
  Exp[M.f(x) @ &m : (res%r)%xr] = Exp[M.f(x) @ &m : (res%r)%xr].
proof. by []. qed.

(* explicit `{&h}` result memory *)
lemma parse2 &m (x : int) :
  Exp[M.f(x) {&h} @ &m : (res{h}%r)%xr] = Exp[M.f(x) @ &m : (res%r)%xr].
proof. by []. qed.

(* blanks between `Exp` and `[` *)
lemma parse3 &m (x : int) :
  Exp [ M.f(x) @ &m : (res%r)%xr ] = Exp[M.f(x) @ &m : (res%r)%xr].
proof. by []. qed.

(* an expectation has type xreal: it is compared with the xreal order *)
lemma typing1 &m (x : int) : Exp[M.f(x) @ &m : (res%r)%xr] <= oo.
proof. by apply xlexoo. qed.

(* printing *)
expect "
* In [lemmas or axioms]:

lemma parse1:
  forall &m (x : int), Exp[M.f(x) @ &m : res%xr] = Exp[M.f(x) @ &m : res%xr].
" by print parse1.

expect "
* In [lemmas or axioms]:

lemma parse2:
  forall &m (x : int),
    Exp[M.f(x) {&h}@ &m : res%xr] = Exp[M.f(x) @ &m : res%xr].
" by print parse2.

(* ---- typing error: the body must be an xreal, not a bool -------------- *)
fail lemma bad &m : Exp[M.f(1) @ &m : res = 0] = '1.

(* ---- `rewrite Pr[...]` only selects probabilities ----------------------- *)
lemma mixed &m :
     Exp[M.f(1) @ &m : (res%r)%xr] = Exp[M.f(1) @ &m : (res%r)%xr]
  /\ Pr[M.f(1) @ &m : res = 0] <= 1%r.
proof. by rewrite Pr[mu_le1]. qed.

(* ---- SMT: Exp is `Ep` of the same distribution as Pr -------------------- *)
lemma exp_smt &m :
  Exp[M.f(1) @ &m : (res = 0)%xr] = Pr[M.f(1) @ &m : res = 0]%xr.
proof. smt(Ep_mu). qed.

expect "
* In [lemmas or axioms]:

lemma exp_smt:
  forall &m, Exp[M.f(1) @ &m : (res = 0)%xr] = Pr[M.f(1) @ &m : res = 0]%xr.
" by print exp_smt.
