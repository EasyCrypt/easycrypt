(* [rewrite Pr]: the facts of the bdhoare pr-fact rule (t_bdhoare_pr_fact),
   one per lemma, and the error paths of the tactic. *)
require import AllCore List Distr DInterval StdBigop RealSeries.
import Bigreal.

(* -------------------------------------------------------------------- *)
module M = {
  var g : int

  proc f(a : int) : int = {
    var x : int;
    x <$ [0..a];
    g <- x;
    return x;
  }

  proc h() : int = {
    var x : int;
    x <$ [0..1];
    return x;
  }
}.

(* -------------------------------------------------------------------- *)
(* mu_eq: one premise, the equivalence of the events. *)
lemma t_mu_eq &m :
  Pr[M.f(1) @ &m : res = 0 /\ M.g = res] = Pr[M.f(1) @ &m : M.g = res /\ res = 0].
proof.
rewrite Pr[mu_eq].
- by move=> &hr; split=> [[-> ->]|[-> ->]].
- by [].
qed.

(* mu_sub: one premise, the inclusion of the events. *)
lemma t_mu_sub &m :
  Pr[M.f(1) @ &m : res = 0] <= Pr[M.f(1) @ &m : 0 <= res].
proof.
rewrite Pr[mu_sub].
- by move=> &hr ->.
- by [].
qed.

(* mu_false *)
lemma t_mu_false &m : Pr[M.f(1) @ &m : false] = 0%r.
proof. by rewrite Pr[mu_false]. qed.

(* mu_not *)
lemma t_mu_not &m :
  Pr[M.f(1) @ &m : !(res = 0)]
  = Pr[M.f(1) @ &m : true] - Pr[M.f(1) @ &m : res = 0].
proof. by rewrite Pr[mu_not]. qed.

(* mu_or, symmetric and asymmetric disjunctions *)
lemma t_mu_or &m :
  Pr[M.f(1) @ &m : res = 0 \/ M.g = 1]
  = Pr[M.f(1) @ &m : res = 0] + Pr[M.f(1) @ &m : M.g = 1]
  - Pr[M.f(1) @ &m : res = 0 /\ M.g = 1].
proof. by rewrite Pr[mu_or]. qed.

lemma t_mu_ora &m :
  Pr[M.f(1) @ &m : res = 0 || M.g = 1]
  = Pr[M.f(1) @ &m : res = 0] + Pr[M.f(1) @ &m : M.g = 1]
  - Pr[M.f(1) @ &m : res = 0 /\ M.g = 1].
proof. by rewrite Pr[mu_or]. qed.

(* mu_disjoint: one premise, the disjointness of the events. *)
lemma t_mu_disjoint &m :
  Pr[M.f(1) @ &m : res = 0 \/ res = 1]
  = Pr[M.f(1) @ &m : res = 0] + Pr[M.f(1) @ &m : res = 1].
proof.
rewrite Pr[mu_disjoint].
- by move=> &hr /#.
- by [].
qed.

lemma t_mu_disjoint_a &m :
  Pr[M.f(1) @ &m : res = 0 || res = 1]
  = Pr[M.f(1) @ &m : res = 0] + Pr[M.f(1) @ &m : res = 1].
proof.
rewrite Pr[mu_disjoint].
- by move=> &hr /#.
- by [].
qed.

(* mu_split, the argument read in the memory of the event *)
lemma t_mu_split &m :
  Pr[M.f(1) @ &m : res = 0]
  = Pr[M.f(1) @ &m : res = 0 /\ M.g = res] + Pr[M.f(1) @ &m : res = 0 /\ !M.g = res].
proof. by rewrite Pr[mu_split (M.g = res)]. qed.

(* mu_ge0, mu_le1 *)
lemma t_mu_ge0 &m : 0%r <= Pr[M.f(1) @ &m : res = 0].
proof. by rewrite Pr[mu_ge0]. qed.

lemma t_mu_le1 &m : Pr[M.f(1) @ &m : res = 0] <= 1%r.
proof. by rewrite Pr[mu_le1]. qed.

(* muE, with and without a trivial event *)
lemma t_muE &m :
  Pr[M.f(1) @ &m : 0 <= res]
  = sum (fun x => Pr[M.f(1) @ &m : 0 <= res /\ res = x]).
proof. by rewrite Pr[muE]. qed.

lemma t_muE_true &m :
  Pr[M.f(1) @ &m : true] = sum (fun x => Pr[M.f(1) @ &m : res = x]).
proof. by rewrite Pr[muE]. qed.

(* mu1_le_eq_mu1: two premises, losslessness and the bound. *)
lemma t_mu1_le_eq_mu1 &m :
  Pr[M.h() @ &m : res = 0] = mu1 [0..1] 0.
proof.
rewrite Pr[mu1_le_eq_mu1 [0..1]].
- by proc; auto=> />; rewrite dinter_ll.
- move=> k; byphoare (_ : true ==> res = k)=> //.
  by proc; rnd (pred1 k); auto.
- by [].
qed.

(* mu_has_le *)
op l : int list.

lemma t_mu_has_le &m :
  Pr[M.f(1) @ &m : has (fun x => res = x) l]
  <= BRA.big predT (fun x => Pr[M.f(1) @ &m : res = x]) l.
proof. by rewrite Pr[mu_has_le]. qed.

(* The first matching subterm is rewritten. *)
lemma t_first &m :
  Pr[M.f(1) @ &m : false] + Pr[M.f(2) @ &m : false] = 0%r.
proof. by rewrite Pr[mu_false] Pr[mu_false]. qed.

(* -------------------------------------------------------------------- *)
(* Error paths. *)

(* not a probability lemma *)
lemma e_unknown &m : Pr[M.f(1) @ &m : false] = 0%r.
proof. fail rewrite Pr[mu_foo]. abort.

(* argument expected *)
lemma e_arg &m : Pr[M.f(1) @ &m : res = 0] = 0%r.
proof. fail rewrite Pr[mu_split]. fail rewrite Pr[mu1_le_eq_mu1]. abort.

(* no argument expected *)
lemma e_noarg &m : Pr[M.f(1) @ &m : false] = 0%r.
proof. fail rewrite Pr[mu_false true]. abort.

(* no pattern *)
lemma e_nopattern &m : Pr[M.f(1) @ &m : res = 0] = 0%r.
proof.
fail rewrite Pr[mu_false]. fail rewrite Pr[mu_not]. fail rewrite Pr[mu_or].
fail rewrite Pr[mu_disjoint]. fail rewrite Pr[mu_eq]. fail rewrite Pr[mu_sub].
fail rewrite Pr[mu_ge0]. fail rewrite Pr[mu_le1]. fail rewrite Pr[mu_has_le].
abort.

(* a probability under a binder it depends on is not selected *)
lemma e_bound &m : forall a, Pr[M.f(a) @ &m : false] = 0%r.
proof. fail rewrite Pr[mu_false]. abort.

(* mu1_le_eq_mu1: the value depends on the memory of the event *)
lemma e_mu1_value &m : Pr[M.f(1) @ &m : res = M.g] = 0%r.
proof. fail rewrite Pr[mu1_le_eq_mu1 [0..1]]. abort.

(* mu1_le_eq_mu1: the distribution depends on a memory *)
lemma e_mu1_distr &m : Pr[M.f(1) @ &m : res = 0] = 0%r.
proof. fail rewrite Pr[mu1_le_eq_mu1 [0..M.g]]. abort.

(* mu_has_le: the list depends on the memory of the event *)
lemma e_has_le &m :
  Pr[M.f(1) @ &m : has (fun x => res = x) [M.g]] <= 1%r.
proof. fail rewrite Pr[mu_has_le]. abort.

(* not in a hypothesis *)
lemma e_hyp &m : Pr[M.f(1) @ &m : false] = 0%r => true.
proof. move=> h. fail rewrite Pr[mu_false] in h. abort.
