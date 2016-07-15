(* -------------------------------------------------------------------- *)
require export Distr NewDistr Int IntExtra Real RealExtra RealExp List.
require import StdBigop.
(*---*) export StdBigop.Bigreal.BRA.

(* -------------------------------------------------------------------- *)
op lap : real -> int -> int distr.

axiom lap_ll e x : is_lossless (lap e x).

(* -------------------------------------------------------------------- *)
op sumr (n : int) (f : int -> real) =
  Bigreal.BRA.bigi predT f 0 n.

(* -------------------------------------------------------------------- *)
axiom lap_bound_le eps delt:
  0%r < eps => 0%r < delt =>
    1%r - delt <=
     mu (lap eps 0) (fun x => `|x%r| <= ln (inv delt) / eps).

lemma lap_bound_lt eps delt:
   0%r < eps => 0%r < delt =>
     mu (lap eps 0) (fun x => ln (inv delt) / eps < `|x%r|) <= delt.
proof.
move=> gt0_e gt0_d; pose F := fun x => (`|x%r| <= ln (inv delt) / eps).
rewrite -(mu_eq _ (predC F)) 1:/# mu_not lap_ll /F.
by have /# := lap_bound_le _ _ gt0_e gt0_d.
qed.
