(* ==========================================================================

   Oracle-access Rényi-∞ bound.

   [rdiv_inf_oracleRO]: an adversary [D] with oracle access to a sampler
   sees Rényi-∞ probability preservation multiplicative in the number of
   distinct queried keys (bounded by [|t|]).

   Approach: black-box reduction to [PROM.FullRO]'s eager/lazy
   equivalence.  The oracle is indexed by a finite key type [t]; each
   distinct key's response is an independent sample from [d].  After
   [PROM]'s trailing-resample form, the oracle's state is distributed
   as [dfun (fun _ => d)], on which we apply [rdiv_inf_dfun].

   The query budget is expressed as [FinT.card] — the total number of
   possible distinct keys.  Users choose [t] to match their query
   bound (e.g., [t = fin N] for a bound of [N]).

   ========================================================================== *)

require import AllCore FMap FinType StdOrder StdRing.
require import Distr RDiv.
require (*--*) PROM.
(*---*) import RealOrder RField.

abstract theory RDivOracle.

type t, out_t.

(* Finite key space — [FinT.card] is the query-budget ceiling. *)
clone import FinType as FinT with type t <- t.

(* The two distributions compared. *)
op [lossless] d1 : out_t distr.
op [lossless] d2 : out_t distr.

axiom dom_d1_d2 : dominated d1 d2.

(* Two PROM clones — one per distribution. *)
clone import PROM.FullRO as R1 with
  type in_t   <- t,
  type out_t  <- out_t,
  type d_in_t <- unit,
  type d_out_t <- bool,
  op dout      <- fun _ => d1
  proof*.

clone import PROM.FullRO as R2 with
  type in_t   <- t,
  type out_t  <- out_t,
  type d_in_t <- unit,
  type d_out_t <- bool,
  op dout      <- fun _ => d2
  proof*.

(* The flagship: advantage bounded by the product Rényi-∞ over [t]. *)
lemma rdiv_inf_oracleRO
  (D <: R1.RO_Distinguisher {-R1.RO, -R2.RO})
  &m :
  Pr[R1.MainD(D, R1.RO).distinguish() @ &m : res] <=
    RField.exp (rdiv_inf d1 d2) FinT.card *
    Pr[R2.MainD(D, R2.RO).distinguish() @ &m : res].
proof. admit. qed.

end RDivOracle.
