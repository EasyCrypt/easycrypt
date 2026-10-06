(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_bdhoareS_prbounded ~conseq] — a probability lies in [[0%r, 1%r]],
   and the probability of [false] is [0%r]:

     ------------------------------    ---------------------------------
     phoare [c : P ==> Q] <= 1%r       phoare [c : P ==> Q] >= 0%r

     ---------------------------------  (~ any comparison)
     phoare [c : P ==> false] ~ 0%r

   and, more generally, for a bound that is not syntactically one of the
   above:

     forall &m, P => 1%r <= d          forall &m, P => d <= 0%r
     ------------------------------    ---------------------------------
     phoare [c : P ==> Q] <= d         phoare [c : P ==> Q] >= d

   The bounds [0%r], [1%r] and the postcondition [false] are matched
   syntactically. Side condition: one of the premise-free forms applies,
   or the comparison is [<=] or [>=] (otherwise fails). With
   [~conseq:false], the premise forms are not used (the tactic fails
   instead).

   Node: [RBdHoareSPrBounded]. Checker: "bdhoareS-prbounded". *)
val t_bdhoareS_prbounded : conseq:bool -> backward

(* [t_bdhoareF_prbounded ~conseq] — same for a procedure (the premise
   quantifies over its initial memory).

   Node: [RBdHoareFPrBounded]. Checker: "bdhoareF-prbounded". *)
val t_bdhoareF_prbounded : conseq:bool -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_prbounded ~conseq] — [t_bdhoareS_prbounded ~conseq] or
   [t_bdhoareF_prbounded ~conseq], depending on the goal. *)
val t_bdhoare_prbounded : conseq:bool -> backward
