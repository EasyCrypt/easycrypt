(* -------------------------------------------------------------------- *)
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): a hoare judgement is a probability-0 one,
   which is then stated on the probability of the negated postcondition. *)
let t_hoareF_pr (tc : tcenv1) =
  FApi.t_seq EcHoareOfBdHoare.t_hoareF_of_bdhoare EcBdHoarePr.t_bdhoareF_pr tc
