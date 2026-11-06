(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* None: splitting a hoare postcondition is derived from the consequence
   rules. *)

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_split] — on [hoare [c : P ==> A /\ B | Q_e]] (a symmetric
   conjunction [/\], not [&&]):
   1. the consequence rule (currently [EcPhlConseq.t_hoareS_conseq]) to
      [hoare [c : P /\ P ==> A /\ B | Q_e]], closing its two side
      conditions with [done] (fails if it does not);
   2. the conjunctive consequence rule (currently
      [EcPhlConseq.t_hoareS_conseq_conj]) on [P /\ P].
   Visible goals: [hoare [c : P ==> B | Q_e]], then
   [hoare [c : P ==> A | Q_e]]. Emits no node of its own. *)
val t_hoare_split : backward
