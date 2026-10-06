(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_split_bop = {
  bsb_b1 : ss_inv;   (* bound b1 for the left operand A *)
  bsb_b2 : ss_inv;   (* bound b2 for the right operand B *)
  bsb_b3 : ss_inv;   (* opposite bound b3 for the dual connective *)
}

(* In the rules below, [~] is the goal's comparison and [~'] its opposite
   ([<=] and [>=] are swapped, [=] stays). *)

(* [t_bdhoareS_split_and { bsb_b1 = b1; bsb_b2 = b2; bsb_b3 = b3 }] —
   inclusion-exclusion on a conjunction:

     phoare [c : P ==> A] ~ b1
     phoare [c : P ==> B] ~ b2
     phoare [c : P ==> A \/ B] ~' b3
     -------------------------------  d = (b1 + b2) - b3
     phoare [c : P ==> A /\ B] ~ d

   Side conditions: the postcondition is a conjunction, and the bound [d]
   is [(b1 + b2) - b3] up to alpha-conversion (otherwise fails).

   Node: [RBdHoareSSplitAnd { bsb_b1 = b1; bsb_b2 = b2; bsb_b3 = b3 }].
   Checker: "bdhoareS-split-and". *)
val t_bdhoareS_split_and : bdhoare_split_bop -> backward

(* [t_bdhoareF_split_and] — same for a procedure.
   Node: [RBdHoareFSplitAnd]. Checker: "bdhoareF-split-and". *)
val t_bdhoareF_split_and : bdhoare_split_bop -> backward

(* [t_bdhoareS_split_or { bsb_b1 = b1; bsb_b2 = b2; bsb_b3 = b3 }] —
   inclusion-exclusion on a disjunction:

     phoare [c : P ==> A] ~ b1
     phoare [c : P ==> B] ~ b2
     phoare [c : P ==> A /\ B] ~' b3
     -------------------------------  d = (b1 + b2) - b3
     phoare [c : P ==> A \/ B] ~ d

   Side conditions: the postcondition is a disjunction, and the bound [d]
   is [(b1 + b2) - b3] up to alpha-conversion (otherwise fails).

   Node: [RBdHoareSSplitOr { bsb_b1 = b1; bsb_b2 = b2; bsb_b3 = b3 }].
   Checker: "bdhoareS-split-or". *)
val t_bdhoareS_split_or : bdhoare_split_bop -> backward

(* [t_bdhoareF_split_or] — same for a procedure.
   Node: [RBdHoareFSplitOr]. Checker: "bdhoareF-split-or". *)
val t_bdhoareF_split_or : bdhoare_split_bop -> backward

type bdhoare_split_not = {
  bnt_b1 : ss_inv;   (* bound b1 for [true] *)
  bnt_b2 : ss_inv;   (* opposite bound b2 for the negated postcondition *)
}

(* [t_bdhoareS_split_not { bnt_b1 = b1; bnt_b2 = b2 }] — complement:

     phoare [c : P ==> true] ~ b1
     phoare [c : P ==> !Q] ~' b2
     ----------------------------  d = b1 - b2
     phoare [c : P ==> Q] ~ d

   where [!Q] is simplified ([!!Q'] is [Q'], ...). Side condition: the
   bound [d] is [b1 - b2] up to alpha-conversion (otherwise fails).

   Node: [RBdHoareSSplitNot { bnt_b1 = b1; bnt_b2 = b2 }].
   Checker: "bdhoareS-split-not". *)
val t_bdhoareS_split_not : bdhoare_split_not -> backward

(* [t_bdhoareF_split_not] — same for a procedure.
   Node: [RBdHoareFSplitNot]. Checker: "bdhoareF-split-not". *)
val t_bdhoareF_split_not : bdhoare_split_not -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_split_and r] — on a statement or procedure goal
   [phoare [_ : P ==> A /\ B] ~ d]:
   1. unless [d] is syntactically [(b1 + b2) - b3], the bound-changing
      consequence (currently [EcPhlConseq.t_bdHoare{S,F}_conseq_bd]) to
      that bound, whose side condition is left open;
   2. then [t_bdhoare{S,F}_split_and r].
   Visible goals: the bound side condition if any, then the three
   premises. Emits no node of its own. *)
val t_bdhoare_split_and : bdhoare_split_bop -> backward

(* [t_bdhoare_split_or r] — same, with [t_bdhoare{S,F}_split_or]. *)
val t_bdhoare_split_or : bdhoare_split_bop -> backward

(* [t_bdhoare_split_not r] — same, with [t_bdhoare{S,F}_split_not]; the
   bound is compared with [b1 - b2] up to alpha-conversion. *)
val t_bdhoare_split_not : bdhoare_split_not -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [phoare split ...] on a bdhoare goal [phoare [_ : P ==> Q] ~ d], the
   bounds being typed in the goal's memory:
   - [phoare split b1 b2 b3?]: [Q] is a conjunction (resp. disjunction),
     [b3] defaults to [0%r]; applies [t_bdhoare_split_and] (resp.
     [t_bdhoare_split_or]);
   - [phoare split b1 b2 : R]: the consequence rule (currently
     [EcPhlConseq.t_conseq]) to [(R /\ Q) \/ (!R /\ Q)] (closing its side
     conditions by [orDandN]), [t_bdhoare_split_or] with [b3 = 0%r], and
     the consequence rule on its third premise to [false] (closing it with
     [andDorN] and [trivial]). Visible goals: the bounds side condition if
     any, then [phoare [_ : P ==> R /\ Q] ~ b1] and
     [phoare [_ : P ==> !R /\ Q] ~ b2];
   - [phoare split ! b1 b2]: applies [t_bdhoare_split_not]. *)
val process_bdhoare_split : EcParsetree.bdh_split -> backward
