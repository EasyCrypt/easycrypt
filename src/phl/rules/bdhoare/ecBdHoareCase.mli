(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_case = {
  bca_cond     : ss_inv;   (* case formula f *)
  bca_simplify : bool;     (* conjoin with the simplifying conjunction *)
}

(* [t_bdhoare_case { bca_cond = f; bca_simplify }] — case analysis on [f],
   with [~] the goal's comparison ([<=], [=] or [>=]):

     phoare [c : P /\ f ==> Q] ~ d      phoare [c : P /\ !f ==> Q] ~ d
     ----------------------------------------------------------------
                        phoare [c : P ==> Q] ~ d

   where [/\] is [f_and_simpl] when [bca_simplify], [f_and] otherwise.

   Node: [RBdHoareCase { bca_cond = f; bca_simplify }].
   Checker: "bdhoare-case". *)
val t_bdhoare_case : bdhoare_case -> backward
