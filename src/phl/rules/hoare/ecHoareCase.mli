(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_case = {
  hca_cond     : ss_inv;   (* case formula f *)
  hca_simplify : bool;     (* conjoin with the simplifying conjunction *)
}

(* [t_hoare_case { hca_cond = f; hca_simplify }] — case analysis on [f]:

     hoare [c : P /\ f ==> Q | Q_e]      hoare [c : P /\ !f ==> Q | Q_e]
     --------------------------------------------------------------------
                          hoare [c : P ==> Q | Q_e]

   where [/\] is [f_and_simpl] when [hca_simplify], [f_and] otherwise.

   Node: [RHoareCase { hca_cond = f; hca_simplify }]. Checker: "hoare-case". *)
val t_hoare_case : hoare_case -> backward
