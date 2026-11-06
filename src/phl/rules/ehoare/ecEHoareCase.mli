(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type ehoare_case = {
  ehca_cond : ss_inv;   (* case formula f *)
}

(* [t_ehoare_case { ehca_cond = f }] — case analysis on [f]:

     ehoare [c : (f `|` P) ==> Q]      ehoare [c : (!f `|` P) ==> Q]
     ----------------------------------------------------------------
                        ehoare [c : P ==> Q]

   where [(f `|` P)] is the expectation [P] where [f] holds, [+oo]
   elsewhere.

   Node: [REHoareCase { ehca_cond = f }]. Checker: "ehoare-case". *)
val t_ehoare_case : ehoare_case -> backward
