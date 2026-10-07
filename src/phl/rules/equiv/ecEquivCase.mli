(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_case = {
  eca_cond     : ts_inv;   (* case relation f *)
  eca_simplify : bool;     (* conjoin with the simplifying conjunction *)
}

(* [t_equiv_case { eca_cond = f; eca_simplify }] — case analysis on [f]:

     equiv [c ~ c' : P /\ f ==> Q]      equiv [c ~ c' : P /\ !f ==> Q]
     ----------------------------------------------------------------
                        equiv [c ~ c' : P ==> Q]

   where [/\] is [f_and_simpl] when [eca_simplify], [f_and] otherwise.

   Node: [REquivCase { eca_cond = f; eca_simplify }]. Checker: "equiv-case". *)
val t_equiv_case : equiv_case -> backward
