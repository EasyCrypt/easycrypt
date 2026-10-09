(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_ehoareF_fun_def] — a concrete procedure, by its body:

     ehoare [body : P[arg := (x1, ..., xn)] ==> Q[res := e]]
     -------------------------------------------------------  f concrete
                     ehoare [f : P ==> Q]

   where [f] (normalized) is [proc f(x1, ..., xn) = { body; return e }]
   ([e] is [tt] when [f] returns nothing), in the memory of [f] extended
   with its parameters and locals. Side condition: [f] is not abstract
   (otherwise fails).

   Node: [REHoareFunDef]. Checker: "ehoareF-fun-def". *)
val t_ehoareF_fun_def : backward
