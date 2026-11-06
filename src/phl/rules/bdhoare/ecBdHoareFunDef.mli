(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_bdhoareF_fun_def] — a concrete procedure, by its body, with [~] the
   goal's comparison:

     phoare [body : P[arg := xs] ==> Q[res := e]] ~ d[arg := xs]
     -----------------------------------------------------------  f concrete
                     phoare [f : P ==> Q] ~ d

   where [f] (normalized) is [proc f(x1, ..., xn) = { body; return e }],
   [xs] is [(x1, ..., xn)] ([e] is [tt] when [f] returns nothing), in the
   memory of [f] extended with its parameters and locals. Side condition:
   [f] is not abstract (otherwise fails).

   Node: [RBdHoareFunDef]. Checker: "bdhoareF-fun-def". *)
val t_bdhoareF_fun_def : backward
