(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoareF_fun_def] — a concrete procedure, by its body:

     hoare [body : P[arg := (x1, ..., xn)] ==> Q[res := e] | E]
     ----------------------------------------------------------  f concrete
                     hoare [f : P ==> Q | E]

   where [f] (normalized) is [proc f(x1, ..., xn) = { body; return e }]
   ([e] is [tt] when [f] returns nothing), in the memory of [f] extended
   with its parameters and locals, and [E] are the exceptional
   postconditions of the goal, kept unchanged. Side condition: [f] is not
   abstract (otherwise fails).

   Node: [RHoareFunDef]. Checker: "hoareF-fun-def". *)
val t_hoareF_fun_def : backward
