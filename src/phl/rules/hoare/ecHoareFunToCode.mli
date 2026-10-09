(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoareF_fun_to_code] — a procedure, as a single call ([proc*]):

     hoare [r <@ f(a1, ..., an) : P[arg := (a1, ..., an)] ==> Q[res := r] | E]
     -------------------------------------------------------------------------
                            hoare [f : P ==> Q | E]

   where [a1 ... an] and [r] are fresh local variables of the memory (the
   parameters of [f], unnamed ones named [arg<i>], and its result), and
   [E] are the exceptional postconditions of the goal, kept unchanged.

   Node: [RHoareFunToCode]. Checker: "hoareF-fun-to-code". *)
val t_hoareF_fun_to_code : backward
