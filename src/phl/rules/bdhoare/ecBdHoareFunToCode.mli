(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_bdhoareF_fun_to_code] — a procedure, as a single call ([proc*]),
   with [~] the goal's comparison:

     phoare [r <@ f(as) : P[arg := as] ==> Q[res := r]] ~ d[arg := as]
     -----------------------------------------------------------------
                       phoare [f : P ==> Q] ~ d

   where [as] is [(a1, ..., an)], [a1 ... an] and [r] being fresh local
   variables of the memory (the parameters of [f], unnamed ones named
   [arg<i>], and its result).

   Node: [RBdHoareFunToCode]. Checker: "bdhoareF-fun-to-code". *)
val t_bdhoareF_fun_to_code : backward
