(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_ehoareF_fun_to_code] — a procedure, as a single call ([proc*]):

     ehoare [r <@ f(a1, ..., an) : P[arg := (a1, ..., an)] ==> Q[res := r]]
     -----------------------------------------------------------------------
                            ehoare [f : P ==> Q]

   where [a1 ... an] and [r] are fresh local variables of the memory (the
   parameters of [f], unnamed ones named [arg<i>], and its result).

   Node: [REHoareFunToCode]. Checker: "ehoareF-fun-to-code". *)
val t_ehoareF_fun_to_code : backward
