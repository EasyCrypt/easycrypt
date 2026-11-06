(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_eagerF_fun_to_code] — an eager judgement, its procedures as single
   calls ([proc*]):

     equiv [s; r1 <@ f1(as1) ~ r2 <@ f2(as2); s' :
              P[arg<1> := as1, arg<2> := as2] ==> Q[res<1> := r1, res<2> := r2]]
     ---------------------------------------------------------------------------
                        eager [s, f1 ~ f2, s' : P ==> Q]

   where [asi] is [(a1, ..., an)], [a1 ... an] and [ri] being fresh local
   variables of the memory of side [i] (the parameters of [fi], unnamed
   ones named [arg<j>], and its result).

   Node: [REagerFunToCode]. Checker: "eagerF-fun-to-code". *)
val t_eagerF_fun_to_code : backward
