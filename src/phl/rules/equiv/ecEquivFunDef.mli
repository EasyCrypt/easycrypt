(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_equivF_fun_def] — two concrete procedures, by their bodies:

     equiv [body1 ~ body2 : P[arg<1> := xs1, arg<2> := xs2]
                        ==> Q[res<1> := e1, res<2> := e2]]
     ------------------------------------------------------  f1, f2 concrete
                  equiv [f1 ~ f2 : P ==> Q]

   where [fi] (normalized) is [proc fi(xs_i) = { body_i; return e_i }]
   ([e_i] is [tt] when [fi] returns nothing), in the memory of [fi]
   extended with its parameters and locals. Side condition: neither
   procedure is abstract (otherwise fails).

   Node: [REquivFunDef]. Checker: "equivF-fun-def". *)
val t_equivF_fun_def : backward
