(* -------------------------------------------------------------------- *)
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* [t_delay] turns an equivS / equivF goal into the corresponding
   dcoupl judgment with empty delay / continuation contexts.          *)
val t_delay : FApi.backward

(* [t_undelay] is the inverse: it closes a dcoupl goal whose delay and
   continuation contexts are all empty by falling back to the pRHL
   judgment.                                                           *)
val t_undelay : FApi.backward
