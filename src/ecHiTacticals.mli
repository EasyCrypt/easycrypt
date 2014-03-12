(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcHiGoal

(* -------------------------------------------------------------------- *)
val process1 : ttenv -> ptactic -> FApi.backward
val process  : ttenv -> ptactic list -> proof -> proof
