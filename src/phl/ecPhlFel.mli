(* -------------------------------------------------------------------- *)
open EcPath
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_failure_event :
     int
  -> form -> form -> form -> form
  -> (xpath * form) list
  -> form
  -> backward

(* -------------------------------------------------------------------- *)
type pfel_t =
    pformula
  * pformula
  * pformula
  * pformula
  * (pgamepath * pformula) list
  * pformula option

val process_fel : int -> pfel_t -> backward
