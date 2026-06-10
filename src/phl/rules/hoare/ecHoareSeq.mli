(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
(* Hoare [seq] rule (TCB): split the statement at [i], with [phi] as the
   intermediate assertion. Emits a recheckable proof-node. *)
val t_hoare_seq : codegap1 -> ss_inv -> backward

(* Elaboration entry for a goal already known to be a [hoareS]: types the
   intermediate assertion and split position, then applies [t_hoare_seq]. *)
val process_hoare_seq : oside -> pcodegap1 -> pformula -> backward
