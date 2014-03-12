(* -------------------------------------------------------------------- *)
open EcParsetree
open EcEnv
open EcMemory
open EcModules
open EcFol

open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)

(* Please, note that WP only operates over assignments and conditional
 * statements.  Any weakening of this restriction may break the
 * soundness of the bounded hoare logic.
 *)

val wp : ?onesided:bool -> env -> memory -> stmt -> form -> instr list * form

val t_wp : (int doption) option -> backward
