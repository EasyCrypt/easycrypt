(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcParsetree
open EcMatching.Position

open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)

(* Please, note that WP only operates over assignments and conditional
 * statements.  Any weakening of this restriction may break the
 * soundness of the bounded hoare logic.
 *)

val t_wp : ?uselet:bool -> (codegap1 doption) option -> backward

val process_wp : (pcodegap1 doption) option -> backward

(* Low-level WP: computes the weakest-precondition of [s] with respect
   to the exn-post [poe] in memory [m]. Returns leftover prefix and
   the resulting formula. Used by other logics that need WP over
   assignments / conditionals.                                         *)
val wp :
  ?mc:(memory * memory)
  -> ?uselet:bool
  -> ?onesided:bool
  -> ?c_pre:form
  -> EcEnv.LDecl.hyps
  -> memenv
  -> stmt
  -> exnpost
  -> instr list * form
