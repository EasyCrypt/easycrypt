(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree

open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)

(* Please, note that WP only operates over assignments and conditional
 * statements.  Any weakening of this restriction may break the
 * soundness of the bounded hoare logic.
 *)

val t_wp : ?uselet:bool -> (codepos1 doption) option -> backward

val process_wp : (codepos1 doption) option -> backward
