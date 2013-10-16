(* -------------------------------------------------------------------- *)
open EcParsetree
open EcEnv
open EcMemory
open EcModules
open EcFol
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)

(* Please, note that WP only operates over assignments and conditional
 * statements.  Any weakening of this restriction may break the
 * soundness of the bounded hoare logic.
 *)

class rn_hl_wp : int doption -> object
  inherit xrule

  method doption : int doption
end

val wp : env -> memory -> stmt -> form -> instr list * form
val t_wp : (int doption) option -> tactic
