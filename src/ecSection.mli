(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv
open EcTheory

(* -------------------------------------------------------------------- *)
exception SectionError of string

(* -------------------------------------------------------------------- *)
type scenv

val env : scenv -> env

val initial : env -> scenv

val add_item     : ?override_locality:EcTypes.is_local option -> theory_item -> scenv -> scenv
val add_decl_mod : EcIdent.t -> mty_mr -> scenv -> scenv

val enter_section : EcSymbols.symbol option -> scenv -> scenv
val exit_section  : EcSymbols.symbol option -> scenv -> scenv

val enter_theory : EcSymbols.symbol -> EcTypes.is_local -> thmode -> scenv -> scenv

val exit_theory  :
  ?clears:EcPath.path list ->
  ?pempty:[ `ClearOnly | `Full | `No ] ->
  scenv -> EcSymbols.symbol * EcEnv.Theory.compiled_theory option * scenv

val import : EcPath.path -> scenv -> scenv

val import_vars : EcPath.mpath -> scenv -> scenv

val add_th  : import:import -> EcEnv.Theory.compiled_theory -> scenv -> scenv
val require : EcEnv.Theory.compiled_theory -> scenv -> scenv

val astop : scenv -> scenv
