(* -------------------------------------------------------------------- *)
open EcSymbols
open EcTypes
open EcFol
open EcLogic
open EcRing
open EcAlgebra

(* -------------------------------------------------------------------- *)
val is_module_loaded : EcEnv.env -> bool

(* -------------------------------------------------------------------- *)
val ring_symbols  : EcEnv.env -> bool -> ty -> (symbol * (bool * ty)) list
val field_symbols : EcEnv.env -> ty -> (symbol * (bool * ty)) list

val ring_axioms  : EcEnv.env -> ring  -> (symbol * form) list
val field_axioms : EcEnv.env -> field -> (symbol * form) list

(* -------------------------------------------------------------------- *)
val n_ring_congr : 
  judgment_uc -> EcEnv.LDecl.hyps ->
  cring -> RState.rstate ->
  form -> int list -> form list ->
    form * int * EcLogic.goals

val n_ring_norm :
  judgment_uc ->  EcEnv.LDecl.hyps ->
  cring -> RState.rstate ->
  form ->
  RState.rstate * form * int * EcLogic.goals

val t_ring : ring -> eqs -> form * form -> tactic
val t_ring_simplify : ring -> eqs -> form * form -> tactic

val t_field : field -> eqs -> form * form -> tactic
val t_field_simplify : field -> eqs -> form * form -> tactic
