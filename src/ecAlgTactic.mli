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
val t_cut_ring_congr : 
  cring -> RState.rstate -> pexpr -> int list -> EcFol.form list -> tactic
val t_cut_ring_norm :
  cring -> RState.rstate -> (pexpr * pexpr) list -> pexpr -> tactic
val t_ring : ring -> eqs -> form * form -> tactic
val t_ring_simplify : ring -> eqs -> form * form -> tactic

val t_field : field -> eqs -> form * form -> tactic
val t_field_simplify : field -> eqs -> form * form -> tactic
