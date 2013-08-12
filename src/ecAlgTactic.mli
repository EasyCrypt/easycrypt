(* -------------------------------------------------------------------- *)
open EcSymbols
open EcFol
open EcLogic
open EcAlgebra

(* -------------------------------------------------------------------- *)
val ring_axioms  : EcEnv.env -> ring  -> (symbol * form) list
val field_axioms : EcEnv.env -> field -> (symbol * form) list

(* -------------------------------------------------------------------- *)
val t_ring : ring -> eqs -> form * form -> tactic
val t_ring_simplify : ring -> eqs -> form * form -> tactic

val t_field : field -> eqs -> form * form -> tactic
val t_field_simplify : field -> eqs -> form * form -> tactic
