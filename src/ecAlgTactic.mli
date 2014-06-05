(* -------------------------------------------------------------------- *)
open EcSymbols
open EcTypes
open EcDecl
open EcFol
open EcAlgebra
open EcCoreGoal

(* -------------------------------------------------------------------- *)
val is_module_loaded : EcEnv.env -> bool

(* -------------------------------------------------------------------- *)
val ring_symbols  : EcEnv.env -> bool -> ty -> (symbol * (bool * ty)) list
val field_symbols : EcEnv.env -> ty -> (symbol * (bool * ty)) list

val ring_axioms  : EcEnv.env -> ring  -> (symbol * form) list
val field_axioms : EcEnv.env -> field -> (symbol * form) list

(* -------------------------------------------------------------------- *)
val t_ring : ring -> eqs -> form * form -> FApi.backward
val t_ring_simplify : ring -> eqs -> form * form -> FApi.backward
val t_ring_congr : cring -> RState.rstate ->
           EcRing.pexpr -> int list -> form list -> FApi.backward 

val t_field : field -> eqs -> form * form -> FApi.backward
val t_field_simplify : field -> eqs -> form * form -> FApi.backward
val t_field_congr : cfield -> RState.rstate ->
           EcField.fexpr -> int list -> form list -> FApi.backward 
