(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
open EcAst
open EcEnv
open LDecl

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map

(* -------------------------------------------------------------------- *)
type circuit 
type pstate
type cache

(* -------------------------------------------------------------------- *)
exception CircError of string

(* -------------------------------------------------------------------- *)
(* Utilities (figure out better name) *)
val circ_red : hyps -> EcReduction.reduction_info
val width_of_type : env -> ty -> int 
val circuit_to_string : circuit -> string
val get_specification_by_name : string -> Lospecs.Ast.adef option

(* Pstate utilities *)
val pstate_get : pstate -> symbol -> circuit
val pstate_get_opt : pstate -> symbol -> circuit option
val pstate_get_all : pstate -> circuit list 

(* Cache utilities *)
val cache_get : cache -> ident -> circuit
val cache_add : cache -> ident -> circuit -> cache
val empty_cache : cache

(* Transform circuits *)
val circuit_ueq : circuit -> circuit -> circuit
val circuit_aggregate : circuit list -> circuit
val circuit_aggregate_inps : circuit -> circuit
val circuit_flatten : circuit -> circuit
val circuit_permute : int -> (int -> int) -> circuit -> circuit 
val circuit_mapreduce : ?perm:(int -> int)  -> circuit -> int -> int -> circuit list

(* Use circuits *)
val compute    : sign:bool -> circuit -> BI.zint list -> BI.zint
val circ_equiv : ?pcond:circuit -> circuit -> circuit -> bool
val circ_sat   : circuit -> bool 
val circ_taut  : circuit -> bool 

(* Generate circuits *)
(* Form processors *)
val circuit_of_form : ?pstate:pstate -> ?cache:cache -> hyps -> form -> circuit
val circ_simplify_form_bitstring_equality :
  ?mem:EcMemory.memory ->
  ?pstate:pstate ->
  ?pcond:circuit -> hyps -> form -> form
 
(* Proc processors *)
val pstate_of_prog : hyps -> memory -> instr list -> variable list -> pstate 
val instrs_equiv : hyps -> memenv -> ?keep:EcPV.PV.t -> ?pstate:pstate -> instr list -> instr list -> bool
val process_instr : hyps -> memory -> pstate -> instr -> pstate
(* val pstate_of_memtype : ?pstate:pstate -> env -> memtype -> pstate * cinput list *)

(* Temporary? *)
val circuit_of_form_with_hyps : ?pstate:pstate -> ?cache:cache -> hyps -> form -> circuit 
