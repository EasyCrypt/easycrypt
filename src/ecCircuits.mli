(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
open EcAst
open EcEnv
open LDecl
open EcLowCircuits

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map

(* -------------------------------------------------------------------- *)
exception CircError of string

(* -------------------------------------------------------------------- *)
(* Utilities (figure out better name) *)
val circ_red : hyps -> EcReduction.reduction_info
val width_of_type : env -> ty -> int 
val circuit_to_string : circuit -> string
val ctype_of_ty : env -> ty -> ctype

(* State utilities *)
val state_get : state -> memory -> symbol -> circuit
val state_get_opt : state -> memory -> symbol -> circuit option
val state_get_all : state -> circuit list 

(* Create circuits *)
val input_of_type : name:[`Str of string | `Idn of ident | `Bad] -> env -> ty -> circuit

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
val circuit_of_form : ?st:state -> hyps -> form -> hyps * circuit
val circ_simplify_form_bitstring_equality :
  ?st:state ->
  ?pcond:circuit -> hyps -> form -> form
 
(* Proc processors *)
val state_of_prog : hyps -> memory -> ?st:state -> instr list -> variable list -> hyps * state 
val instrs_equiv : hyps -> memenv -> ?keep:EcPV.PV.t -> ?st:state -> instr list -> instr list -> bool
val process_instr : hyps -> memory -> st:state -> instr -> hyps * state
(* val pstate_of_memtype : ?pstate:pstate -> env -> memtype -> pstate * cinput list *)

val circuit_state_of_hyps : ?st:state -> hyps -> state 

(* Check for uninitialized inputs *)
val circuit_has_uninitialized : circuit -> int option

val circuit_slice : circuit -> int -> int -> circuit
val circuit_align_inputs : circuit -> (int * int) option list -> circuit 

val circuit_to_file : name:string -> circuit -> symbol
