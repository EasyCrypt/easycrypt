(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
open EcAst
open EcEnv
open LDecl

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map

(* -------------------------------------------------------------------- *)
type circ
type cinput
type circuit = { circ: circ; inps: cinput list; }
type pstate = (symbol, circuit) Map.t
type cache  = (EcIdent.t, (cinput * circuit)) Map.t

(* -------------------------------------------------------------------- *)
exception CircError of string

(* -------------------------------------------------------------------- *)
val get_specification_by_name : string -> Lospecs.Ast.adef option
val circ_red : hyps -> EcReduction.reduction_info
val cinput_to_string : cinput -> string
val cinput_of_type : ?idn:ident -> env -> ty -> cinput
val width_of_type : env -> ty -> int 
val size_of_circ : circ -> int 
val compute : sign:bool -> circuit -> BI.zint list -> BI.zint
val circuit_to_string : circuit -> string
val circ_ident : cinput -> circuit
val circuit_ueq : circuit -> circuit -> circuit
val circuit_aggregate : circuit list -> circuit
val circuit_aggregate_inps : circuit -> circuit
val circuit_flatten : circuit -> circuit
val circuit_permutation : int -> int -> (int -> int) -> circuit 
val circuit_mapreduce : ?perm:(int -> int)  -> circuit -> int -> int -> circuit list
val circ_equiv : ?strict:bool -> circuit -> circuit -> circuit option -> bool
val circuit_of_form : ?pstate:pstate -> ?cache:cache -> hyps -> form -> circuit
val pstate_of_memtype : ?pstate:pstate -> env -> memtype -> pstate * cinput list
val input_of_variable : env -> variable -> circuit * cinput
val instrs_equiv : hyps -> memenv -> ?keep:EcPV.PV.t -> ?pstate:pstate -> instr list -> instr list -> bool
val process_instr : hyps -> memory -> ?cache:cache -> pstate -> instr -> (symbol, circuit) Map.t
