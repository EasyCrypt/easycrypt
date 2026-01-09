(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
open EcAst
open EcEnv
open LDecl
open EcPath
open EcLowCircuits

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map

(* -------------------------------------------------------------------- *)
exception CircError of string Lazy.t
exception MissingTyBinding of ty
exception AbstractTyBinding of ty
exception InvalidArgument
exception MissingOpBinding of path
exception MissingOpSpec of path
exception IntConversionFailure 
exception DestrError of string (* FIXME: change this one *)
exception MissingOpBody (* FIXME: rename? *)
exception BadFormForArg (* FIXME: rename *)
exception CantConvertToConstant
exception CantConvertToCirc of 
  [`Int 
  | `OpK of EcFol.op_kind 
  | `Op of path 
  | `Quantif of quantif
  | `Match
  | `Glob
  | `Record
  | `Hoare
  | `Instr
] 

(* -------------------------------------------------------------------- *)
(* Utilities (figure out better name) *)
val circ_red : hyps -> EcReduction.reduction_info
val width_of_type : env -> ty -> int 
val circuit_to_string : circuit -> string
val ctype_of_ty : env -> ty -> ctype
val int_of_form : ?redmode:EcReduction.reduction_info -> hyps -> form -> BI.zint

(* State utilities *)
val state_get : state -> memory -> symbol -> circuit
val state_get_opt : state -> memory -> symbol -> circuit option
val state_get_all : state -> circuit list 

(* Create circuits *)
val input_of_type : name:[`Str of string | `Idn of ident | `Bad] -> env -> ty -> circuit

(* Transform circuits *)
val circuit_ueq : circuit -> circuit -> circuit
val circuit_flatten : circuit -> circuit

(* Use circuits *)
val compute    : sign:bool -> circuit -> BI.zint list -> BI.zint
val circ_equiv : ?pcond:circuit -> circuit -> circuit -> bool
val circ_sat   : circuit -> bool 
val circ_taut  : circuit -> bool 

(* Generate circuits *)
(* Form processors *)
val circuit_of_form : ?st:state -> hyps -> form -> circuit
val circuit_simplify_equality : ?do_time:bool -> st:state -> hyps:hyps -> pres:circuit list -> form -> form -> bool
val circ_simplify_form_bitstring_equality :
  ?st:state ->
  ?pres:circuit list -> hyps -> form -> form
 
(* Proc processors *)
val state_of_prog : ?me:memenv -> hyps -> memory -> ?st:state -> instr list -> state 
val instrs_equiv : hyps -> memenv -> ?keep:EcPV.PV.t -> ?st:state -> instr list -> instr list -> bool
val process_instr : ?me:memenv -> hyps -> memory -> st:state -> instr -> state
(* val pstate_of_memtype : ?pstate:pstate -> env -> memtype -> pstate * cinput list *)

val circuit_state_of_memenv : st:state -> env -> memenv -> state
val circuit_state_of_hyps : ?strict:bool -> ?use_mem:bool -> ?st:state -> hyps -> state 

(* Check for uninitialized inputs *)
val circuit_has_uninitialized : circuit -> int option

val circuit_slice : circuit -> int -> int -> circuit

val circuit_to_file : name:string -> circuit -> symbol

(* Imperative state clearing *)
val clear_translation_caches : unit -> unit
