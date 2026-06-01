(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv
open LDecl
open EcPath
open EcLowCircuits

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map

(* -------------------------------------------------------------------- *)
(* [stopwatch env] returns a [lap msg] function reporting the time since
   the previous lap. A no-op unless the [Circuit:timing] flag is set. *)
val stopwatch : env -> (string -> unit)

(* -------------------------------------------------------------------- *)
type circuit_conversion_call = [
  | `Convert of form
  | `ToArg of form
  | `ExpandIter of form * form list
  | `Instr of instr
  | `Memenv of memenv
]


type circuit_error =
| MissingTyBinding of [`Ty of ty | `Path of path]
| AbstractTyBinding of [`Ty of ty | `Path of path]
| MissingOpBinding of path
| MissingOpSpec of path
| IntConversionFailure
| MissingOpBody of path 
| CantConvertToConstant
| CantReadWriteGlobs
| BadFormForArg of form
| CantConvertToCirc of 
  [ `Int 
  | `OpK of EcFol.op_kind 
  | `Op of path 
  | `Quantif of quantif
  | `Match
  | `Glob
  | `ModGlob
  | `Record
  | `Hoare
  | `Instr
] 
| PropagateError of circuit_conversion_call * circuit_error (* FIXME: make this lazy *)

exception CircError of circuit_error

val pp_circ_error : EcPrinting.PPEnv.t -> Format.formatter -> circuit_error -> unit

(* -------------------------------------------------------------------- *)
(* Utilities (figure out better name) *)
val circ_red : hyps -> EcReduction.reduction_info
val int_of_form : ?redmode:EcReduction.reduction_info -> hyps -> form -> BI.zint

(* Use circuits *)
val circ_taut  : circuit -> bool

(* Generate circuits *)
(* Form processors *)
val circuit_of_form : state -> hyps -> form -> circuit
val circuit_check_posts : env:env -> pres:circuit list -> circuit list -> bool
val circuits_of_equality : st:state -> hyps:hyps -> form -> form -> circuit list
val circ_simplify_form_bitstring_equality :
  ?st:state ->
  ?pres:circuit list -> hyps -> form -> form

(* Proc processors *)
val state_of_prog : ?close:bool -> hyps -> memory -> st:state -> instr list -> state
val instrs_equiv : hyps -> memenv -> ?keep:EcPV.PV.t -> state -> instr list -> instr list -> bool

val circuit_state_of_memenv : ?st:state -> env -> memenv -> state
val circuit_state_of_hyps : ?st:state -> ?strict:bool -> hyps -> state

(* Imperative state clearing *)
val clear_translation_caches : unit -> unit
