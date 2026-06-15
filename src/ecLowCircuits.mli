(* -------------------------------------------------------------------- *)
open EcBigInt
open EcSymbols
open EcIdent
open EcMemory

(* -------------------------------------------------------------------- *)
(* Low-level circuit interface: an AIG/QF_ABV circuit representation, the
   translation state, and the decision procedures, on top of an (opaque)
   backend. The backend, hash-consing tables, dependency analysis and SMT
   plumbing are intentionally hidden. *)

(* -------------------------------------------------------------------- *)
(* The backend's flattened circuit register (opaque). *)
type flatcirc

(* The type of a circuit value. *)
type ctype =
  | CArray of {width: int; count: int}
  | CBitstring of int
  | CTuple of ctype list
  | CBool

(* A circuit input. *)
type cinp = {
  type_ : ctype;
  id    : int;
  name  : string;  (* source-level name, for counter-model display *)
}

(* A circuit: a register together with its type. *)
type circ = {
  reg   : flatcirc;
  type_ : ctype;
}

(* A circuit function: a value together with its open inputs. *)
type 'a cfun = 'a * (cinp list)
type circuit = circ cfun

(* A satisfying assignment read back from the SMT solver: one value per
   input it materialized, as (id, value) pairs. The queries below return
   it lazily. *)
type model = (int * string) list

val pp_flatcirc : Format.formatter -> flatcirc -> unit

(* -------------------------------------------------------------------- *)
(* Arguments to (parametric) circuit operators. *)
type arg =
  [ `Circuit of circuit
  | `Constant of zint
  | `Init of int -> circuit
  | `List of circuit list ]

val arg_of_circuit  : circuit -> arg
val arg_of_zint     : zint -> arg
val arg_of_circuits : circuit list -> arg
val arg_of_init     : (int -> circuit) -> arg
val pp_arg          : Format.formatter -> arg -> unit

(* -------------------------------------------------------------------- *)
(* Translation state: bindings from program variables / locals to the
   circuits computing them, plus the circuit lambdas (open inputs). *)
type state

val empty_state : state

val update_state_pv     : state -> memory -> symbol -> circuit -> state
val state_get_pv_opt    : state -> memory -> symbol -> circuit option
val state_get_pv        : state -> memory -> symbol -> circuit
val state_get_all_memory : state -> memory -> (symbol * circuit) list
val state_get_all_pv    : state -> ((memory * symbol) * circuit) list

val update_state   : state -> ident -> circuit -> state
val state_get_opt  : state -> ident -> circuit option
val state_get      : state -> ident -> circuit
val state_bindings : state -> (ident * circuit) list
val state_lambdas  : state -> cinp list
val state_is_closed : state -> bool
val state_close_circuit : state -> circuit -> circuit
val map_state_var  : (ident -> circuit -> circuit) -> state -> state

(* Circuit lambdas, for managing inputs *)
val open_circ_lambda    : state -> (ident * ctype) list -> state
val open_circ_lambda_pv : state -> ((memory * symbol) * ctype) list -> state
val close_circ_lambda   : state -> state
val circ_lambda_oneshot : state -> (ident * ctype) list -> (state -> circuit) -> circuit

val set_logger : state -> (string -> unit) -> state
val log        : state -> string -> unit

(* -------------------------------------------------------------------- *)
(* Operator translation. *)
val bvget : circuit -> int -> circuit
val circuit_of_bvop : EcDecl.crb_bvoperator -> circuit
val circuit_of_parametric_bvop : EcDecl.crb_bvoperator -> arg list -> circuit

val array_get     : circuit -> int -> circuit
val array_set     : circuit -> int -> circuit -> circuit
val array_oflist  : circuit list -> circuit -> int -> circuit

(* -------------------------------------------------------------------- *)
(* Circuit type utilities *)
val size_of_ctype       : ctype -> int
val convert_type        : ctype -> circuit -> circuit
val can_convert_input_type : ctype -> ctype -> bool

(* Pretty printers *)
val pp_ctype   : Format.formatter -> ctype -> unit
val pp_cinp    : Format.formatter -> cinp -> unit
val pp_circ    : Format.formatter -> circ -> unit
val pp_circuit : Format.formatter -> circuit -> unit

(* General utilities *)
val circ_of_zint    : size:int -> zint -> circ
val circuit_of_zint : size:int -> zint -> circuit

(* Construct an input *)
val new_input_circuit : ?name:[`Str of string | `Idn of ident] -> ctype -> circ * cinp
val input_of_ctype    : ?name:[`Str of string | `Idn of ident] -> ctype -> circuit

(* Aggregation functions *)
val circuit_aggregate        : circuit list -> circuit
val circuit_aggregate_inputs : circuit -> circuit

(* Circuits representing booleans *)
val circuit_true  : circuit
val circuit_false : circuit
val circuit_and   : circuit -> circuit -> circuit
val circuit_or    : circuit -> circuit -> circuit
val circuit_not   : circuit -> circuit

(* <=> circuit has no inputs (every input is unbound) *)
val circuit_is_free : circuit -> bool

(* Direct circuit constructions *)
val circuit_ite : c:circuit -> t:circuit -> f:circuit -> circuit
val circuit_eq  : circuit -> circuit -> circuit
val circuit_eqs : circuit -> circuit -> circuit list

(* Circuit tuples *)
val circuit_tuple_proj        : circuit -> int -> circuit
val circuit_tuple_of_circuits : circuit list -> circuit
val circuits_of_circuit_tuple : circuit -> circuit list

(* Fresh arbitrary value (used for [witness] and unknown values) *)
val circuit_uninit            : ctype -> circuit

(* Logical reasoning over circuits *)
val circ_equiv : ?pcond:circuit -> circuit -> circuit -> bool * model Lazy.t
val circ_sat   : circuit -> bool * model Lazy.t
val circ_valid : circuit -> bool * model Lazy.t

(* Composition of circuit functions *)
val circuit_compose : circuit -> circuit list -> circuit

(* Computing the function given by a circuit *)
val compute : sign:bool -> circuit -> arg list -> zint option

(* Mapreduce / dependency-analysis related functions *)
val circuit_slice        : size:int -> circuit -> int -> circuit
val circuit_slice_insert : circuit -> int -> circuit -> circuit
val fillet_circuit       : circuit -> circuit list
val fillet_tauts         : ?logger:(string -> unit) -> circuit list -> circuit list -> bool
val batch_checks         :
     ?logger:(string -> unit)
  -> ?sort:bool
  -> ?mode:[`ByEq | `BySub]
  -> circuit list
  -> circuit list

val circuit_from_spec : ?name:symbol -> (ctype list * ctype) -> Lospecs.Ast.adef -> circuit

(* -------------------------------------------------------------------- *)
(* Reset the process-global backend state (AIG hash-cons table and the
   dependency cache). *)
val reset_backend_state : unit -> unit
