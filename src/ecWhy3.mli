(* -------------------------------------------------------------------- *)
open EcSymbols

type env

val initialize : string option -> unit
(* To be called after initialize *)
val known_provers : unit -> string list
val empty : env

type rebinding_item
type rebinding = rebinding_item list

val rebind : env -> rebinding -> env

(* importing why3 theory *)

type renaming_kind =
  | RDts 
  | RDls
  | RDpr

type renaming_decl = (string list * renaming_kind * symbol) list

val import_w3 : 
    env -> EcPath.path -> 
      Why3.Theory.theory -> 
        renaming_decl -> EcTheory.theory * rebinding_item 

val add_ty : env -> EcPath.path -> EcDecl.tydecl -> env * rebinding_item

val add_op : 
    env -> EcPath.path -> EcDecl.operator -> env * rebinding_item

val add_ax : env -> EcPath.path -> EcDecl.axiom -> env * rebinding_item

val get_w3_th : string list -> string -> Why3.Theory.theory

(*****************************************************************************)
type prover_infos = 
  { prover_max_run   : int;
    prover_names     : string array;
    prover_timelimit : int; }    

val dft_prover_infos : prover_infos

val check_prover_name : string -> bool

val check_goal : env -> prover_infos -> EcFol.l_decl -> bool
