(* -------------------------------------------------------------------- *)
type options = {
  o_input      : string option;
  o_idirs      : string list;
  o_boot       : bool;
  o_emacs      : bool;
  o_why3       : string option;
  o_full_check : bool;
  o_max_prover : int;
  o_provers    : string list option;
}

(* -------------------------------------------------------------------- *)
val parse   : unit -> options
val options : options ref
