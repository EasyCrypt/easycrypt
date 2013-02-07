(* -------------------------------------------------------------------- *)
type options = {
  o_input      : string option;
  o_idirs      : string list;
  o_emacs      : bool;
  o_why3       : string option;
  o_full_check : bool;
}

(* -------------------------------------------------------------------- *)
val parse   : unit -> options
val options : options ref
