(* -------------------------------------------------------------------- *)
type options = {
  o_input : string option;
  o_idirs : string list;
  o_emacs : bool;
}

(* -------------------------------------------------------------------- *)
val parse   : unit -> options
val options : options ref
