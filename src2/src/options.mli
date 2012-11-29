(* -------------------------------------------------------------------- *)
type options = {
  o_input : string option;
  o_idirs : string list;
}

(* -------------------------------------------------------------------- *)
val initial  : options
val add_idir : options -> string -> options

(* -------------------------------------------------------------------- *)
val parse : unit -> options
