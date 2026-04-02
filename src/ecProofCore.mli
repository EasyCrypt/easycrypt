type position = {
  line : int;
  character : int;
}

type range = {
  start_ : position;
  end_ : position;
}

type text_change = {
  range : range option;
  text : string;
}

type proof_response = {
  output : string;
  uuid : int;
  mode : string;
  processed_end : int;
  sentence_start : int option;
  sentence_end : int option;
}

type query_kind = [ `Print | `Locate | `Search ]

type query_response = {
  output : string;
}

type t

val create :
     ?log:(string -> unit)
  -> cli_path:string
  -> cli_args:string list
  -> unit
  -> t

val did_open : t -> uri:string -> text:string -> unit
val did_change : t -> uri:string -> text_change list -> unit Lwt.t
val did_close : t -> uri:string -> unit Lwt.t
val close : t -> unit Lwt.t

val proof_next : t -> uri:string -> proof_response Lwt.t
val proof_step : t -> uri:string -> proof_response Lwt.t
val proof_jump_to : t -> uri:string -> target:int -> proof_response Lwt.t
val proof_back : t -> uri:string -> proof_response Lwt.t
val proof_restart : t -> uri:string -> proof_response Lwt.t
val proof_goals : t -> uri:string -> proof_response Lwt.t

val query : t -> uri:string -> kind:query_kind -> query:string -> query_response Lwt.t
