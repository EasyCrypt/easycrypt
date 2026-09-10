(* -------------------------------------------------------------------- *)
(* Model Context Protocol server over stdio: a second front-end, next to
   the [easycrypt llm] REPL, over the shared engine core in
   [EcLlmCore]. Driven via the [easycrypt mcp] command. *)

module J = Yojson.Safe

(* Serve JSON-RPC 2.0 messages on stdin/stdout until end of input, then
   exit the process. Never returns. [projini] resolves the
   [easycrypt.project] context of a file path, as for the REPL. *)
val run :
     relocdir:string option
  -> boot:bool
  -> projini:(string option -> EcOptions.ini_context option)
  -> EcOptions.mcp_option
  -> 'a

(* -------------------------------------------------------------------- *)
(* The pieces the session multiplexer ([EcMcpMux]) shares with the
   single-engine server, so that the two front doors answer alike. *)

val protocol_latest : string
val protocol_supported : string list
val server_name : string
val server_version : string

val e_parse_error : int
val e_invalid_request : int
val e_method_not_found : int
val e_invalid_params : int

(* A [tools/call] whose arguments violate the declared schema. *)
exception Invalid_params of string

val print_usage : unit -> unit

(* One JSON-RPC message per line. [writer oc] sends on [oc]; [Over]
   builds the reply helpers over any [send]. *)
module Wire : sig
  val repair : J.t -> J.t
  val writer : out_channel -> J.t -> unit
  val result_msg : J.t -> J.t -> J.t
  val error_msg : ?data:J.t -> J.t -> int -> string -> J.t
  module Over (C : sig val send : J.t -> unit end) : sig
    val send : J.t -> unit
    val result : J.t -> J.t -> unit
    val error : ?data:J.t -> J.t -> int -> string -> unit
  end
end

(* A private descriptor for the protocol; the process's stdout is
   pointed at stderr. Call once, before anything can print. *)
val wire_stdout : unit -> out_channel

module Schema : sig
  val str : ?description:string -> unit -> J.t
  val obj : ?required:string list -> (string * J.t) list -> J.t
end

(* The tool table, and the same table with a required [session]
   argument on every tool. *)
val tools : J.t list
val tools_with_session : J.t list

module Args : sig
  val of_params : J.t option -> (string * J.t) list
  val arguments : J.t option -> (string * J.t) list
end

(* The [initialize] result for the given request parameters. *)
val initialize_result : J.t option -> J.t
