(* -------------------------------------------------------------------- *)
(* Engine-facing core of the LLM interaction protocol: one operation per
   meta-command of the [easycrypt llm] REPL, with the text protocol
   factored out. Operations never print, never exit, and never format a
   wire envelope; they return structured values a front-end renders
   (the REPL in [ecLlm.ml], the MCP server next to it).

   One process = one session: the proof engine ([EcCommands]) is global
   mutable state, so at most one [state] may exist per process. *)

(* -------------------------------------------------------------------- *)
type state

(* Reply body. [Goals] means "the current goals"; the front-end renders
   them through [current_goals] and may suppress them (the REPL does,
   under QUIET). [Text] is a literal body and is never suppressed. *)
type body =
  | Goals
  | Text of string

(* [notices] are the engine messages emitted while the operation ran,
   captured and cleared at the point the REPL used to print them.
   [changed] tells whether the engine uuid advanced. *)
type reply = {
  uuid    : int;
  tag     : string;
  notices : string;
  body    : body;
  changed : bool;
}

(* [goals] is the goal state at the point of failure. The REPL does not
   render [notices] on failures (it never did); they are captured all
   the same, so the buffer is left clean for the next operation.
   [reverted] is set by [try_step] only: it says the engine was rolled
   back to the state it had before the operation ran, so [uuid] and
   [goals] describe that restored state, not the point of failure. *)
type failure = {
  uuid     : int;
  message  : string;
  goals    : string;
  notices  : string;
  reverted : bool;
}

(* Operations that can be asked to end the session ([exit.]) return an
   [answer]: the front-end owns the process, hence the exit. *)
type answer =
  | Done of (reply, failure) result
  | Quit

(* Raised by [create] when the session cannot be set up. *)
exception Init_error of string

(* -------------------------------------------------------------------- *)
(* Open a session: connect to the Why3 server, seed the loader with
   [relocdir], and initialize the engine. [projini] resolves the
   [easycrypt.project] context of a file path, so [load] can apply the
   project's load path and prover options the way the batch compiler
   does. *)
val create :
     relocdir:string option
  -> boot:bool
  -> projini:(string option -> EcOptions.ini_context option)
  -> prvopts:EcOptions.prv_options
  -> state

(* -------------------------------------------------------------------- *)
(* Operations. *)

(* LOAD, on already-parsed arguments. *)
val load :
     state
  -> file:string
  -> upto:(int * int option) option
  -> nosmt:bool
  -> trace:bool
  -> (reply, failure) result

(* One line of raw EasyCrypt input (or a multi-line block). *)
val step : state -> string -> answer

(* [step], but a failure leaves no trace: the engine is rolled back to
   the uuid it had on entry (as REVERT does) and the failure comes back
   with [reverted = true]. Successes and [Quit] behave exactly as in
   [step]. A phrase that fails after having already advanced the engine
   is rolled back whole. *)
val try_step : state -> string -> answer

val goals      : state -> all:bool -> (reply, failure) result
val tree       : state -> all:bool -> (reply, failure) result
val focus      : state -> [`Next | `Path of int list] -> (reply, failure) result
val undo       : state -> (reply, failure) result
val revert     : state -> string -> (reply, failure) result
val checkpoint : state -> name:string -> (reply, failure) result
val commit     : state -> (reply, failure) result
val search     : state -> pattern:string -> answer

(* -------------------------------------------------------------------- *)
(* Front-end helpers: for replies a front-end produces on its own (the
   REPL's HELP and QUIET) and for errors it detects itself (line-parse
   errors). Both capture-and-clear the notice buffer, as the operations
   above do. *)

val uuid          : state -> int
val current_goals : state -> string
val clear_notices : state -> unit
val make_reply    : state -> ?tag:string -> body -> reply
val make_failure  : state -> string -> failure
