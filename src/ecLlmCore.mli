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
   [goals] describe that restored state, not the point of failure.
   [changed] tells whether the engine uuid advanced -- a failing
   operation may well have moved the engine before failing. It reports
   the *net* effect of the call, so under [try_step] it is [false] for
   a phrase that advanced, failed and was rolled back: after the
   rollback there is nothing left to have changed. *)
type failure = {
  uuid     : int;
  message  : string;
  goals    : string;
  notices  : string;
  reverted : bool;
  changed  : bool;
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

(* Raw EasyCrypt input: one line, or a multi-line block. Every
   sentence the input holds is executed, in order, and a single reply
   describes the state they leave behind. A sentence that fails stops
   the run at that point and its failure is returned; the sentences
   before it stay applied, as they would in a compiled file. An
   [exit.] ends the session immediately, with the sentences that
   preceded it applied. *)
val step : state -> string -> answer

(* [step], but a failure leaves no trace: the engine is rolled back to
   the uuid it had on entry (as REVERT does) and the failure comes back
   with [reverted = true]. Successes and [Quit] behave exactly as in
   [step]. Input that fails after having already advanced the engine
   -- a phrase with a side effect, or an earlier sentence of a
   multi-sentence input -- is rolled back whole. *)
val try_step : state -> string -> answer

val goals      : state -> all:bool -> (reply, failure) result
val tree       : state -> all:bool -> (reply, failure) result
val focus      : state -> [`Next | `Path of int list] -> (reply, failure) result
val undo       : state -> (reply, failure) result
val revert     : state -> string -> (reply, failure) result
val checkpoint : state -> name:string -> (reply, failure) result
val commit     : state -> (reply, failure) result

(* SEARCH. [pattern] is a search pattern, not EasyCrypt input: the
   composed phrase is parsed here and refused unless it is exactly one
   toplevel [search] item, so a pattern carrying a sentence-ending '.'
   cannot smuggle further commands past it. Hence a [result] and not an
   [answer]: SEARCH runs a query and can never end the session. *)
val search     : state -> pattern:string -> (reply, failure) result

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
