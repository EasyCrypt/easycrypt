(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(** Proof sessions *)

open Why3

(** {2 Prover's data} *)

type prover_data = private
    { prover_id : string;
      prover_name : string;
      prover_version : string;
      command : string;
      driver_name : string;
      driver : Driver.driver;
      mutable editor : string;
      interactive : bool;
    }
    (** record of necessary data for a given external prover *)

(* stays here until old IDE is deleted *)
val get_prover_data :
  Env.env -> Util.Mstr.key -> Whyconf.config_prover ->
  prover_data Util.Mstr.t -> prover_data Util.Mstr.t
  (** loads all provers from the current configuration *)


(** {2 Transformation's data} *)

type transformation_data
  (** record data for transformations *)

val transformation_id : transformation_data -> string
  (** Why3 name of a transformation *)

val lookup_transformation : Env.env -> string -> transformation_data
  (** returns a transformation from its Why3 name *)

(** {2 Proof attempts} *)

type proof_attempt_status = private
    | Undone
    | Scheduled (** external proof attempt is scheduled *)
    | Interrupted
    | Running (** external proof attempt is in progress *)
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)
    | Unedited (** interactive prover yet no proof script *)

(** {2 Observers signature} *)

module type OBSERVER = sig

  type key
    (** type key allowing to uniquely identify an element of
        of session: a goal, a transformation, a proof attempt,
        a theory or a file. See type [any] below *)

  val create: ?parent:key -> unit -> key
    (** returns a fresh key, a new child of the given parent if any *)

  val remove: key -> unit
    (** removes a key *)

  val reset: unit -> unit
    (** deletes all keys *)

  val timeout: ms:int -> (unit -> bool) -> unit
    (** a handler for functions that must be called after a given time
        elapsed, in milliseconds. When the given function returns
        true, it must be rescheduled *)

  val idle: (unit -> bool) -> unit
    (** a handler for a delayed function, that can be called when
        there is nothing else to do. When the given function returns
        true, it must be rescheduled *)

  val notify_timer_state : int -> int -> int -> unit
    (** this function is called when timer state changes.
        The first arg is the number of tasks waiting.
        The second arg is the number of scheduled proof tasks.
        The third arg is the number of running proof tasks *)
end

(** {2 Main functor} *)

module Make(O: OBSERVER) : sig

(** {2 static state of a session} *)

  type goal
    (** a goal *)

  type transf = private
      { transf : transformation_data;
        parent_goal : goal;
        mutable transf_proved : bool;
        transf_key : O.key;
        mutable subgoals : goal list;
        mutable transf_expanded : bool;
      }
    (** a transformation of a given goal *)

  val set_transf_expanded : transf -> bool -> unit

  val goal_name : goal -> string
  val goal_expl : goal -> string
  val get_task : goal -> Task.task
  val goal_key : goal -> O.key
  val goal_proved : goal -> bool
  val transformations : goal -> (string, transf) Hashtbl.t
  val goal_expanded : goal -> bool
  val set_goal_expanded : goal -> bool -> unit

  type prover_option =
    | Detected_prover of prover_data
    | Undetected_prover of string

  type proof_attempt = private
      { prover : prover_option;
        proof_goal : goal;
        proof_key : O.key;
        mutable proof_state : proof_attempt_status;
        mutable timelimit : int;
        mutable proof_obsolete : bool;
        mutable edited_as : string;
      }
    (** a proof attempt for a given goal *)

  val external_proofs : goal -> (string, proof_attempt) Hashtbl.t

  type theory
    (** a theory, holding a collection of goals *)

  val theory_name : theory -> string
  val get_theory : theory -> Theory.theory
  val theory_key : theory -> O.key
  val verified : theory -> bool
  val goals : theory -> goal list
  val theory_expanded : theory -> bool
  val set_theory_expanded : theory -> bool -> unit

  type file = private
      { file_name : string;
        file_key : O.key;
        mutable theories: theory list;
        mutable file_verified : bool;
        mutable file_expanded : bool;
      }

  val set_file_expanded : file -> bool -> unit

  type any =
    | File of file
    | Theory of theory
    | Goal of goal
    | Proof_attempt of proof_attempt
    | Transformation of transf


(** {2 Save and load a state}      *)

  exception OutdatedSession

  val open_session :
    allow_obsolete:bool ->
    env:Env.env ->
    config:Whyconf.config ->
    init:(O.key -> any -> unit) ->
    notify:(any -> unit) ->
    string -> bool
    (** starts a new proof session, using directory given as argument
        this reloads the previous session database if any.

        Opening a session must be done prior to any other actions.
        And it cannot be done twice.

        the [notify] function is a function that will be called at each
        update of element of the state

        the [init] function is a function that will be called at each
        creation of element of the state

        raises [OutdatedSession] if [allow_obsolete] is false and any obsolete
        data for a goal is found in the session database

        raises [Failure msg] if the database file cannot be read correctly

        returns true if some obsolete goal was found (and
        [allow_obsolete] is true), false otherwise

    *)

  val get_provers : unit -> prover_data Util.Mstr.t

  val maximum_running_proofs : int ref

  val save_session : unit -> unit
    (** enforces to save the session state on disk.
        this it supposed to be called only at exit,
        since the session manager also performs automatic saving
        some time to time *)

  val file_exists : string -> bool

  val add_file : string -> unit
    (** [add_file f] adds the file [f] in the proof session,
        the file name must be given relatively to the session dir
        given to [open_session] *)


  val get_all_files : unit -> file list

(** {2 Actions} *)


  val apply_transformation : callback:(Task.task list -> unit) ->
    transformation_data -> Task.task -> unit

  val run_prover : context_unproved_goals_only:bool ->
    timelimit:int -> prover_data -> any -> unit
    (** [run_prover p a] runs prover [p] on all goals under [a]
        the proof attempts are only scheduled for running, and they
        will be started asynchronously when processors are available
    *)

  val cancel_scheduled_proofs : unit -> unit
    (** cancels all currently scheduled proof attempts.
        note that the already running proof attempts are not
        stopped, the corresponding processes must terminate
        by their own. *)

  val transform : context_unproved_goals_only:bool ->
    transformation_data -> any -> unit
    (** [apply_transformation tr a] applies transformation [trp]
        on all goals under [a] *)

  val edit_proof :
    default_editor:string -> project_dir:string -> proof_attempt -> unit
    (** edit the given proof attempt using the appropriate editor *)

  val replay :
    obsolete_only:bool ->
    context_unproved_goals_only:bool -> any -> unit
    (** [replay a] reruns proofs under [a]
        if obsolete_only is set then does not rerun non-obsolete proofs
        if context_unproved_goals_only is set then reruns only proofs
        with result was 'valid'
    *)

  val cancel : any -> unit
    (** [cancel a] marks all proofs under [a] as obsolete *)

  type report =
    | Wrong_result of Call_provers.prover_result * Call_provers.prover_result
    | CallFailed of exn
    | Prover_not_installed
    | No_former_result

  val check_all: callback:((string * string * report) list -> unit) -> unit
    (** [check_all ()] reruns all the proofs of the session, and reports
        all difference with the current state
        (does not change the session state)
        When finished, calls the callback with the list of failed comparisons,
        which are triples (goal name, prover, report)
    *)

  val reload_all: bool -> bool
    (** reloads all the files
        If for one of the file, the parsing or typing fails, then
        the complete old session state is kept, and an exception
        is raised

        raises [OutdatedSession] if [allow_obsolete] is false and any obsolete
        data for a goal is found in the session database

        returns true if some obsolete goal was found (and
        [allow_obsolete] is true), false otherwise

    *)

  val remove_proof_attempt : proof_attempt -> unit

  val remove_transformation : transf -> unit

  val clean : any -> unit
    (** [clean a] removes failed attempts below [a] where
        there at least one successful attempt or transformation *)

end



(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
