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

open Why3

(** Proof database *)

(** {2 data types} *)

type prover_id
(** a prover identifier *)

module Hprover : Hashtbl.S with type key = prover_id

type transf_id
(** a transformation identifier *)

module Htransf : Hashtbl.S with type key = transf_id

type file
(** a database contains a (ordered?) set of files *)

type theory
(** each files contains an ordered sequence of theories *)

type goal
(** each theory contains an ordered sequences of goals *)

type proof_attempt
(** each goal has a set of proof attempts, indeed a map indexed
    by prover identifiers *)

type transf
(** each goal also has a set of transformations, indeed a map indexed
    by transformation identifiers *)


(** status of an external proof attempt *)

type proof_status =
  | Undone                      (** external proof attempt not done yet *)
  | Done of Call_provers.prover_answer  (** external proof attempt done *)

(** parent of a goal: either a theory (for "toplevel" goals)
    or a transformation (for "subgoals") *)
(* useful ?
type goal_parent =
  | Theory of theory
  | Transf of transf
*)

(** {2 accessors} *)

(** prover_id accessors *)
val prover_name : prover_id -> string

(** transf_id accessors *)
val transf_name : transf_id -> string

(** proof_attempt accessors *)
(*
val prover : proof_attempt -> prover_id
*)
(*
val proof_goal : proof_attempt -> goal
*)
val status_and_time :
  proof_attempt -> proof_status * float * bool * string
  (** returns (status, time, obsolete flag, edited file name) *)

val edited_as : proof_attempt -> string

(** goal accessors *)
(*
val parent : goal -> goal_parent
*)
val goal_name : goal -> string
val task_checksum : goal -> string (** checksum *)
(*
val proved : goal -> bool
*)
val external_proofs: goal -> proof_attempt Hprover.t
val transformations : goal -> transf Htransf.t

(** transf accessors *)
(*
val parent_goal : transf -> goal
*)
(*
val transf_id : transf -> transf_id
*)
val subgoals : transf -> goal Util.Mstr.t
(** key are md5sum *)

(** theory accessors *)
val theory_name : theory -> string
val goals : theory -> goal Util.Mstr.t
(** keys are goal name *)
(*
val verified : theory -> bool
*)

(** file accessors *)
(*
val file_name : file -> string
*)
val theories : file -> theory Util.Mstr.t

(** {2 The persistent database} *)

val init_base : string -> unit
(** opens or creates the current database, from given file name *)

val is_initialized : unit -> bool
(** [is_initialized ()] is true if init_base as been called
    succesively previously *)

val db_name : unit -> string
(** [db_name ()] return the path of the database *)

val files : unit -> (file * string) list
(** returns the current set of files, with their filenames *)


(** {2 Updates} *)

exception AlreadyExist

(** {3 prover id} *)
val prover_from_name : string -> prover_id
(** retrieves existing prover id from its name.
    creates prover id if not existing yet *)

(** {3 transf id} *)
val transf_from_name : string -> transf_id
(** retrieves existing transformation id from its name.
    creates it if not existing yet *)

(** {3 external proof attempts} *)

val add_proof_attempt : goal -> prover_id -> proof_attempt
(** adds a proof attempt for this prover, with status is set to Unknown.
    @raise AlreadyExist if an attempt for the same prover
    is already there *)

val remove_proof_attempt : proof_attempt -> unit
(** removes a proof attempt from the database *)

val set_obsolete : proof_attempt -> unit
(** marks this proof as obsolete *)

val set_status : proof_attempt -> proof_status -> float -> unit
(** set the proof status for this prover, and its time.
    also unset the obsolete flag *)

val set_edited_as : proof_attempt -> string -> unit
(** set the file name where this proof can be edited *)

(** {3 transformations} *)

val add_transformation : goal -> transf_id -> transf
(** adds a transformation for this goal.
    subgoals must be added afterwards by [add_subgoal]
    @raise AlreadyExist if a transformation with the same id
    is already there *)

val remove_transformation : transf -> unit
  (** Removes a proof attempt from the database.  Beware that the
      subgoals are not removed by this function, you must remove them
      first using [remove_subgoal]. In other words, this function
      assumes there are no subgoals left under the transformation, but
      it does not protect against that. *)

(** {3 goals} *)

val add_goal : theory -> string -> string -> goal
(** [add_goal th id sum] adds to theory [th] a new goal named [id], with
    [sum] as the checksum of its task.
    @raise AlreadyExist if a goal with the same id already exists
    in this theory *)

val change_checksum: goal -> string -> unit
(** [change_checksum g sum] replaces checksum of [g] by [sum] *)

val add_subgoal : transf -> string -> string -> goal
(** [add_subgoal t id sum] adds to transf [t] a new subgoal named [id], with
    [sum] as the checksum of its task.
    @raise AlreadyExist if a goal with the same id already exists
    as subgoal of this transf *)

val remove_subgoal:  goal -> unit
(** [remove_subgoal g] removes the subgoal [g] from db. *)

(** {3 theories} *)

val add_theory : file -> string -> theory
(** [add_theory f id] adds to file f a theory named [th].
    @raise AlreadyExist if a theory with the same id already exists
    in this file *)

(* todo: remove_theory *)


(** {3 files} *)

val add_file :  string -> file
(** adds a file to the database.
    @raise AlreadyExist if a file with the same id already exists *)

(* todo: remove_file *)







(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
