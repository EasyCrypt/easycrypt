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

(** Call provers and parse their outputs *)

type prover_answer =
  | Valid
      (** The task is valid according to the prover *)
  | Invalid
      (** The task is invalid *)
  | Timeout
      (** the task timeout, ie it takes more time than specified *)
  | Unknown of string
      (** The prover can't determine if the task is valid *)
  | Failure of string
      (** The prover reports a failure *)
  | HighFailure
      (** An error occured during the call to the prover or none
          of the given regexps match the output of the prover *)

type prover_result = {
  pr_answer : prover_answer;
  (* The answer of the prover on the given task *)
  pr_output : string;
  (* The output of the prover currently stderr and stdout *)
  pr_time   : float;
  (* The time taken by the prover *)
}

val print_prover_answer : Format.formatter -> prover_answer -> unit
(** Pretty-print a {! prover_answer} *)

val print_prover_result : Format.formatter -> prover_result -> unit
(** Pretty-print a prover_result. The answer and the time are output.
    The output of the prover is printed if and only if the answer is
    a [HighFailure] *)

val debug : Debug.flag
(** debug flag for the calling procedure (option "--debug call_prover")
    If set [call_on_buffer] prints on stderr the commandline called
    and the output of the prover. *)

type timeregexp
(** The type of precompiled regular expressions for time parsing *)

val timeregexp : string -> timeregexp
(** Converts a regular expression with special markers '%h','%m',
    '%s','%i' (for milliseconds) into a value of type [timeregexp] *)

type prover_call
(** Type that represents a single prover run *)

type pre_prover_call = unit -> prover_call
(** Thread-safe closure that launches the prover *)

type post_prover_call = unit -> prover_result
(** Thread-unsafe closure that interprets the prover's results *)

val call_on_buffer :
  command     : string ->
  ?timelimit  : int ->
  ?memlimit   : int ->
  regexps     : (Str.regexp * prover_answer) list ->
  timeregexps : timeregexp list ->
  exitcodes   : (int * prover_answer) list ->
  filename    : string ->
  Buffer.t -> pre_prover_call
(** Call a prover on the task printed in the {!type: Buffer.t} given.

    @param timelimit : set the available time limit (def. 0 : unlimited)
    @param memlimit : set the available time limit (def. 0 : unlimited)

    @param regexps : if the first field matches the prover output,
    the second field is the answer. Regexp groups present in
    the first field are substituted in the second field (\0,\1,...).
    The regexps are tested in the order of the list.

    @param timeregexps : a list of regular expressions with special
    markers '%h','%m','%s','%i' (for milliseconds), constructed with
    [timeregexp] function, and used to extract the time usage from
    the prover's output. If the list is empty, wallclock is used.
    The regexps are tested in the order of the list.

    @param exitcodes : if the first field is the exit code, then
    the second field is the answer. Exit codes are tested in the order
    of the list and before the regexps.

    @param filename : the suffix of the proof task's file, if the prover
    doesn't accept stdin. *)

val query_call : prover_call -> post_prover_call option
(** Thread-safe non-blocking function that checks if the prover
    has finished. *)

val wait_on_call : prover_call -> post_prover_call
(** Thread-safe blocking function that waits until the prover finishes. *)


val kill : prover_call -> int -> unit
