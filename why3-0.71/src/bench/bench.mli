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
open Env
open Theory
open Task
open Trans
open Driver
open Call_provers

module BenchUtil : sig
  val maximum_running_proofs: int ref
(** bound on the number of prover processes running in parallel.
    default is 2 *)

  val new_external_proof :
    Call_provers.pre_prover_call * (Call_provers.prover_result -> unit)
    -> unit
  (** [new_external_proof pre_prover_call callback] *)

  val wait_remaining_task : unit -> unit
  (** Wait the completion of the remaining task started by
      new_external_proof *)

  val task_checksum : Task.task -> string

  val apply_trans :
    task * Db.goal option ->
    task trans * Db.transf_id option ->
    task * Db.goal option
  (** [apply_transl trans goal] *)

  val apply_transl :
    task * Db.goal option ->
    task list trans * Db.transf_id option ->
    (task * Db.goal option) list
  (** [apply_transl transl goal] *)

  val apply_transll :
    (task list trans * Db.transf_id option) list ->
    (task * Db.goal option) list ->
    task * Db.goal option ->
    (task * Db.goal option) list
  (** [apply_transll transllist acc goal] *)

  val proof_status_to_db_result :
    Call_provers.prover_result -> Db.proof_status * float

  val print_proof_status :
    Format.formatter -> Db.proof_status -> unit

end

type tool_id = {
  tool_name : string;
  prover_name : string;
  tool_db : Db.prover_id option;
  }
(* tool_name, prover_name *)

type prob_id = {
  prob_name : string;
  prob_file : string;
  prob_theory : string;
  prob_db : Db.goal option;
}
(* prob_name, file_name, theory name *)

type tool = {
  tval     : tool_id;
  ttrans   : (task trans * (Db.transf_id option)) list;
  tdriver  : driver;
  tcommand : string;
  tenv     : env;        (** Allow to compare axiomatic easily *)
  tuse     : (theory * Db.transf_id option) list;
  ttime    : int;
  tmem     : int;
}
type gen_task = env -> (theory * Db.transf_id option) list ->
    (prob_id * task) list

type prob = {
  ptask  : gen_task;
  (** needed for tenv and tuse *)
  ptrans : env -> (task list trans * (Db.transf_id option)) list;
}

type why_result =
  | InternalFailure of exn
  | Done of  Db.proof_status * float

val print_why_result : Format.formatter -> why_result -> unit
type result = {tool   : tool_id;
               prob   : prob_id;
               task   : Decl.prsymbol;
               idtask : int;
               result : why_result}

type proof_attempt_status =
  | Runned of why_result
  | Cached of Db.proof_status * float

val print_pas : Format.formatter -> proof_attempt_status -> unit

type callback = tool_id -> prob_id ->
    task -> int -> proof_attempt_status -> unit

val all_list_tp :
  ?callback:callback ->
  tool list -> prob list -> result list

val all_list_pt :
  ?callback:callback ->
  tool list -> prob list -> result list

val all_array :
  ?callback:callback ->
  tool array -> prob array -> result list array array

val any :
  ?callback:callback ->
  (tool * prob) list -> result list


val all_list_tools :
  ?callback:callback ->
  tool list -> prob list -> (tool_id * result list) list


type output =
  (** In a file *)
  |Average of string
  |Timeline of string
  |Csv of string

type bench =
    {
      bname  : string;
      btools : tool list;
      bprobs : prob list;
      boutputs : output list;
    }

val run_bench :
  ?callback:callback -> bench  -> result list


val run_benchs :
  ?callback:callback -> bench list ->
  (bench * result list) list

val run_benchs_tools :
  ?callback:callback -> bench list ->
  (bench * (tool_id * result list) list) list


type nb_avg = int * float

val print_nb_avg : Format.formatter -> nb_avg -> unit

type tool_res =
    { valid : nb_avg;
      timeout : nb_avg;
      unknown : nb_avg;
      invalid : nb_avg;
      failure : nb_avg}

val print_tool_res : Format.formatter -> tool_res -> unit

val compute_average : result list -> tool_res
val compute_timeline :
  float -> float -> float -> result list -> int list
(** [compute_timeline start end step results] *)

val filter_timeline : result list -> result list

val max_time : result list -> float

open Format

val print_csv :
  (prob_id -> prob_id -> int)         ->
  (formatter -> tool_id -> unit) ->
  (formatter -> prob_id -> unit) ->
  formatter ->
  (tool_id * result list) list -> unit

val print_output :
  (prob_id -> prob_id -> int)         ->
  (formatter -> tool_id -> unit) ->
  (formatter -> prob_id -> unit) ->
  bench * (tool_id * result list) list -> unit
