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

(** run benchs from the database *)

open Format
open Why3
open Util
module BenchUtil = Bench.BenchUtil

let load_driver = Env.Wenv.memoize 2 (fun env ->
  memo_string 10 (Driver.load_driver env))

let debug = Debug.register_flag "benchdb"

type path =
  | Pgoal of string
  | Ptrans of string

let print_path fmt = function
  | Pgoal s -> Format.fprintf fmt "the goal %s" s
  | Ptrans s -> Format.fprintf fmt "the transformation %s" s

let print_paths fmt (wf,thname,pathl) =
  Format.fprintf fmt "%a of theory %s in file %s"
    (Pp.print_list (fun fmt () -> fprintf fmt "@ of@ ") print_path) pathl
    thname wf

let concat_path p (wf,thname,pathl) = (wf,thname,p::pathl)

let rec goal whyconf env path dbgoal wgoal =
  (** external proof *)
  let db_proofs = Db.external_proofs dbgoal in
  let iter prover_id proof_attempt =
    try
      let (proof_status,time,obsolete,edited_as) =
        Db.status_and_time proof_attempt in
      if obsolete then () else
      let prover_name = Db.prover_name prover_id in
      let driver,command =
        try
          let p = Mstr.find prover_name (Whyconf.get_provers whyconf) in
          p.Whyconf.driver ,p.Whyconf.command
        with
      (* TODO add exceptions pehaps inside rc.ml in fact*)
          | Not_found ->
            Debug.dprintf debug "Error : Prover %s not found.@." prover_name;
            raise Exit
      in
      let cb res =
        let (res_status,_res_time) = BenchUtil.proof_status_to_db_result res in
        if proof_status <> res_status then
          printf "Diff : %a instead of %a in %a@."
            BenchUtil.print_proof_status res_status
            BenchUtil.print_proof_status proof_status
            print_paths path
        else
          Debug.dprintf debug "Same : %a for %a@."
            BenchUtil.print_proof_status proof_status
            print_paths path
      in
      let old = if edited_as = "" then None else
          begin
            eprintf "Info: proving using edited file %s@." edited_as;
            (Some (open_in edited_as))
          end
      in
      let call_prover : Call_provers.pre_prover_call =
        Driver.prove_task
          ~timelimit:(truncate (ceil (0.1 +. time *. 1.1)))
          ~command (load_driver env driver) ?old wgoal in
      BenchUtil.new_external_proof (call_prover,cb)
    with Exit -> ()
  in
  Db.Hprover.iter iter db_proofs;
  (** with transformations *)
  let db_trans = Db.transformations dbgoal in
  let iter dbtrans_id dbtrans =
    let name = Db.transf_name dbtrans_id in
    try
      let wtransf = try Trans.singleton (Trans.lookup_transform name env)
        with Trans.UnknownTrans _ -> Trans.lookup_transform_l name env
      in
      transf whyconf env (concat_path (Ptrans name) path) dbtrans wtransf wgoal
    with Trans.UnknownTrans _ ->
      Debug.dprintf debug "Error : Transformation %s not found.@." name
  in
  Db.Htransf.iter iter db_trans

and transf whyconf env path dbtransf wtransf wgoal =
  try
    let wgoals = Trans.apply wtransf wgoal in
    let dbgoals = Db.subgoals dbtransf in
    let iter wgoal =
      let checksum = BenchUtil.task_checksum wgoal in
      try
        let dbgoal = Mstr.find checksum dbgoals in
        let gname = (Task.task_goal wgoal).Decl.pr_name.Ident.id_string in
        goal whyconf env (concat_path (Pgoal gname) path) dbgoal wgoal
      with Not_found ->
        Debug.dprintf debug
          "Error : Goal with checksum %s@ not found in@ %a.@."
          checksum print_paths path
    in
    List.iter iter wgoals
  with e ->
    Debug.dprintf debug "Error : Execption %a@ in %a not found.@."
      Exn_printer.exn_printer e print_paths path

let theory whyconf env wf thname dbth wth =
  let wgoals = Task.split_theory wth None None in
  let dbgoals = Db.goals dbth in
  let iter wgoal =
    let gname = (Task.task_goal wgoal).Decl.pr_name.Ident.id_string in
    try
      let dbgoal = Mstr.find gname dbgoals in
      goal whyconf env (wf,thname,[Pgoal gname]) dbgoal wgoal
    with Not_found ->
      Debug.dprintf debug
        "Error : No sketch of proof for the goal %s of theory %s in file %s.@."
        gname thname wf
  in
  List.iter iter wgoals

let file whyconf env (dbf,wf) =
  let wths = Env.read_file env
    (Filename.concat (Filename.dirname (Db.db_name ())) wf) in
  let dbths = Db.theories dbf in
  let iter thname wth =
    try
      let dbth = Mstr.find thname dbths in
      theory whyconf env wf thname dbth wth
    with Not_found ->
      Debug.dprintf debug
        "Error : No sketch of proof for the theory %s of file %s.@."
        thname wf
  in
  Util.Mstr.iter iter wths


let db whyconf env =
  assert (Db.is_initialized ());
  List.iter (file whyconf env) (Db.files ());
  BenchUtil.wait_remaining_task ()
