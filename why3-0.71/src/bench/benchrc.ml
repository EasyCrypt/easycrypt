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

open Format
open Bench
open Why3
open Util
open Theory


type id_tool = (string * string)
type id_prob = (string * string * string)

type benchrc = { tools : tool list Mstr.t;
                 probs : prob list Mstr.t;
                 benchs : bench Mstr.t
               }

open Whyconf
open Rc

let absolute_filename dirname f =
  if f = "-" then f else
  if Filename.is_relative f then
    Filename.concat dirname f
  else
    f

let lookup_transf t =
  if Db.is_initialized () then Some (Db.transf_from_name t) else None


let read_tools absf wc map (name,section) =
  (* loadpath *)
  let wc_main = get_main wc in
  let loadpath = get_stringl ~default:[] section "loadpath" in
  let loadpath = List.append loadpath (Whyconf.loadpath wc_main) in
  (* limit *)
  let timelimit = get_int ~default:(timelimit wc_main) section "timelimit" in
  let memlimit = get_int ~default:(memlimit wc_main) section "memlimit" in
  (* env *)
  let env = Env.create_env loadpath in
  (* transformations *)
  let transforms = get_stringl ~default:[] section "transform" in
  let lookup acc t = (Trans.lookup_transform t env, lookup_transf t)::acc in
  let transforms = List.fold_left lookup [] transforms in
  let transforms = List.rev transforms in
  (* use *)
  let use = get_stringl ~default:[] section "use" in
  let load_use s =
    let file,th = match Util.split_string_rev s '.' with
      | [] | [_] -> eprintf "Bad theory qualifier %s" s; exit 1
      | a::l -> List.rev l,a in
    Env.find_theory env file th,
    if Db.is_initialized () then
      Some (Db.transf_from_name (Printf.sprintf "use %s" s))
    else None in
  let use = List.map load_use use in
  (* provers *)
  let provers = get_stringl ~default:[] section "prover" in
  let find_provers s =
    try let p = Mstr.find s (get_provers wc) in
        s,p.driver ,p.command
    with
      (* TODO add exceptions pehaps inside rc.ml in fact*)
      | Not_found -> eprintf "Prover %s not found.@." s; exit 1 in
  let provers = List.map find_provers provers in
  let provers =
    try
      let driver = get_string section "driver" in
      let command = get_string section "command" in
      ("driver",absf driver,command) :: provers
    with MissingField _ -> provers in
  let load_driver (n,d,c) = n,Driver.load_driver env d,c in
  let provers = List.map load_driver provers in
  let create_tool (n,driver,command) =
    { tval = {tool_name = name; prover_name = n; tool_db =
        if Db.is_initialized () then Some (Db.prover_from_name n) else None};
      ttrans = transforms;
      tdriver = driver;
      tcommand = command;
      tenv = env;
      tuse = use;
      ttime = timelimit;
      tmem = memlimit
    } in
  Mstr.add name (List.map create_tool provers) map

let use_before_goal th = function
  | Some {Task.task_decl = tdecl; task_prev = task} ->
    Task.add_tdecl (Task.use_export task th) tdecl
  | _ -> assert false

let apply_use_before_goal (task,goal_id) (th_use,th_use_id) =
  let task = use_before_goal th_use task in
  let goal_id = match goal_id, th_use_id with
    | Some goal_id, Some th_use_id ->
      Some begin
        let transf =
          try Db.Htransf.find (Db.transformations goal_id) th_use_id
          with Not_found ->
            Db.add_transformation goal_id th_use_id  in
        let name2 = (Task.task_goal task).Decl.pr_name.Ident.id_string in
        let md5_2 = BenchUtil.task_checksum task in
        try Mstr.find md5_2 (Db.subgoals transf)
        with Not_found ->
          Db.add_subgoal transf name2 md5_2
      end
    | _,_ -> None in
  (task,goal_id)

let gen_from_file ~format ~prob_name ~file_path ~file_name env lth =
    try
      let theories =
        let file_name, cin = match file_path with
          | "-" -> "stdin", stdin
          | f   -> file_name, open_in f
        in
        let m = Env.read_channel ?format:format env file_name cin in
        close_in cin;
        Mstr.bindings m in
      let file_id = if Db.is_initialized () then
          let file_db = Sysutil.relativize_filename
            (Filename.dirname (Db.db_name ())) file_path in
          Some
          (try fst (List.find (fun (_,x) -> file_db = x) (Db.files ()))
           with Not_found ->
             Db.add_file file_db)
        else None in
      let map (th_name,th) =
        let theory_id = option_map (fun file_id ->
          try Mstr.find th_name (Db.theories file_id)
          with Not_found ->
            Db.add_theory file_id th_name
        ) file_id in
        (* TODO make DB aware of the env *)
        let tasks = Task.split_theory th None None in
        let map task =
          let goal_id = option_map (fun theory_id ->
            let name = (Task.task_goal task).Decl.pr_name.Ident.id_string in
            try Mstr.find name (Db.goals theory_id)
            with Not_found ->
              Db.add_goal theory_id name (BenchUtil.task_checksum task)
          ) theory_id in
          let (task,goal_id) = List.fold_left apply_use_before_goal
            (task,goal_id) lth in
          {prob_name = prob_name;prob_file = file_name; prob_theory = th_name;
           prob_db = goal_id}, task in
        List.rev_map map tasks in
      list_flatten_rev (List.rev_map map theories)
    with exn -> eprintf "%a@." Exn_printer.exn_printer exn; exit 1

let read_probs absf map (name,section) =
  (* transformations *)
  let transforms = get_stringl ~default:[] section "transform" in
  let gen_trans env =
    let lookup acc t =
      ((try Trans.singleton (Trans.lookup_transform t env) with
          Trans.UnknownTrans _ -> Trans.lookup_transform_l t env),
       lookup_transf t)::acc
    in
    let transforms = List.fold_left lookup [] transforms in
    List.rev transforms
  in
  (* format *)
  let format = get_stringo section "format" in
  (* files *)
  let files = get_stringl ~default:[] section "file" in
  Mstr.add name
    (List.rev_map
       (fun file ->
         { ptask   = gen_from_file ~format ~prob_name:name
             ~file_path:(absf file) ~file_name:file;
           ptrans   = gen_trans}) files)
    map

let read_bench absf mtools mprobs map (name,section) =
  let tools = get_stringl section "tools" in
  let lookup s =
    try Mstr.find s mtools
    with Not_found -> eprintf "Undefined tools %s@." s;
      exit 1 in
  let tools = list_flatten_rev (List.map lookup tools) in
  let probs = get_stringl section "probs" in
  let lookup s =
    try Mstr.find s mprobs
    with Not_found -> eprintf "Undefined probs %s@." s;
      exit 1 in
  let probs = list_flatten_rev (List.map lookup probs) in
  let averages = get_stringl ~default:[] section "average" in
  let outputs = List.fold_left
    (cons (fun s -> Average (absf s)))
    [] averages in
  let timelines = get_stringl ~default:[] section "timeline" in
  let outputs = List.fold_left
    (cons (fun s -> Timeline (absf s)))
    outputs timelines in
  let csvs = get_stringl ~default:[] section "csv" in
  let outputs = List.fold_left
    (cons (fun s -> Csv (absf s)))
    outputs csvs in
  Mstr.add name
    { bname = name; btools = tools; bprobs = probs; boutputs = outputs} map


let read_file wc f =
  let rc = from_file f in
  let absf = absolute_filename (Filename.dirname f) in
  let tools = get_family rc "tools" in
  let tools = List.fold_left (read_tools absf wc) Mstr.empty tools in
  let probs = get_family rc "probs" in
  let probs = List.fold_left (read_probs absf) Mstr.empty probs in
  let benchs = get_family rc "bench" in
  let benchs = List.fold_left (read_bench absf tools probs)
    Mstr.empty benchs in
  {tools = tools;
   probs = probs;
   benchs = benchs}
