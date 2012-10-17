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
open Why3
open Util
open Whyconf
open Theory
open Task
open Driver
open Trans
module B = Bench
module C = Call_provers

let debug = Debug.register_flag "main"

let usage_msg = sprintf
  "Usage: %s [options] [[file|-] [-T <theory> [-G <goal>]...]...]...
  [-P <prover> ]..."
  (Filename.basename Sys.argv.(0))

let version_msg = sprintf "Why3 bench tool, version %s (build date: %s)"
  Config.version Config.builddate

let opt_queue = Queue.create ()

let opt_input = ref None
let opt_theory = ref None
let opt_trans = ref []
let opt_metas = ref []
let opt_debug = ref []

let add_opt_file x =
  let tlist = Queue.create () in
  Queue.push (Some x, tlist) opt_queue;
  opt_input := Some tlist

let add_opt_theory =
  let rdot = (Str.regexp "\\.") in fun x ->
  let l = Str.split rdot x in
  let p, t = match List.rev l with
    | t::p -> List.rev p, t
    | _ -> assert false
  in
  match !opt_input, p with
  | None, [] ->
      eprintf "Option '-T'/'--theory' with a non-qualified \
        argument requires an input file.@.";
      exit 1
  | Some tlist, [] ->
      let glist = Queue.create () in
      Queue.push (x, p, t, glist) tlist;
      opt_theory := Some glist
  | _ ->
      let tlist = Queue.create () in
      Queue.push (None, tlist) opt_queue;
      opt_input := None;
      let glist = Queue.create () in
      Queue.push (x, p, t, glist) tlist;
      opt_theory := Some glist

let add_opt_goal x = match !opt_theory with
  | None ->
      eprintf "Option '-G'/'--goal' requires a theory.@.";
      exit 1
  | Some glist ->
      let l = Str.split (Str.regexp "\\.") x in
      Queue.push (x, l) glist

let add_opt_trans x = opt_trans := x::!opt_trans

let add_opt_debug x = opt_debug := x::!opt_debug

let add_opt_meta meta =
  let meta_name, meta_arg =
    let index = String.index meta '=' in
    (String.sub meta 0 index),
    (String.sub meta (index+1) (String.length meta - (index + 1))) in
  opt_metas := (meta_name,meta_arg)::!opt_metas

let opt_config = ref None
let opt_parser = ref None
let opt_prover = ref []
let opt_loadpath = ref []
let opt_output = ref None
let opt_timelimit = ref None
let opt_memlimit = ref None
let opt_benchrc = ref []
let opt_db = ref None
let opt_redo = ref false

let opt_print_theory = ref false
let opt_print_namespace = ref false
let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false
let opt_list_flags = ref false

let opt_debug_all = ref false
let opt_version = ref false

let opt_quiet = ref false

let option_list = Arg.align [
  "-", Arg.Unit (fun () -> add_opt_file "-"),
      " Read the input file from stdin";
  "-T", Arg.String add_opt_theory,
      "<theory> Select <theory> in the input file or in the library";
  "--theory", Arg.String add_opt_theory,
      " same as -T";
  "-G", Arg.String add_opt_goal,
      "<goal> Select <goal> in the last selected theory";
  "--goal", Arg.String add_opt_goal,
      " same as -G";
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> Add <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L";
  "-I", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L (obsolete)";
  "-P", Arg.String (fun s -> opt_prover := s::!opt_prover),
      "<prover> Add <prover> in the bench";
  "-B", Arg.String (fun s -> opt_benchrc := s::!opt_benchrc),
      "<bench> Read one bench configuration file from <bench>";
  "-d", Arg.String (fun s -> opt_db := Some s),
  "<dir> the directory containing the database";
  "--redo-db", Arg.Set opt_redo,
  " Check that the proof attempts in the database (-d) give the same results";
  "--prover", Arg.String (fun s -> opt_prover := s::!opt_prover),
      " same as -P";
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> Select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
  "-t", Arg.Int (fun i -> opt_timelimit := Some i),
      "<sec> Set the prover's time limit (default=10, no limit=0)";
  "--timelimit", Arg.Int (fun i -> opt_timelimit := Some i),
      " same as -t";
  "-m", Arg.Int (fun i -> opt_memlimit := Some i),
      "<MiB> Set the prover's memory limit (default: no limit)";
  "--memlimit", Arg.Int (fun i -> opt_timelimit := Some i),
      " same as -m";
  "-a", Arg.String add_opt_trans,
      "<transformation> Apply a transformation to every task";
  "--apply-transform", Arg.String add_opt_trans,
      " same as -a";
  "-M", Arg.String add_opt_meta,
      "<meta_name>=<string> Add a string meta to every task";
  "--meta", Arg.String add_opt_meta,
      " same as -M";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> Print the selected goals to separate files in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o";
  "--print-theory", Arg.Set opt_print_theory,
      " Print selected theories";
  "--print-namespace", Arg.Set opt_print_namespace,
      " Print namespaces of selected theories";
  "--list-transforms", Arg.Set opt_list_transforms,
      " List known transformations";
  "--list-printers", Arg.Set opt_list_printers,
      " List known printers";
  "--list-provers", Arg.Set opt_list_provers,
      " List known provers";
  "--list-formats", Arg.Set opt_list_formats,
      " List known input formats";
  "--list-metas", Arg.Set opt_list_metas,
      " List known metas";
  "--list-debug-flags", Arg.Set opt_list_flags,
      " List known debug flags";
  "--debug-all", Arg.Set opt_debug_all,
      " Set all debug flags (except parse_only and type_only)";
  "--debug", Arg.String add_opt_debug,
      "<flag> Set a debug flag";
  "--quiet", Arg.Set opt_quiet,
      " Print only what asked";
  "--version", Arg.Set opt_version,
      " Print version information"
 ]

let tools = ref []
let probs = ref []
let benchs = ref []

let () =
  try
  Arg.parse option_list add_opt_file usage_msg;

  (** Debug flag *)
  if !opt_debug_all then begin
    List.iter (fun (_,f,_) -> Debug.set_flag f) (Debug.list_flags ());
    Debug.unset_flag Typing.debug_parse_only;
    Debug.unset_flag Typing.debug_type_only
  end;

  List.iter (fun s -> Debug.set_flag (Debug.lookup_flag s)) !opt_debug;

  (** Configuration *)
  let config = try read_config !opt_config with Not_found ->
    option_iter (eprintf "Config file '%s' not found.@.") !opt_config;
    exit 1;
  in

  let main = get_main config in
  Whyconf.load_plugins main;
  Bench.BenchUtil.maximum_running_proofs := Whyconf.running_provers_max main;
  (** listings*)

  let opt_list = ref false in
  if !opt_version then begin
    opt_list := true;
    printf "%s@." version_msg
  end;
  if !opt_list_transforms then begin
    opt_list := true;
    printf "@[<hov 2>Known non-splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Trans.list_transforms ()));
    printf "@[<hov 2>Known splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Trans.list_transforms_l ()))
  end;
  if !opt_list_printers then begin
    opt_list := true;
    printf "@[<hov 2>Known printers:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Printer.list_printers ()))
  end;
  if !opt_list_formats then begin
    opt_list := true;
    let print1 fmt s = fprintf fmt "%S" s in
    let print fmt (p, l) =
      fprintf fmt "%s [%a]" p (Pp.print_list Pp.comma print1) l
    in
    printf "@[<hov 2>Known input formats:@\n%a@]@."
      (Pp.print_list Pp.newline print)
      (List.sort Pervasives.compare (Env.list_formats ()))
  end;
  if !opt_list_provers then begin
    opt_list := true;
    let config = read_config !opt_config in
    let print fmt s prover = fprintf fmt "%s (%s)@\n" s prover.name in
    let print fmt m = Mstr.iter (print fmt) m in
    let provers = get_provers config in
    printf "@[<hov 2>Known provers:@\n%a@]@." print provers
  end;
  if !opt_list_metas then begin
    opt_list := true;
    let print fmt m = fprintf fmt "@[%s %s%a@]"
      (let s = m.meta_name in
        if String.contains s ' ' then "\"" ^ s ^ "\"" else s)
      (if m.meta_excl then "* " else "")
      (Pp.print_list Pp.space Pretty.print_meta_arg_type) m.meta_type
    in
    let cmp m1 m2 = Pervasives.compare m1.meta_name m2.meta_name in
    printf "@[<hov 2>Known metas:@\n%a@]@\n@."
      (Pp.print_list Pp.newline print) (List.sort cmp (Theory.list_metas ()))
  end;
  if !opt_list_flags then begin
    opt_list := true;
    let print fmt (p,_,_) = fprintf fmt "%s" p in
    printf "@[<hov 2>Known debug flags:@\n%a@]@."
      (Pp.print_list Pp.newline print)
      (List.sort Pervasives.compare (Debug.list_flags ()))
  end;
  if !opt_list then exit 0;

  (* Someting else using rc file intead of driver will be added later *)
  (* if !opt_prover <> None && !opt_driver <> None then begin *)
  (*   eprintf "Options '-P'/'--prover' and \ *)
  (*     '-D'/'--driver' cannot be used together.@."; *)
  (*   exit 1 *)
  (* end; *)

  begin match !opt_db with
    | None -> ()
    | Some db ->
      Debug.dprintf debug "Load database@.";
      if Sys.file_exists db then
        begin if not (Sys.is_directory db) then
            begin Format.eprintf
                "-d %s; the given database should be a directory@." db;
              exit 1
            end
        end
      else
        begin
          eprintf "Info: '%s' does not exists. Creating directory of that \
           name for the project@." db;
          Unix.mkdir db 0o777
        end;
      let dbfname = Filename.concat db "project.db" in
      (try
         Db.init_base dbfname
      with e ->
        eprintf "Error while opening database '%s'@." dbfname;
        eprintf "Aborting...@.";
        raise e);
      Debug.dprintf debug "database loaded@."
  end;

  if !opt_benchrc = [] && (!opt_prover = [] || Queue.is_empty opt_queue)
    && (not !opt_redo)
  then
    begin
      eprintf "At least one bench is required or one prover and one file or
      the verification of a database .@.";
      Arg.usage option_list usage_msg;
      exit 1
    end;

  opt_loadpath := List.rev_append !opt_loadpath (Whyconf.loadpath main);
  if !opt_timelimit = None then opt_timelimit := Some (Whyconf.timelimit main);
  if !opt_memlimit  = None then opt_memlimit  := Some (Whyconf.memlimit main);
  let add_meta theory (meta,s) =
    let meta = lookup_meta meta in
    Theory.add_meta theory meta [MAstr s]
  in
  let opt_theo = Theory.close_theory (List.fold_left add_meta
    (Theory.create_theory (Ident.id_fresh "cmdline"))
    !opt_metas) in

  let env = Env.create_env !opt_loadpath in

  if !opt_redo then
    begin if not (Db.is_initialized ()) then
        begin eprintf "--redo-db need the option -d";
          exit 1 end;
      Benchdb.db config env
    end;


  let map_prover s =
    let prover = try Mstr.find s (get_provers config) with
      | Not_found -> eprintf "Prover %s not found.@." s; exit 1
    in
    { B.tval   = {B.tool_name = "cmdline"; prover_name = s; tool_db = None};
      ttrans   = [Trans.identity,None];
      tdriver  = load_driver env prover.driver;
      tcommand = prover.command;
      tenv     = env;
      tuse     = [opt_theo,None];
      ttime    = of_option !opt_timelimit;
      tmem     = of_option !opt_memlimit;
    } in
  Debug.dprintf debug "Load provers@.";
  tools := List.map map_prover !opt_prover;

  Debug.dprintf debug "Load transformations@.";
  let transl =
      let lookup acc t =
    ((try Trans.singleton (Trans.lookup_transform t env) with
       Trans.UnknownTrans _ -> Trans.lookup_transform_l t env),None)::acc
      in
      List.rev (List.fold_left lookup [] !opt_trans) in

  let fold_prob acc = function
    | None, _ -> acc
    | Some f, _ ->
      { B.ptask   = Benchrc.gen_from_file ~format:!opt_parser
          ~prob_name:"cmdline" ~file_path:f ~file_name:f;
        ptrans   = fun _ -> transl;
      }::acc in
  Debug.dprintf debug "Load problems@.";
  probs := Queue.fold fold_prob [] opt_queue;

  Debug.dprintf debug "Load bench@.";
  let cmdl = "commandline" in
  let bench = List.map (Benchrc.read_file config) !opt_benchrc in
  let bench = if !tools <> [] && !probs <> [] then
      let b_cmdl = {
        B.bname = cmdl;
        btools = !tools; bprobs = !probs;
        boutputs = [B.Timeline "-";B.Average "-"]} in
      { Benchrc.tools = Mstr.empty;
        probs = Mstr.empty;
        benchs = Mstr.singleton cmdl b_cmdl}
      ::bench
    else bench in
  benchs := bench


  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

let () =
  let nb_done = ref 0 in
  let nb_valid = ref 0 in
  let nb_cached = ref 0 in
  let nb_failure = ref 0 in
  let callback tool_id prob_id task i res =
    if not !opt_quiet then
      begin begin match res with
        | B.Runned B.Done (ans,_) -> incr nb_done;
          begin match ans with
            | Db.Done Call_provers.Valid -> incr nb_valid
            | _ -> () end
        | B.Runned B.InternalFailure _ -> incr nb_done; incr nb_failure
        | B.Cached (_,_) -> incr nb_cached
      end;
        Format.printf "%a%i done with valid : %i failure : %i cached : %i%!"
          Pp.Ansi.set_column 0
          !nb_done !nb_valid !nb_failure !nb_cached
      end;
    Debug.dprintf debug "%s.%s %a %i with %s : %a@."
      prob_id.B.prob_file prob_id.B.prob_theory
      Pretty.print_pr (task_goal task) i tool_id.B.tool_name
      B.print_pas res;
  in
  let benchs =
    List.map (fun b -> List.map snd (Mstr.bindings b.Benchrc.benchs))
      !benchs in
  let bl = B.run_benchs_tools ~callback (list_flatten_rev benchs) in
  let print_tool fmt tool_id = fprintf fmt "%s.%s"
    tool_id.B.tool_name tool_id.B.prover_name in
  let print_prob fmt prob_id = fprintf fmt "%s.%s.%s"
    prob_id.B.prob_name prob_id.B.prob_file prob_id.B.prob_theory in
  let cmp = compare in
  List.iter (B.print_output cmp print_tool print_prob) bl

(*
Local Variables:
compile-command: "unset LANG; make -j -C ../.. bin/why3bench.byte"
End:
*)
