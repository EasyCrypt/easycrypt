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

let usage_msg = sprintf
  "Usage: %s [options] [[file|-] [-T <theory> [-G <goal>]...]...]..."
  (Filename.basename Sys.argv.(0))

let version_msg = sprintf "Why3 platform, version %s (build date: %s)"
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
let opt_prover = ref None
let opt_loadpath = ref []
let opt_driver = ref None
let opt_output = ref None
let opt_timelimit = ref None
let opt_memlimit = ref None
let opt_command = ref None
let opt_task = ref None
let opt_realize = ref false
let opt_bisect = ref false

let opt_print_libdir = ref false
let opt_print_datadir = ref false

let opt_print_theory = ref false
let opt_print_namespace = ref false
let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false
let opt_list_flags = ref false

let opt_parse_only = ref false
let opt_type_only = ref false
let opt_debug_all = ref false
let opt_version = ref false

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
  "-P", Arg.String (fun s -> opt_prover := Some s),
      "<prover> Prove or print (with -o) the selected goals";
  "--prover", Arg.String (fun s -> opt_prover := Some s),
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
  "-D", Arg.String (fun s -> opt_driver := Some s),
      "<file> Specify a prover's driver (conflicts with -P)";
  "--driver", Arg.String (fun s -> opt_driver := Some s),
      " same as -D";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> Print the selected goals to separate files in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o";
  "--realize", Arg.Set opt_realize,
      " Realize selected theories from the library";
  "--bisect", Arg.Set opt_bisect,
      " Reduce the set of needed axioms which prove a goal, \
        and output the resulting task";
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
  "--parse-only", Arg.Set opt_parse_only,
      " Stop after parsing (same as --debug parse_only)";
  "--type-only", Arg.Set opt_type_only,
      " Stop after type checking (same as --debug type_only)";
  "--debug-all", Arg.Set opt_debug_all,
      " Set all debug flags (except parse_only and type_only)";
  "--debug", Arg.String add_opt_debug,
      "<flag> Set a debug flag";
  "--print-libdir", Arg.Set opt_print_libdir,
      " Print location of binary components (plugins, etc)";
  "--print-datadir", Arg.Set opt_print_datadir,
      " Print location of non-binary data (theories, modules, etc)";
  "--version", Arg.Set opt_version,
      " Print version information" ]

let () = try
  Arg.parse option_list add_opt_file usage_msg;

  if !opt_version then begin
    printf "%s@." version_msg;
    exit 0
  end;
  if !opt_print_libdir then begin
    printf "%s@." Config.libdir;
    exit 0
  end;
  if !opt_print_datadir then begin
    printf "%s@." Config.datadir;
    exit 0
  end;

  (** Debug flag *)
  if !opt_debug_all then begin
    List.iter (fun (_,f,_) -> Debug.set_flag f) (Debug.list_flags ());
    Debug.unset_flag Typing.debug_parse_only;
    Debug.unset_flag Typing.debug_type_only
  end;

  List.iter (fun s -> Debug.set_flag (Debug.lookup_flag s)) !opt_debug;

  if !opt_parse_only then Debug.set_flag Typing.debug_parse_only;
  if !opt_type_only then Debug.set_flag Typing.debug_type_only;

  (** Configuration *)
  let config = read_config !opt_config in
  let main = get_main config in
  Whyconf.load_plugins main;

  (** listings*)

  let opt_list = ref false in
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
      (if m.meta_excl then "(flag) " else "")
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

  if Queue.is_empty opt_queue then begin
    Arg.usage option_list usage_msg;
    exit 1
  end;

  if !opt_prover <> None && !opt_driver <> None then begin
    eprintf "Options '-P'/'--prover' and \
      '-D'/'--driver' cannot be used together.@.";
    exit 1
  end;

  if !opt_prover = None then begin
    if !opt_driver = None && !opt_output <> None then begin
      eprintf "Option '-o'/'--output' requires a prover or a driver.@.";
      exit 1
    end;
    if !opt_timelimit <> None then begin
      eprintf "Option '-t'/'--timelimit' requires a prover.@.";
      exit 1
    end;
    if !opt_memlimit <> None then begin
      eprintf "Option '-m'/'--memlimit' requires a prover.@.";
      exit 1
    end;
    if !opt_bisect then begin
      eprintf "Option '--bisect' requires a prover.@.";
      exit 1
    end;
    if !opt_driver = None && not !opt_print_namespace then
      opt_print_theory := true
  end;

  if !opt_bisect && !opt_output = None then begin
    eprintf "Option '--bisect' require a directory to output the result.@.";
    exit 1
  end;

  opt_loadpath := List.rev_append !opt_loadpath (Whyconf.loadpath main);
  if !opt_timelimit = None then opt_timelimit := Some (Whyconf.timelimit main);
  if !opt_memlimit  = None then opt_memlimit  := Some (Whyconf.memlimit main);
  begin match !opt_prover with
  | Some s ->
      let prover = try Mstr.find s (get_provers config) with
        | Not_found -> eprintf "Prover '%s' not found in %s@."
            s (Whyconf.get_conf_file config); exit 1
      in
      opt_command := Some prover.command;
      opt_driver := Some prover.driver
  | None ->
      ()
  end;
  let add_meta task (meta,s) =
    let meta = lookup_meta meta in
    add_meta task meta [MAstr s]
  in
  opt_task := List.fold_left add_meta !opt_task !opt_metas

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

let timelimit = match !opt_timelimit with
  | None -> 10
  | Some i when i <= 0 -> 0
  | Some i -> i

let memlimit = match !opt_memlimit with
  | None -> 0
  | Some i when i <= 0 -> 0
  | Some i -> i

let print_th_namespace fmt th =
  Pretty.print_namespace fmt th.th_name.Ident.id_string th

let fname_printer = ref (Ident.create_ident_printer [])

let output_task drv fname _tname th task dir =
  let fname = Filename.basename fname in
  let fname =
    try Filename.chop_extension fname with _ -> fname in
  let tname = th.th_name.Ident.id_string in
  let dest = Driver.file_of_task drv fname tname task in
  (* Uniquify the filename before the extension if it exists*)
  let i = try String.rindex dest '.' with _ -> String.length dest in
  let name = Ident.string_unique !fname_printer (String.sub dest 0 i) in
  let ext = String.sub dest i (String.length dest - i) in
  let cout = open_out (Filename.concat dir (name ^ ext)) in
  Driver.print_task drv (formatter_of_out_channel cout) task;
  close_out cout

let output_task_prepared drv fname _tname th task dir =
  let fname = Filename.basename fname in
  let fname =
    try Filename.chop_extension fname with _ -> fname in
  let tname = th.th_name.Ident.id_string in
  let dest = Driver.file_of_task drv fname tname task in
  (* Uniquify the filename before the extension if it exists*)
  let i = try String.rindex dest '.' with _ -> String.length dest in
  let name = Ident.string_unique !fname_printer (String.sub dest 0 i) in
  let ext = String.sub dest i (String.length dest - i) in
  let cout = open_out (Filename.concat dir (name ^ ext)) in
  Driver.print_task_prepared drv (formatter_of_out_channel cout) task;
  close_out cout

let output_theory drv fname _tname th task dir =
  let fname = Filename.basename fname in
  let fname =
    try Filename.chop_extension fname with _ -> fname in
  let dest = Driver.file_of_theory drv fname th in
  let file = Filename.concat dir dest in
  let old =
    if Sys.file_exists file then begin
      let backup = file ^ ".bak" in
      Sys.rename file backup;
      Some (open_in backup)
    end else None in
  let cout = open_out file in
  Driver.print_task ?old drv (formatter_of_out_channel cout) task;
  close_out cout

let do_task env drv fname tname (th : Theory.theory) (task : Task.task) =
  match !opt_output, !opt_command with
    | Some dir, _ when !opt_realize ->
        output_theory drv fname tname th task dir
    | None, _ when !opt_realize ->
        (* FIXME: we should be able to realize other formats *)
        let file,ich = Env.find_channel env "why" th.th_path in
        let dir = try Filename.chop_extension file with _ ->
          eprintf "File %s does not have an extension.@." file;
          exit 1 in
        close_in ich;
        output_theory drv fname tname th task dir
    | Some dir, Some command when !opt_bisect ->
        let test task =
          let call = Driver.prove_task_prepared
            ~command ~timelimit ~memlimit drv task in
          let res = Call_provers.wait_on_call (call ()) () in
          printf "%s %s %s : %a@." fname tname
            (task_goal task).Decl.pr_name.Ident.id_string
            Call_provers.print_prover_result res;
          res.Call_provers.pr_answer = Call_provers.Valid in
        let prepared_task = Driver.prepare_task drv task in
        if not (test prepared_task)
        then printf "I can't bisect %s %s %s which is not valid@." fname tname
          (task_goal task).Decl.pr_name.Ident.id_string
        else
          let prepared_task = Task.bisect test prepared_task in
          output_task_prepared drv fname tname th prepared_task dir
    | None, Some command ->
        let call = Driver.prove_task ~command ~timelimit ~memlimit drv task in
        let res = Call_provers.wait_on_call (call ()) () in
        printf "%s %s %s : %a@." fname tname
          (task_goal task).Decl.pr_name.Ident.id_string
          Call_provers.print_prover_result res
    | None, None ->
        Driver.print_task drv std_formatter task
    | Some dir, _ -> output_task drv fname tname th task dir

let do_tasks env drv fname tname th task =
  let lookup acc t =
    (try Trans.singleton (Trans.lookup_transform t env) with
       Trans.UnknownTrans _ -> Trans.lookup_transform_l t env) :: acc
  in
  let trans = List.fold_left lookup [] !opt_trans in
  let apply tasks tr =
    List.rev (List.fold_left (fun acc task ->
      List.rev_append (Trans.apply tr task) acc) [] tasks)
  in
  let tasks = List.fold_left apply [task] trans in
  List.iter (do_task env drv fname tname th) tasks

let do_theory env drv fname tname th glist =
  if !opt_print_theory then
    printf "%a@." Pretty.print_theory th
  else if !opt_print_namespace then
    printf "%a@." print_th_namespace th
  else if !opt_realize then
    if th.th_path = [] then begin
      eprintf "Theory %s is not from the library.@." tname;
      exit 1
    end else if not (Queue.is_empty glist) then begin
      eprintf "Cannot realize individual goals.@.";
      exit 1
    end else begin
      let drv = Util.of_option drv in
      let task = Task.use_export None th in
      do_tasks env drv fname tname th task
    end
  else begin
    let add acc (x,l) =
      let pr = try ns_find_pr th.th_export l with Not_found ->
        eprintf "Goal '%s' not found in theory '%s'.@." x tname;
        exit 1
      in
      Decl.Spr.add pr acc
    in
    let drv = Util.of_option drv in
    let prs = Queue.fold add Decl.Spr.empty glist in
    let sel = if Decl.Spr.is_empty prs then None else Some prs in
    let tasks = List.rev (split_theory th sel !opt_task) in
    List.iter (do_tasks env drv fname tname th) tasks
  end

let do_global_theory env drv (tname,p,t,glist) =
  let th = try Env.find_theory env p t with Env.TheoryNotFound _ ->
    eprintf "Theory '%s' not found.@." tname;
    exit 1
  in
  do_theory env drv "lib" tname th glist

let do_local_theory env drv fname m (tname,_,t,glist) =
  let th = try Mstr.find t m with Not_found ->
    eprintf "Theory '%s' not found in file '%s'.@." tname fname;
    exit 1
  in
  do_theory env drv fname tname th glist

let do_input env drv = function
  | None, _ when !opt_parse_only || !opt_type_only ->
      ()
  | None, tlist ->
      Queue.iter (do_global_theory env drv) tlist
  | Some f, tlist ->
      let fname, cin = match f with
        | "-" -> "stdin", stdin
        | f   -> f, open_in f
      in
      let m = Env.read_channel ?format:!opt_parser env fname cin in
      close_in cin;
      if !opt_type_only then
        ()
      else
        if Queue.is_empty tlist then
          let glist = Queue.create () in
          let add_th t th mi = Ident.Mid.add th.th_name (t,th) mi in
          let do_th _ (t,th) = do_theory env drv fname t th glist in
          Ident.Mid.iter do_th (Mstr.fold add_th m Ident.Mid.empty)
        else
          Queue.iter (do_local_theory env drv fname m) tlist

let () =
  try
    let env = Env.create_env !opt_loadpath in
    let drv = Util.option_map (load_driver env) !opt_driver in
    Queue.iter (do_input env drv) opt_queue
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C .. byte"
End:
*)
