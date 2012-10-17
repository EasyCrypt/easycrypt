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

let usage_msg =
  sprintf "Usage: %s [options]\n
  Environment variables WHY3LIB, WHY3DATA, and WHY3CONFIG
  can be set to change the default paths.@."
    (Filename.basename Sys.argv.(0))

let version_msg = sprintf
  "Why3 configuration utility, version %s (build date: %s)"
  Config.version Config.builddate

(* let libdir = ref None *)
(* let datadir = ref None *)
let conf_file = ref None
let autoprovers = ref false
let autoplugins = ref false
let opt_version = ref false

let opt_list_flags = ref false
let opt_debug_all = ref false

let save = ref true

let set_oref r = (fun s -> r := Some s)

let plugins = Queue.create ()
let add_plugin x = Queue.add x plugins

let opt_debug = ref []
let add_opt_debug x = opt_debug := x::!opt_debug

let option_list = Arg.align [
  (* "--libdir", Arg.String (set_oref libdir), *)
  (* "<dir> set the lib directory ($WHY3LIB)"; *)
  (* "--datadir", Arg.String (set_oref datadir), *)
  (* "<dir> set the data directory ($WHY3DATA)"; *)
  "-C", Arg.String (set_oref conf_file),
  "<file> Config file to create";
  "--config", Arg.String (set_oref conf_file),
      " same as -C";
  "--detect-provers", Arg.Set autoprovers,
  " Search for provers in $PATH";
  "--detect-plugins", Arg.Set autoplugins,
  " Search for plugins in the default library directory";
  "--detect", Arg.Unit (fun () -> autoprovers := true; autoplugins := true),
  " Search for both provers and plugins";
  "--install-plugin", Arg.String add_plugin,
  " Install a plugin to the actual libdir";
  "--dont-save", Arg.Clear save,
  " Do not modify the config file";
  "--list-debug-flags", Arg.Set opt_list_flags,
      " List known debug flags";
  "--debug-all", Arg.Set opt_debug_all,
      " Set all debug flags (except parse_only and type_only)";
  "--debug", Arg.String add_opt_debug,
      "<flag> Set a debug flag";
  "--version", Arg.Set opt_version,
  " Print version information"
]

let anon_file _ = Arg.usage option_list usage_msg; exit 1

let install_plugin main p =
  begin match Plugin.check_plugin p with
    | Plugin.Plubad -> eprintf "Unknown extension (.cmo|.cmxs) : %s@." p;
      raise Exit
    | Plugin.Pluother ->
      eprintf "The plugin %s will not be used with this kind of compilation \
and it has not been tested@."
        p
    | Plugin.Plugood -> ()
    | Plugin.Plufail exn -> eprintf "The plugin %s dynlink failed :@.%a@."
      p Exn_printer.exn_printer exn; raise Exit
  end;
  let base = Filename.basename p in
  let plugindir = Whyconf.pluginsdir main in
  if not (Sys.file_exists plugindir) then begin
    eprintf "Error: plugin directory %s not found.@." plugindir;
    raise Exit
  end;
  let target = (Filename.concat plugindir base) in
  if p <> target then Sysutil.copy_file p target;
  Whyconf.add_plugin main (Filename.chop_extension target)

let plugins_auto_detection config =
  let main = get_main config in
  let main = set_plugins main [] in
  let dir = Whyconf.pluginsdir main in
  let files = Sys.readdir dir in
  let fold main p =
    if p.[0] == '.' then main else
    let p = Filename.concat dir p in
    try eprintf "== Found %s ==@." p;
        install_plugin main p
    with Exit -> main
  in
  let main = Array.fold_left fold main files in
  set_main config main

let main () =
  (** Parse the command line *)
  Arg.parse option_list anon_file usage_msg;

  let opt_list = ref false in
  if !opt_version then begin
    opt_list := true;
    printf "%s@." version_msg
  end;

  (** Debug flag *)
  if !opt_debug_all then begin
    List.iter (fun (_,f,_) -> Debug.set_flag f) (Debug.list_flags ());
    Debug.unset_flag Typing.debug_parse_only;
    Debug.unset_flag Typing.debug_type_only
  end;

  List.iter (fun s -> Debug.set_flag (Debug.lookup_flag s)) !opt_debug;

  if !opt_list_flags then begin
    opt_list := true;
    let print fmt (p,_,_) = fprintf fmt "%s" p in
    printf "@[<hov 2>Known debug flags:@\n%a@]@."
      (Pp.print_list Pp.newline print)
      (List.sort Pervasives.compare (Debug.list_flags ()))
  end;
  if !opt_list then exit 0;

  (** Main *)
  let config =
    try
      read_config !conf_file
    with
      | Rc.CannotOpen (f, s)
      | Whyconf.ConfigFailure (f, s) ->
         eprintf "warning: cannot read config file %s:@\n  %s@." f s;
         autoprovers := true;
         autoplugins := true;
         default_config f
  in
  let main = get_main config in
  (* let main = option_apply main (fun d -> {main with libdir = d})
     !libdir in *)
  (* let main = option_apply main (fun d -> {main with datadir = d})
     !datadir in *)
  let main = try Queue.fold install_plugin main plugins with Exit -> exit 1 in
  let config = set_main config main in
  let conf_file = get_conf_file config in
  if not (Sys.file_exists conf_file) then begin
    autoprovers := true;
    autoplugins := true;
  end;
  let config =
    if !autoprovers
    then Autodetection.run_auto_detection config
    else config
  in
  let config =
    if !autoplugins
    then plugins_auto_detection config
    else config
  in
  if !save then begin
    printf "Save config to %s@." conf_file;
    save_config config
  end

let () =
  try
    main ()
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

