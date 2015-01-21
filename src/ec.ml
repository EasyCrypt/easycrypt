(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions

module T = EcTerminal

(* -------------------------------------------------------------------- *)
let copyright =
  let sentences =
    List.flatten
      [String.splitlines EcVersion.copyright;
       String.splitlines EcVersion.license  ; ] in

  String.concat "\n"
    (List.map
       (fun s -> Printf.sprintf ">> %s" s)
       sentences)

(* -------------------------------------------------------------------- *)
let psep = match Sys.os_type with "Win32" -> ";" | _ -> ":"

(* -------------------------------------------------------------------- *)
type pconfig = {
  pc_why3     : string option;
  pc_pwrapper : string option;
  pc_loadpath : (bool * string) list;
}

let print_config config =
  (* Print load path *)
  Format.eprintf "load-path:@\n%!";
  List.iter
    (fun (sys, dir) ->
       Format.eprintf "  <%.6s>@@%s@\n%!"
         (if sys then "system" else "user") dir)
    (EcCommands.loadpath ());

  (* Print why3 configuration file location *)
  Format.eprintf "why3 configuration file@\n%!";
  begin match config.pc_why3 with
  | None   -> Format.eprintf "  <why3 default>@\n%!"
  | Some f -> Format.eprintf "  %s@\n%!" f end;

  (* Print prover wrapper *)
  Format.eprintf "prover wrapper@\n%!";
  begin match config.pc_pwrapper with
  | None -> Format.eprintf "  <none>@\n%!"
  | Some wrapper -> Format.eprintf "  %s@\n%!" wrapper end;

  (* Print list of known provers *)
  begin
    let string_of_prover prover =
      let fullname =
        Printf.sprintf "%s@%s"
          prover.EcProvers.pr_name
          prover.EcProvers.pr_version in

      match prover.EcProvers.pr_evicted with
      | None -> fullname
      | Some (cause, overridden) ->
          let cause =
            match cause with
            | `Inconsistent -> "inconsistent"
          in
            Printf.sprintf
              "%s [evicted:%s/overridden=%b]"
              fullname cause overridden
    in

    let provers = EcProvers.known ~evicted:true in

    Format.eprintf "known provers: %s@\n%!"
      (String.concat ", " (List.map string_of_prover provers))
  end;

  (* Print system PATH *)
  Format.eprintf "System PATH:@\n%!";
  List.iter
    (fun x -> Format.eprintf "  %s@\n%!" x)
    (Str.split
       (Str.regexp (Str.quote psep))
       (try Sys.getenv "PATH" with Not_found -> ""))

(* -------------------------------------------------------------------- *)
let _ =
  let myname  = Filename.basename Sys.executable_name
  and mydir   = Filename.dirname  Sys.executable_name in

  let eclocal =
    let re = Str.regexp "^ec\\.\\(native\\|byte\\)\\(\\.exe\\)?$" in
    Str.string_match re myname 0
  in

  let bin =
    match Sys.os_type with
    | "Win32" | "Cygwin" -> fun (x : string) -> x ^ ".exe"
    | _ -> fun (x : string) -> x
  in

  let resource name =
    match eclocal with
    | true ->
        if Filename.basename (Filename.dirname mydir) = "_build" then
          List.fold_left Filename.concat mydir
            ([Filename.parent_dir_name;
              Filename.parent_dir_name] @ name)
        else
          List.fold_left Filename.concat mydir name

    | false ->
        List.fold_left Filename.concat mydir
          ([Filename.parent_dir_name; "lib"; "easycrypt"] @ name)
  in

  let pwrapper =
    (* Find provers wrapper *)
    match Sys.os_type with
    | "Win32" -> None
    | _ ->
      let wrapper = resource ["system"; bin "callprover"] in
        if   Sys.file_exists wrapper
        then Some wrapper
        else None
  in

  (* If in local mode, add the toolchain bin/ path to $PATH *)
  if eclocal then begin
    let module E = struct exception Found of string end in

    let rootdir = resource ["_tools"] in
    let regexp  = Str.regexp "^ocaml-[0-9.]+$" in

    if Sys.file_exists rootdir && Sys.is_directory rootdir then begin
      let dirs = Sys.readdir rootdir in

      try
        for i = 0 to (Array.length dirs) - 1 do
          let target = Filename.concat rootdir dirs.(i) in
            if Sys.is_directory target then
              if Str.string_match regexp dirs.(i) 0 then
                raise (E.Found target)
        done
      with E.Found target ->
        let target = List.fold_left
          Filename.concat target ["opam"; "system"; "bin"] in
        let path = try Unix.getenv "PATH" with Not_found -> "" in
        let path = Printf.sprintf "%s%s%s" target psep path in
        Unix.putenv "PATH" path
    end
  end;

  (* Parse command line arguments *)
  let options = EcOptions.parse Sys.argv in

  (* chrdir_$PATH if in reloc mode (FIXME / HACK) *)
  let relocdir =
    match options.o_options.o_reloc with
    | true ->
      let pwd = Sys.getcwd () in
        Sys.chdir (resource [".."; ".."]); Some pwd
    | false ->
        None
  in

  (* Initialize why3 engine *)
  let why3conf =
    match options.o_options.o_why3 with
    | None when eclocal -> begin
      let why3conf = resource ["_tools"; "why3.local.conf"] in
        match Sys.file_exists why3conf with
        | false -> None
        | true  -> Some why3conf
    end
    | why3conf -> why3conf
  
  and ovrevict = options.o_options.o_ovrevict in

  begin
    try  EcProvers.initialize ~ovrevict ?why3conf ()
    with e ->
      Format.eprintf
        "cannot initialize Why3 engine: %a@."
        EcPException.exn_printer e;
      exit 1
  end;

  (* Initialize load path *)
  let ldropts = options.o_options.o_loader in

  begin
    let theories = resource ["theories"] in

    EcCommands.addidir ~system:true (Filename.concat theories "prelude");
    if not ldropts.ldro_boot then
      EcCommands.addidir ~system:true ~recursive:true theories;
    List.iter EcCommands.addidir ldropts.ldro_idirs;
  end;

  (* Initialize I/O + interaction module *)
  let (prvopts, input, terminal) =
    match options.o_command with
    | `Config ->
        let config = {
          pc_why3     = why3conf;
          pc_pwrapper = pwrapper;
          pc_loadpath = EcCommands.loadpath ();
        } in 

        print_config config; exit 0

    | `Cli cliopts -> begin
        let terminal =
          match (cliopts.clio_emacs, cliopts.clio_webui) with
          | (true, false)  -> lazy (EcTerminal.from_emacs ())
          | (false, true)  -> lazy (EcTerminal.from_webui ())
          | (_, _) -> lazy (EcTerminal.from_tty ())
        in
          (cliopts.clio_provers, None, terminal)
    end

    | `Compile cmpopts -> begin
        let input = cmpopts.cmpo_input in
        let terminal = lazy (EcTerminal.from_channel ~name:input (open_in input)) in
          (cmpopts.cmpo_provers, Some input, terminal)
    end
  in

  (match input with
   | Some input -> EcCommands.addidir (Filename.dirname input)
   | None ->
       match relocdir with
       | None     -> EcCommands.addidir Filename.current_dir_name
       | Some pwd -> EcCommands.addidir pwd);

  (* Initialize global scope *)
  begin
    let checkmode = {
      EcCommands.cm_checkall  = prvopts.prvo_checkall;
      EcCommands.cm_timeout   = prvopts.prvo_timeout;
      EcCommands.cm_cpufactor = prvopts.prvo_cpufactor;
      EcCommands.cm_nprovers  = prvopts.prvo_maxjobs;
      EcCommands.cm_provers   = prvopts.prvo_provers;
      EcCommands.cm_wrapper   = pwrapper;
      EcCommands.cm_profile   = prvopts.prvo_profile;
    } in

    EcCommands.initialize ~boot:ldropts.ldro_boot ~checkmode
  end;

  begin
    try
      List.iter EcCommands.apply_pragma prvopts.prvo_pragmas
    with EcCommands.InvalidPragma x ->
      (Printf.eprintf "invalid pragma: `%s'\n%!" x; exit 1)
  end;

  (* Instantiate terminal *)
  let lazy terminal = terminal in

  (* Initialize PRNG *)
  Random.self_init ();

  (* Initialize fortune *)
  EcFortune.init ();

  (* Display Copyright *)
  if EcTerminal.interactive terminal then
    EcTerminal.notice ~immediate:true `Warning copyright terminal;

  try
    begin
      let notifier (lvl : EcGState.loglevel) (lazy msg) =
        EcTerminal.notice ~immediate:true lvl msg terminal
      in EcCommands.addnotifier notifier
    end;

    (* Interaction loop *)
    while true do
      let terminate = ref false in

      try
        begin
          match EcLocation.unloc (EcTerminal.next terminal) with
          | EcParsetree.P_Prog (commands, locterm) ->
              terminate := locterm;
              List.iter
                (fun p ->
                   let loc = p.EcLocation.pl_loc in
                     try  EcCommands.process p
                     with e -> begin
                       if not (EcTerminal.interactive terminal) then
                         Printf.fprintf stderr "%t\n%!" Printexc.print_backtrace;
                     raise (EcCommands.toperror_of_exn ~gloc:loc e)
                   end)
                commands

          | EcParsetree.P_Undo i ->
              EcCommands.undo i
        end;
        EcTerminal.finish `ST_Ok terminal;
        if !terminate then (EcTerminal.finalize terminal; exit 0);
      with e -> begin
        EcTerminal.finish
          (`ST_Failure (EcCommands.toperror_of_exn e))
          terminal;
        if not (EcTerminal.interactive terminal) then
          exit 1
      end
    done
  with e ->
    (try EcTerminal.finalize terminal with _ -> ());
    raise e
