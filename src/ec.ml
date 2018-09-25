(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions

module EP = EcParsetree
module T  = EcTerminal

(* -------------------------------------------------------------------- *)
let copyright =
  let sentences =
    List.flatten
      [EcVersion.copyright;
       String.split_lines EcVersion.License.engine;
       ["Standard Library (theories/**/*.ec): "];
       List.map (Printf.sprintf "\t%s")
         (String.split_lines EcVersion.License.stdlib);
       [""; Format.sprintf "GIT hash: %s" EcVersion.hash] ]
  in
  String.concat "\n"
    (List.map
       (fun s -> Printf.sprintf ">> %s" s)
       sentences)

(* -------------------------------------------------------------------- *)
let psep = match Sys.os_type with "Win32" -> ";" | _ -> ":"

(* -------------------------------------------------------------------- *)
let confname    = "easycypt.conf"
let why3dflconf = Filename.concat XDG.home "why3.conf"

(* -------------------------------------------------------------------- *)
type pconfig = {
  pc_why3     : string option;
  pc_pwrapper : string option;
  pc_loadpath : (bool * string) list;
}

let print_config config =
  (* Print git-hash *)
  Format.eprintf "git-hash: %s@\n%!" EcVersion.hash;

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
    (EcRegexp.split0 (`S (EcRegexp.quote psep))
      (try Sys.getenv "PATH" with Not_found -> ""))

(* -------------------------------------------------------------------- *)
let main () =
  let myname  = Filename.basename Sys.executable_name
  and mydir   = Filename.dirname  Sys.executable_name in

  let eclocal =
    let rex = EcRegexp.regexp "^ec\\.(?:native|byte)(?:\\.exe)?$" in
    EcRegexp.match_ (`C rex) myname
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

  (* Parse command line arguments *)
  let options =
    let ini =
      let xdgini =
        XDG.Config.file ~exists:true ~mode:`All ~appname:EcVersion.app
          confname
      in List.hd (List.append xdgini [resource ["etc"; "easycrypt.conf"]]) in

    let ini =
      try  Some (EcOptions.read_ini_file ini)
      with
      | Sys_error _ -> None
      | EcOptions.InvalidIniFile (lineno, file) ->
          Format.eprintf "%s:%l: cannot read INI file@." file lineno;
          exit 1

    in EcOptions.parse_cmdline ?ini Sys.argv in

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
  let cp_why3conf ~exists ~mode : string option =
    match options.o_options.o_why3 with
    | None ->
        let confs =
          XDG.Config.file
            ~exists ~mode ~appname:EcVersion.app "why3.conf"
        in List.nth_opt confs 0

    | Some _ as aout -> aout in

  let why3conf = cp_why3conf ~exists:true ~mode:`All
  and ovrevict = options.o_options.o_ovrevict in

  if options.o_command <> `Why3Config then begin
    try
      EcProvers.initialize ~ovrevict ?why3conf ()
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

  (* Register user messages printers *)
  begin let open EcUserMessages in register () end;

  (* Initialize I/O + interaction module *)
  let (prvopts, input, terminal, interactive) =
    match options.o_command with
    | `Config ->
        let config = {
          pc_why3     = why3conf;
          pc_pwrapper = pwrapper;
          pc_loadpath = EcCommands.loadpath ();
        } in

        print_config config; exit 0

    | `Why3Config -> begin
        let conf = cp_why3conf ~exists:false ~mode:`User in

        let () =
          let ulnk = conf |> odfl why3dflconf in
          try Unix.unlink ulnk with Unix.Unix_error _ -> ()
        in

        let pid =
          let args = ["why3"; "config"; "--detect"] in
          let args = args @ (conf |> omap (fun x -> ["-C"; x])|> odfl []) in

          Printf.eprintf "Executing: %s\n%!" (String.concat " " args);
          Unix.create_process "why3" (Array.of_list args)
            Unix.stdin Unix.stdout Unix.stderr
        in

        exit (fst (Unix.waitpid [] pid))
      end

    | `Cli cliopts -> begin
        let terminal =
          if   cliopts.clio_emacs
          then lazy (EcTerminal.from_emacs ())
          else lazy (EcTerminal.from_tty ())

        in (cliopts.clio_provers, None, terminal, true)
    end

    | `Compile cmpopts -> begin
        let name     = cmpopts.cmpo_input in
        let gcstats  = cmpopts.cmpo_gcstats in
        let terminal =
          lazy (EcTerminal.from_channel ~name ~gcstats (open_in name))
        in
          ({cmpopts.cmpo_provers with prvo_iterate = true},
           Some name, terminal, false)
    end
  in

  (match input with
   | Some input -> EcCommands.addidir (Filename.dirname input)
   | None ->
       match relocdir with
       | None     -> EcCommands.addidir Filename.current_dir_name
       | Some pwd -> EcCommands.addidir pwd);

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
    if EcTerminal.interactive terminal then Sys.catch_break true;

    (* Interaction loop *)
    let first = ref `Init in

    while true do
      let terminate = ref false in

      try
        begin match !first with
        | `Init | `Restart ->
            let restart = (!first = `Restart) in

            (* Initialize global scope *)
            let checkmode = {
              EcCommands.cm_checkall  = prvopts.prvo_checkall;
              EcCommands.cm_timeout   = prvopts.prvo_timeout;
              EcCommands.cm_cpufactor = prvopts.prvo_cpufactor;
              EcCommands.cm_nprovers  = prvopts.prvo_maxjobs;
              EcCommands.cm_provers   = prvopts.prvo_provers;
              EcCommands.cm_wrapper   = pwrapper;
              EcCommands.cm_profile   = prvopts.prvo_profile;
              EcCommands.cm_iterate   = prvopts.prvo_iterate;
            } in

            EcCommands.initialize ~restart
              ~undo:interactive ~boot:ldropts.ldro_boot ~checkmode;
            (try
               List.iter EcCommands.apply_pragma prvopts.prvo_pragmas
             with EcCommands.InvalidPragma x ->
               EcScope.hierror "invalid pragma: `%s'\n%!" x);

            let notifier (lvl : EcGState.loglevel) (lazy msg) =
              EcTerminal.notice ~immediate:true lvl msg terminal
            in

            EcCommands.addnotifier notifier;
            oiter (fun ppwidth ->
              let gs = EcEnv.gstate (EcScope.env (EcCommands.current ())) in
              EcGState.setvalue "PP:width" (`Int ppwidth) gs)
              prvopts.prvo_ppwidth;
            first := `Loop

        | `Loop -> ()
        end;

        oiter (EcTerminal.setwidth terminal)
          (let gs = EcEnv.gstate (EcScope.env (EcCommands.current ())) in
           match EcGState.getvalue "PP:width" gs with
           | Some (`Int i) -> Some i | _ -> None);

        begin
          match EcLocation.unloc (EcTerminal.next terminal) with
          | EP.P_Prog (commands, locterm) ->
              terminate := locterm;
              List.iter
                (fun p ->
                   let loc = p.EP.gl_action.EcLocation.pl_loc in
                     try  EcCommands.process ~timed:p.EP.gl_timed p.EP.gl_action
                     with
                     | EcCommands.Restart ->
                         raise EcCommands.Restart
                     | e -> begin
                       if Printexc.backtrace_status () then begin
                         if not (EcTerminal.interactive terminal) then
                           Printf.fprintf stderr "%t\n%!" Printexc.print_backtrace
                       end;
                       raise (EcScope.toperror_of_exn ~gloc:loc e)
                   end)
                commands

          | EP.P_Undo i ->
              EcCommands.undo i
        end;
        EcTerminal.finish `ST_Ok terminal;
        if !terminate then (EcTerminal.finalize terminal; exit 0);
      with
      | EcCommands.Restart ->
          first := `Restart

      | e -> begin
          EcTerminal.finish
            (`ST_Failure (EcScope.toperror_of_exn e))
            terminal;
          if (!first = `Init) || not (EcTerminal.interactive terminal) then
            exit 1
        end
    done
  with e ->
    (try EcTerminal.finalize terminal with _ -> ());
    raise e

(* -------------------------------------------------------------------- *)
let () = main ()
