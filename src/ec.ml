(* -------------------------------------------------------------------- *)
open EcLib
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
let confname    = "easycrypt.conf"
let projname    = "easycrypt.project"
let why3dflconf = Filename.concat XDG.home "why3.conf"

(* -------------------------------------------------------------------- *)
type pconfig = {
  pc_why3     : string option;
  pc_ini      : string option;
  pc_loadpath : (EcLoader.namespace option * string) list;
}

let print_config config =
  let (module Sites) = EcRelocate.sites in

  (* Print git-hash *)
  Format.eprintf "git-hash: %s@\n%!" EcVersion.hash;

  (* Print load path *)
  begin
    let string_of_namespace = function
      | None            -> "<none>"
      | Some `System    -> "<system>"
      | Some (`Named x) -> x in
    Format.eprintf "load-path:@\n%!";
    List.iter
      (fun (nm, dir) ->
         Format.eprintf "  %s@@%s@\n%!" (string_of_namespace nm) dir)
      (EcCommands.loadpath ());
  end;

  (* Print why3 configuration file location *)
  Format.eprintf "why3 configuration file@\n%!";
  begin match config.pc_why3 with
  | None   -> Format.eprintf "  <why3 default>@\n%!"
  | Some f -> Format.eprintf "  %s@\n%!" f end;

  (* Print EC configuration file location *)
  Format.eprintf "EasyCrypt configuration file@\n%!";
  begin match config.pc_ini with
  | None   -> Format.eprintf "  <none>@\n%!"
  | Some f -> Format.eprintf "  %s@\n%!" f end;

  (* Print list of known provers *)
  begin
    let string_of_prover (prover : EcProvers.prover) =
      let fullname =
        Format.asprintf "%s%t@%s"
          prover.pr_name
          (fun fmt ->
            if not (String.is_empty prover.pr_alt) then
              Format.fprintf fmt "[%s]" prover.pr_alt)
          (EcProvers.Version.to_string prover.pr_version)
      in

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

  (* Command path *)
  Format.eprintf "Commands PATH: %s@\n%!" Sites.commands;

  (* Print system PATH *)
  Format.eprintf "System PATH:@\n%!";
  List.iter
    (fun x -> Format.eprintf "  %s@\n%!" x)
    (EcRegexp.split0 (`S (EcRegexp.quote psep))
      (try Sys.getenv "PATH" with Not_found -> ""))

(* -------------------------------------------------------------------- *)
let main () =
  (* When started from Emacs28 on Apple M1, the set of blocks signals *
   * disallows Why3 server to detect external provers completion      *)
  let _ : int list = Unix.sigprocmask Unix.SIG_SETMASK [] in

  let (module Sites) = EcRelocate.sites in

  (* Parse command line arguments *)
  let conffile, options =
    let conffile =
      let xdgini =
        XDG.Config.file
          ~exists:true ~mode:`All ~appname:EcVersion.app
          confname in
      let localini =
        Option.bind
          EcRelocate.sourceroot
          (fun src ->
            let conffile = List.fold_left Filename.concat src ["etc"; confname] in
            if Sys.file_exists conffile then Some conffile else None) in
      List.Exceptionless.hd (Option.to_list localini @ xdgini) in

    let projfile (path : string option) =
      let rec find (path : string) : string option =
        let projfile = Filename.concat path projname in
        if Sys.file_exists projfile then
          Some projfile
        else
          if Filename.dirname path = path then
            None
          else
            find (Filename.dirname path)
      in

      let root =
        match path with
        | Some path ->
           Filename.dirname path
        | None ->
           Unix.getcwd () in

      let root =
        if   Filename.is_relative root
        then Filename.concat (Unix.getcwd ()) root
        else root in

      find root in

    let read_ini_file ini =
      try  Some (EcOptions.read_ini_file ini)
      with
      | Sys_error _ -> None
      | EcOptions.InvalidIniFile (lineno, file) ->
          Format.eprintf "%s:%l: cannot read INI file@." file lineno;
          exit 1
    in

    let getini (path : string option) =
      let inisys =
        Option.bind conffile (fun conffile ->
          Option.map
            (fun ini -> { inic_ini = ini; inic_root = None; })
            (read_ini_file conffile)
        )
      in

      let iniproj =
        Option.bind (projfile path) (fun conffile ->
          Option.map
            (fun ini -> {
               inic_ini  = ini;
               inic_root = Some (Filename.dirname conffile);
            })
            (read_ini_file conffile)
        )
      in

      List.filter_map identity [iniproj; inisys] in

    (conffile, EcOptions.parse_cmdline ~ini:getini Sys.argv) in

  (* Execution of eager commands *)
  begin
    match options.o_command with
    | `Runtest input -> begin
        let root =
          match EcRelocate.sourceroot with
          | Some root ->
              List.fold_left Filename.concat root ["scripts"; "testing"]
          | None ->
              Sites.commands in
        let cmd  = Filename.concat root "runtest" in

        let ecargs =
          let maxjobs =
            input.runo_provers.prvo_maxjobs
            |> omap (fun i -> ["-max-provers"; string_of_int i])
            |> odfl [] in

          let timeout =
            input.runo_provers.prvo_timeout
            |> omap (fun i -> ["-timeout"; string_of_int i])
            |> odfl [] in

          let cpufactor =
            input.runo_provers.prvo_cpufactor
            |> omap (fun i -> ["-cpu-factor"; string_of_int i])
            |> odfl [] in

          let ppwidth =
            input.runo_provers.prvo_ppwidth
            |> omap (fun i -> ["-pp-width"; string_of_int i])
            |> odfl [] in

          let provers =
            odfl [] input.runo_provers.prvo_provers
            |> List.map (fun prover -> ["-p"; prover])
            |> List.flatten in

          let pragmas =
            input.runo_provers.prvo_pragmas
            |> List.map (fun pragmas -> ["-pragmas"; pragmas])
            |> List.flatten  in

          let checkall =
            if input.runo_provers.prvo_checkall then
              ["-check-all"]
            else [] in

          let profile =
            if input.runo_provers.prvo_profile then
              ["-profile"]
            else [] in

          let iterate =
            if input.runo_provers.prvo_iterate then
              ["-iterate"]
            else [] in

          let why3srv =
            input.runo_provers.prvo_why3server
            |> omap (fun server -> ["-server"; server])
            |> odfl [] in

          let why3 =
            options.o_options.o_why3
            |> omap (fun why3 -> ["-why3"; why3])
            |> odfl [] in

          let reloc =
            if options.o_options.o_reloc then
              ["-reloc"]
            else [] in

          let noevict =
            options.o_options.o_ovrevict
            |> List.map (fun p -> ["-no-evict"; p])
            |> List.flatten in

          let boot =
            if options.o_options.o_loader.ldro_boot then
              ["-boot"]
            else [] in

          let idirs =
            options.o_options.o_loader.ldro_idirs
            |> List.map (fun (pfx, name, rec_) ->
                 let pfx = odfl "" (omap (fun pfx -> pfx ^ ":") pfx) in
                 let opt = if rec_ then "-R" else "-I" in
                 [opt; pfx ^ name])
            |> List.flatten in


          List.flatten [
            maxjobs; timeout; cpufactor; ppwidth;
            provers; pragmas; checkall ; profile;
            iterate; why3srv; why3     ; reloc  ;
            noevict; boot   ; idirs    ;
          ]
        in

        let args =
            [
              "runtest";
              Format.sprintf "--bin=%s" Sys.executable_name;
            ]
          @ Option.to_list (
              Option.map
                (Format.sprintf "--report=%s")
                input.runo_report
            )
          @ Option.to_list (
              Option.map
                (Format.sprintf "--jobs=%d")
                input.runo_jobs
            )
          @ List.map
              (Format.sprintf "--bin-args=%s")
              (ecargs @ input.runo_rawargs)
          @ [input.runo_input]
          @ input.runo_scenarios
        in
        Format.eprintf "Executing: %s@." (String.concat " " (cmd :: args));
        Unix.execv cmd (Array.of_list args)
      end

    | _ -> ()
  end;

  (* chrdir_$PATH if in reloc mode (FIXME / HACK) *)
  let relocdir =
    match options.o_options.o_reloc with
    | true when Option.is_none EcRelocate.sourceroot ->
        let pwd = Sys.getcwd () in
        Sys.chdir (
          List.fold_left Filename.concat
            (List.hd Sites.theories)
            (List.init 3 (fun _ -> ".."))
        ); Some pwd

    | true ->
        Format.eprintf "cannot relocate a local installation@.";
        exit 1

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
    List.iter (fun theory ->
      EcCommands.addidir ~namespace:`System (Filename.concat theory "prelude");
      if not ldropts.ldro_boot then
        EcCommands.addidir ~namespace:`System ~recursive:true theory
    ) Sites.theories;
    List.iter (fun (onm, name, isrec) ->
        EcCommands.addidir
          ?namespace:(omap (fun nm -> `Named nm) onm)
          ~recursive:isrec name)
      ldropts.ldro_idirs;
  end;

  (* Initialize printer *)
  EcCorePrinting.Registry.register (module EcPrinting);

  (* Register user messages printers *)
  begin let open EcUserMessages in register () end;

  (* Initialize I/O + interaction module *)
  let module State = struct
    type t = {
      prvopts     : prv_options;
      input       : string option;
      terminal    : T.terminal lazy_t;
      interactive : bool;
      eco         : bool;
      gccompact   : int option;
    }
  end in

  let state : State.t =
    match options.o_command with
    | `Config ->
        let config = {
          pc_why3     = why3conf;
          pc_ini      = conffile;
          pc_loadpath = EcCommands.loadpath ();
        } in

        print_config config; exit 0

    | `Why3Config -> begin
        let conf = cp_why3conf ~exists:false ~mode:`User in

        conf |> Option.iter (fun conf ->
          EcUtils.makedirs (Filename.dirname conf));

        let () =
          let ulnk = conf |> odfl why3dflconf in
          try Unix.unlink ulnk with Unix.Unix_error _ -> ()
        in

        let pid =
          let args = ["why3"; "config"; "detect"] in
          let args = args @ (conf |> omap (fun x -> ["-C"; x])|> odfl []) in

          Printf.eprintf "Executing: %s\n%!" (String.concat " " args);
          Unix.create_process "why3" (Array.of_list args)
            Unix.stdin Unix.stdout Unix.stderr
        in

        let code =
          match snd (Unix.waitpid [] pid) with
          | WSIGNALED _ -> 127
          | WEXITED   e -> e
          | WSTOPPED  _ -> assert false in exit code
      end

    | `Cli cliopts -> begin
        let terminal =
          if   cliopts.clio_emacs
          then lazy (T.from_emacs ())
          else lazy (T.from_tty ())

        in

        { prvopts     = cliopts.clio_provers
        ; input       = None
        ; terminal    = terminal
        ; interactive = true
        ; eco         = false
        ; gccompact   = None }

    end

    | `Compile cmpopts -> begin
        let name = cmpopts.cmpo_input in

        begin try
          let ext = Filename.extension name in
          ignore (EcLoader.getkind ext : EcLoader.kind)
        with EcLoader.BadExtension ext ->
          Format.eprintf "do not know what to do with %s@." ext;
          exit 1
        end;


        let gcstats  = cmpopts.cmpo_gcstats in
        let progress = if cmpopts.cmpo_script then `Script else `Human in
        let terminal =
          lazy (T.from_channel ~name ~gcstats ~progress (open_in name))
        in

        { prvopts     = {cmpopts.cmpo_provers with prvo_iterate = true}
        ; input       = Some name
        ; terminal    = terminal
        ; interactive = false
        ; eco         = cmpopts.cmpo_noeco
        ; gccompact   = cmpopts.cmpo_compact }

      end

    | `Runtest _ ->
        (* Eagerly executed *)
        assert false
  in

  (match state.input with
   | Some input -> EcCommands.addidir (Filename.dirname input)
   | None ->
       match relocdir with
       | None     -> EcCommands.addidir Filename.current_dir_name
       | Some pwd -> EcCommands.addidir pwd);

  (* Check if the .eco is up-to-date and exit if so *)
  oiter
    (fun input -> if EcCommands.check_eco input then exit 0)
    state.input;

  let finalize_input input scope =
    match input with
    | Some input ->
        let nameo = EcEco.get_eco_filename input in
        let kind  =
          try  EcLoader.getkind (Filename.extension input)
          with EcLoader.BadExtension _ -> assert false in

        assert (nameo <> input);

        let eco = EcEco.{
            eco_root    = EcEco.{
              eco_digest  = Digest.file input;
              eco_kind    = kind;
            };
            eco_depends = EcMaps.Mstr.of_list (
              List.map
                (fun (x : EcScope.required_info) ->
                   let ecr = EcEco.{
                     eco_digest = x.rqd_digest;
                     eco_kind   = x.rqd_kind;
                   } in (x.rqd_name, (ecr, x.rqd_direct)))
                (EcScope.Theory.required scope));
        } in

        let out = open_out nameo in

        EcUtils.try_finally
          (fun () ->
             Format.fprintf
               (Format.formatter_of_out_channel out) "%a@."
               EcEco.pp eco)
          (fun () -> close_out out)

    | None -> ()
  in

  let tstats : EcLocation.t -> float option -> unit =
    match options.o_command with
    | `Compile { cmpo_tstats = Some out } ->
        let channel = Format.formatter_of_out_channel (open_out out) in
        let fmt loc tdelta =
          Format.fprintf channel "%s %f\n%!"
            (EcLocation.tostring_raw ~with_fname:false loc) tdelta in
        fun loc tdelta -> oiter (fmt loc) tdelta
    | _ -> fun _ _ -> () in

  (* Instantiate terminal *)
  let lazy terminal = state.terminal in

  (* Initialize PRNG *)
  Random.self_init ();

  (* Connect to external Why3 server if requested *)
  state.prvopts.prvo_why3server |> oiter (fun server ->
    try
      Why3.Prove_client.connect_external server
    with Why3.Prove_client.ConnectionError e ->
      Format.eprintf "cannot connect to Why3 server `%s': %s" server e;
      exit 1);

  (* Display Copyright *)
  if T.interactive terminal then
    T.notice ~immediate:true `Warning copyright terminal;

  try
    if T.interactive terminal then Sys.catch_break true;

    (* Interaction loop *)
    let first = ref `Init in
    let cmdcounter = ref 0 in

    while true do
      let terminate = ref false in

      try
        begin match !first with
        | `Init | `Restart ->
            let restart = (!first = `Restart) in

            (* Initialize global scope *)
            let checkmode = {
              EcCommands.cm_checkall  = state.prvopts.prvo_checkall;
              EcCommands.cm_timeout   = odfl 3 (state.prvopts.prvo_timeout);
              EcCommands.cm_cpufactor = odfl 1 (state.prvopts.prvo_cpufactor);
              EcCommands.cm_nprovers  = odfl 4 (state.prvopts.prvo_maxjobs);
              EcCommands.cm_provers   = state.prvopts.prvo_provers;
              EcCommands.cm_profile   = state.prvopts.prvo_profile;
              EcCommands.cm_iterate   = state.prvopts.prvo_iterate;
            } in

            EcCommands.initialize ~restart
              ~undo:state.interactive ~boot:ldropts.ldro_boot ~checkmode;
            (try
               List.iter EcCommands.apply_pragma state.prvopts.prvo_pragmas
             with EcCommands.InvalidPragma x ->
               EcScope.hierror "invalid pragma: `%s'\n%!" x);

            let notifier (lvl : EcGState.loglevel) (lazy msg) =
              T.notice ~immediate:true lvl msg terminal
            in

            EcCommands.addnotifier notifier;
            oiter (fun ppwidth ->
              let gs = EcEnv.gstate (EcScope.env (EcCommands.current ())) in
              EcGState.setvalue "PP:width" (`Int ppwidth) gs)
              state.prvopts.prvo_ppwidth;
            first := `Loop

        | `Loop -> ()
        end;

        oiter (T.setwidth terminal)
          (let gs = EcEnv.gstate (EcScope.env (EcCommands.current ())) in
           match EcGState.getvalue "PP:width" gs with
           | Some (`Int i) -> Some i | _ -> None);

        begin
          match EcLocation.unloc (T.next terminal) with
          | EP.P_Prog (commands, locterm) ->
              terminate := locterm;
              List.iter
                (fun p ->
                   let loc = p.EP.gl_action.EcLocation.pl_loc in
                   let timed = p.EP.gl_debug = Some `Timed in
                   let break = p.EP.gl_debug = Some `Break in
                   let ignore_fail = ref false in
                     try
                       let tdelta = EcCommands.process ~timed ~break p.EP.gl_action in
                       if p.EP.gl_fail then begin
                         ignore_fail := true;
                         raise (EcScope.HiScopeError (None, "this command is expected to fail"))
                       end;
                       tstats loc tdelta
                     with
                     | EcCommands.Restart ->
                         raise EcCommands.Restart
                     | e -> begin
                       if !ignore_fail || not p.EP.gl_fail then begin
                         if Printexc.backtrace_status () then begin
                           if not (T.interactive terminal) then
                             Printf.fprintf stderr "%t\n%!" Printexc.print_backtrace
                         end;
                         raise (EcScope.toperror_of_exn ~gloc:loc e)
                       end;
                       if T.interactive terminal then begin
                         let error =
                           Format.asprintf
                             "The following error has been ignored:@.@.@%a"
                             EcPException.exn_printer e in
                         T.notice ~immediate:true `Info error terminal
                       end
                   end)
                commands

          | EP.P_Undo i ->
              EcCommands.undo i
          | EP.P_Exit ->
              terminate := true
        end;
        T.finish `ST_Ok terminal;

        state.gccompact |> Option.iter (fun i ->
          incr cmdcounter;
          if i = !cmdcounter then begin
            cmdcounter := 0;
            Gc.compact ()
          end
        );

        if !terminate then begin
            T.finalize terminal;
            if not state.eco then
              finalize_input state.input (EcCommands.current ());
            exit 0
          end;
      with
      | EcCommands.Restart ->
          first := `Restart

      | e -> begin
          T.finish
            (`ST_Failure (EcScope.toperror_of_exn e))
            terminal;
          if (!first = `Init) || not (T.interactive terminal) then
            exit 1
        end
    done
  with e ->
    (try T.finalize terminal with _ -> ());
    raise e

(* -------------------------------------------------------------------- *)
let () = main ()
