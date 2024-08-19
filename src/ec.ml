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
let why3dflconf = Filename.concat XDG.home "why3.conf"

(* -------------------------------------------------------------------- *)
type pconfig = {
  pc_why3     : string option;
  pc_ini      : string option;
  pc_loadpath : (EcLoader.namespace option * string) list;
}

let print_config config =
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
  (* When started from Emacs28 on Apple M1, the set of blocks signals *
   * disallows Why3 server to detect external provers completion      *)
  let _ : int list = Unix.sigprocmask Unix.SIG_SETMASK [] in

  let theories = EcRelocate.Sites.theories in

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

    let ini =
      Option.bind conffile (fun ini ->
        try  Some (EcOptions.read_ini_file ini)
        with
        | Sys_error _ -> None
        | EcOptions.InvalidIniFile (lineno, file) ->
            Format.eprintf "%s:%l: cannot read INI file@." file lineno;
            exit 1
      )

    in (conffile, EcOptions.parse_cmdline ?ini Sys.argv) in

  (* Execution of eager commands *)
  begin
    match options.o_command with
    | `Runtest input -> begin
        let root =
          match EcRelocate.sourceroot with
          | Some root ->
              List.fold_left Filename.concat root ["scripts"; "testing"]
          | None ->
              EcRelocate.resource ["commands"] in
        let cmd  = Filename.concat root "runtest" in
        let args = ["runtest"; input.runo_input] @ input.runo_scenarios in
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
            (List.hd EcRelocate.Sites.theories)
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
    ) theories;
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
  let (prvopts, input, terminal, interactive, eco, gendoc) =
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

        in (cliopts.clio_provers, None, terminal, true, false, false)
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
          ({cmpopts.cmpo_provers with prvo_iterate = true},
           Some name, terminal, false, cmpopts.cmpo_noeco, cmpopts.cmpo_doc)

      end

    | `Runtest _ ->
        (* Eagerly executed *)
        assert false

  in

  (match input with
   | Some input -> EcCommands.addidir (Filename.dirname input)
   | None ->
       match relocdir with
       | None     -> EcCommands.addidir Filename.current_dir_name
       | Some pwd -> EcCommands.addidir pwd);

  (* Check if the .eco is up-to-date and exit if so *)
  oiter
    (fun input -> if EcCommands.check_eco input then exit 0)
    input;

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
  let lazy terminal = terminal in

  (* Initialize PRNG *)
  Random.self_init ();

  (* Connect to external Why3 server if requested *)
  prvopts.prvo_why3server |> oiter (fun server ->
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
              T.notice ~immediate:true lvl msg terminal
            in

            EcCommands.addnotifier notifier;
            oiter (fun ppwidth ->
              let gs = EcEnv.gstate (EcScope.env (EcCommands.current ())) in
              EcGState.setvalue "PP:width" (`Int ppwidth) gs)
              prvopts.prvo_ppwidth;
            first := `Loop

        | `Loop -> ()
        end;

        oiter (T.setwidth terminal)
          (let gs = EcEnv.gstate (EcScope.env (EcCommands.current ())) in
           match EcGState.getvalue "PP:width" gs with
           | Some (`Int i) -> Some i | _ -> None);    

        begin
          match snd_map EcLocation.unloc (T.next terminal) with
          | (src, EP.P_Prog (commands, locterm)) ->
              let src = String.strip src in
              (* TODO REMOVE Format.eprintf "@.@.[W]%s@.@." src; *)
              terminate := locterm;
              List.iter
                (fun p ->
                   let loc = p.EP.gl_action.EcLocation.pl_loc in
                   let timed = p.EP.gl_debug = Some `Timed in
                   let break = p.EP.gl_debug = Some `Break in
                     try
                       let tdelta =
                         EcCommands.process ~src ~timed ~break p.EP.gl_action
                       in tstats loc tdelta
                     with
                     | EcCommands.Restart ->
                         raise EcCommands.Restart
                     | e -> begin
                       if Printexc.backtrace_status () then begin
                         if not (T.interactive terminal) then
                           Printf.fprintf stderr "%t\n%!" Printexc.print_backtrace
                       end;
                       raise (EcScope.toperror_of_exn ~gloc:loc e)
                   end)
                commands

          | _, EP.P_DocComment doc ->
             EcCommands.doc_comment doc

          | _, EP.P_Undo i ->
              EcCommands.undo i
          | _, EP.P_Exit ->
              terminate := true
        end;
        
        T.finish `ST_Ok terminal;
        if !terminate then begin
            T.finalize terminal;
            if not eco then
              finalize_input input (EcCommands.current ());
            if gendoc then
              EcDoc.generate_html input (EcCommands.current ());
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
