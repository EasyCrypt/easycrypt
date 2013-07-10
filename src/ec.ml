(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions
open EcPrinting

module T = EcTerminal

(* -------------------------------------------------------------------- *)
let _ =
  let myname = Filename.basename Sys.executable_name
  and mydir  = Filename.dirname  Sys.executable_name in
  let locali = ["ec.native"; "ec.byte"] in

  options := EcOptions.parse ();

  (* Initialize why3 engine *)
  let why3conf =
    match !options.o_why3 with
    | None when List.mem myname locali -> begin
      let why3conf =
        List.fold_left Filename.concat mydir
          [Filename.parent_dir_name;
           Filename.parent_dir_name;
           "_tools"; "why3.local.conf"]
      in
        match Sys.file_exists why3conf with
        | false -> None
        | true  -> Some why3conf
    end
    | why3conf -> why3conf
  in

  begin
    try  EcProvers.initialize why3conf
    with e ->
      Format.eprintf
      "cannot initialize Why3 engine: %a@."
      EcPException.exn_printer e;
      exit 1
  end;

  (* Initialize load path *)
  begin
    let theories =
        match myname with
        | _ when List.mem myname locali -> begin
            if Filename.basename (Filename.dirname mydir) = "_build" then
              List.fold_left Filename.concat mydir
                [Filename.parent_dir_name;
                 Filename.parent_dir_name;
                 "theories"]
            else
              Filename.concat mydir "theories"
          end

        | _ ->
            List.fold_left Filename.concat mydir
              [Filename.parent_dir_name; "lib"; "easycrypt"; "theories"]
    in
      EcCommands.addidir ~system:true (Filename.concat theories "prelude");
      EcCommands.addidir ~system:true theories
  end;

  List.iter EcCommands.addidir !options.o_idirs;
  oiter !options.o_input
    (fun input ->
      EcCommands.addidir (Filename.dirname input));
  if !options.o_emacs then
    EcCommands.addidir Filename.current_dir_name;

  (* Force loading of prelude here *)
  ignore (EcCommands.current () : EcScope.scope);

  (* Initialize the proof mode *)
  EcCommands.full_check !options.o_full_check !options.o_max_prover !options.o_provers;

  (* Print configuration is wanted *)
  if !options.o_pconfig then begin
    Format.eprintf "load-path:@\n%!";
    List.iter
      (fun (sys, dir) ->
         Format.eprintf "  <%.6s>@@%s@\n%!" (if sys then "system" else "user") dir)
      (EcCommands.loadpath ());
    Format.eprintf "why3 configuration file@\n%!";
    begin match why3conf with
    | None   -> Format.eprintf "  <why3 default>@\n%!"
    | Some f -> Format.eprintf "  %s@\n%!" f end;
    Format.eprintf "known provers: %s@\n%!"
      (String.concat ", " (EcProvers.known_provers ()));
    exit 0
  end;

  (* Initialize I/O + interaction module *)
  let terminal =
    match !options.o_emacs, !options.o_input with
    | true , None -> EcTerminal.from_emacs ()
    | false, None -> EcTerminal.from_tty   ()

    | _, Some input ->
        EcTerminal.from_channel ~name:input (open_in input)
  in

  (* Set notifier (TODO: fix this global stuff *)
  EcCommands.set_notifier
    (fun msg -> EcTerminal.notice ~immediate:true msg terminal);

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
      if !terminate then exit 0

    with e -> begin
      EcTerminal.finish
        (`ST_Failure (EcCommands.toperror_of_exn e))
        terminal;
      if not (EcTerminal.interactive terminal) then
        exit 1
    end
  done
