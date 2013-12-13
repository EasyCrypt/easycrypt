(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions

module T = EcTerminal

(* -------------------------------------------------------------------- *)
let _ =
  let myname  = Filename.basename Sys.executable_name
  and mydir   = Filename.dirname  Sys.executable_name in
  let eclocal = List.mem myname ["ec.native"; "ec.byte"] in

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
    let wrapper = resource ["system"; bin "callprover"] in
      if   Sys.file_exists wrapper
      then Some wrapper
      else None
  in

  (* Parse command line arguments *)
  let options = EcOptions.parse Sys.argv in

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
  let ldropts = options.o_options.o_loader in

  begin
    let theories = resource ["theories"] in
      EcCommands.addidir ~system:true (Filename.concat theories "prelude");
      EcCommands.addidir ~system:true (Filename.concat theories "core");
      if not ldropts.ldro_boot then
        EcCommands.addidir ~system:true theories
  end;

  (* Initialize I/O + interaction module *)
  let (prvopts, input, terminal) =
    match options.o_command with
    | `Config -> begin
        Format.eprintf "load-path:@\n%!";
        List.iter
          (fun (sys, dir) ->
             Format.eprintf "  <%.6s>@@%s@\n%!" (if sys then "system" else "user") dir)
          (EcCommands.loadpath ());
        Format.eprintf "why3 configuration file@\n%!";
        begin match why3conf with
        | None   -> Format.eprintf "  <why3 default>@\n%!"
        | Some f -> Format.eprintf "  %s@\n%!" f end;
        Format.eprintf "prover wrapper@\n%!";
        begin match pwrapper with
        | None -> Format.eprintf "  <none>@\n%!"
        | Some wrapper -> Format.eprintf "  %s@\n%!" wrapper end;
        Format.eprintf "known provers: %s@\n%!"
          (String.concat ", " (EcProvers.known_provers ()));
        exit 0
    end
  
    | `Cli cliopts -> begin
        let terminal =
          match cliopts.clio_emacs with
          | true  -> lazy (EcTerminal.from_emacs ())
          | false -> lazy (EcTerminal.from_tty ())
        in
          (cliopts.clio_provers, None, terminal)
    end

    | `Compile cmpopts -> begin
        let input = cmpopts.cmpo_input in
        let terminal = lazy (EcTerminal.from_channel ~name:input (open_in input)) in
          (cmpopts.cmpo_provers, Some input, terminal)
    end
  in

  (* Initialize global scope *)
  EcCommands.initialize ~boot:ldropts.ldro_boot  ~wrapper:pwrapper;

  (* Initialize loader *)
  begin
    List.iter EcCommands.addidir ldropts.ldro_idirs;
    match input with
    | None -> EcCommands.addidir Filename.current_dir_name
    | Some input -> EcCommands.addidir (Filename.dirname input)
  end;

  (* Initialize the proof mode *)
  EcCommands.full_check
    prvopts.pvro_checkall
    prvopts.prvo_maxjobs
    prvopts.prvo_provers;

  if prvopts.pvro_weakchk then
    EcCommands.pragma_check false;

  (* Instantiate terminal *)
  let lazy terminal = terminal in

  (* Initialize PRNG *)
  Random.self_init ();

  try
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
