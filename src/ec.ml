(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions
open EcPrinting

module T = EcTerminal

(* -------------------------------------------------------------------- *)
let _ =
  options := EcOptions.parse ();

  (* Initialize why3 engine *)
  EcProvers.initialize !options.o_why3;

  (* Initialize the proof mode *)
  EcCommands.full_check !options.o_full_check !options.o_max_prover !options.o_provers;

  (* Initialize load path *)
  begin
    let theories =
      let myname = Filename.basename Sys.executable_name
      and mydir  = Filename.dirname  Sys.executable_name in
        match myname with
        | "ec.native" | "ec.byte" -> begin
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
      EcCommands.addidir theories
  end;

  oiter !options.o_input
    (fun input ->
      EcCommands.addidir (Filename.dirname input));
  List.iter EcCommands.addidir !options.o_idirs;

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
        match EcTerminal.next terminal with
        | EcParsetree.P_Prog (commands, locterm) ->
            terminate := locterm;
            ignore (List.map EcCommands.process commands);

        | EcParsetree.P_Undo i ->
            ignore (EcCommands.undo i)
      end;
      EcTerminal.finish `ST_Ok terminal;
      if !terminate then exit 0

    with e -> begin
      if not (EcTerminal.interactive terminal) then begin
        Printexc.print_backtrace stderr;
        Printf.fprintf stderr "\n%!";
      end;
      EcTerminal.finish
        (`ST_Failure (EcCommands.toperror_of_exn e))
        terminal;
      if not (EcTerminal.interactive terminal) then
        exit 1
    end
  done
