(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions
open EcPrinting

(* -------------------------------------------------------------------- *)
let _ = 
  EcPexception.set_default Why3.Exn_printer.exn_printer 

(* -------------------------------------------------------------------- *)
let _ =
  options := EcOptions.parse ();

  oiter !options.o_input
    (fun input ->
      EcCommands.addidir (Filename.dirname input));
  List.iter EcCommands.addidir !options.o_idirs;

  let iparser =
    match !EcOptions.options.o_input with
    | None   -> EcIo.from_channel ~name:"<stdin>" stdin
    | Some f -> EcIo.from_file f
  in
    while true do
      let commands, terminate = EcIo.parse iparser in
        List.iter EcCommands.process commands;
        if terminate then exit 0;
    done
