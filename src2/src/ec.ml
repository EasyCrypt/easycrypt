(* -------------------------------------------------------------------- *)
open EcOptions
open EcPrinting

(* -------------------------------------------------------------------- *)
let _ =
  let options = EcOptions.parse () in
  let iparser =
    match options.o_input with
    | None   -> EcIo.from_channel ~name:"<stdin>" stdin
    | Some f -> EcIo.from_file f
  in
    while true do
      match EcIo.parse iparser with
        | prog, false -> List.iter EcCommands.process prog
        | _   , true  -> exit 0
    done
