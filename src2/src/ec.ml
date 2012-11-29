(* -------------------------------------------------------------------- *)
open Options

(* -------------------------------------------------------------------- *)
let _ =
  let options = Options.parse () in
  let iparser =
    match options.o_input with
    | None   -> Io.from_channel ~name:"<stdin>" stdin
    | Some f -> Io.from_file f
  in
    while true do
      match Io.parse iparser with
        | prog, false -> List.iter Commands.process prog
        | _   , true  -> exit 0
    done
