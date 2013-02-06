(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions
open EcPrinting

(* -------------------------------------------------------------------- *)
let _ = 
  EcPexception.set_default Why3.Exn_printer.exn_printer 

(* -------------------------------------------------------------------- *)
module type InteractiveIO = sig
  val prompt  : int -> unit
  val success : EcCommands.info list -> unit
  val error   : exn -> unit
end

(* -------------------------------------------------------------------- *)
module IntCommand : sig
  val prinfo : out_channel -> EcCommands.info -> unit
end = struct
  open EcCommands

  let prinfo (stream : out_channel) (info : EcCommands.info) =
    match info with
    | GI_AddedType name ->
        Printf.fprintf stream "added type %s.\n%!" name

    | GI_AddedAxiom name ->
        Printf.fprintf stream "added axiom %s.\n%!" name

    | GI_AddedOperator name ->
        Printf.fprintf stream "added operator %s.\n%!" name

    | GI_AddedPredicate name ->
        Printf.fprintf stream "added predicated %s.\n%!" name
end

(* -------------------------------------------------------------------- *)
module Emacs : InteractiveIO = struct
  let prompt (uuid : int) =
    Printf.printf "[%d]>\n%!" uuid

  let success (infos : EcCommands.info list) =
    List.iter (IntCommand.prinfo stdout) infos

  let error (e : exn) =
    match e with
    | EcTypedtree.TyError (loc, exn) ->
        EcFormat.pp_err
          (EcPrinting.pp_located loc EcPexception.pp_typerror)
          exn;

    | e ->
      EcFormat.pp_err EcPexception.exn_printer e;
end

(* -------------------------------------------------------------------- *)
module CLI : InteractiveIO = struct
  let prompt (_ : int) =
    Printf.printf "> %!"

  let success (infos : EcCommands.info list) =
    List.iter (IntCommand.prinfo stdout) infos

  let error (e : exn) =
    match e with
    | EcTypedtree.TyError (loc, exn) ->
        EcFormat.pp_err
          (EcPrinting.pp_located loc EcPexception.pp_typerror)
          exn;

    | e ->
        EcFormat.pp_err EcPexception.exn_printer e;
end

(* -------------------------------------------------------------------- *)
let _ =
  options := EcOptions.parse ();

  (* Initialize why3 engine *)
  EcWhy3.initialize !options.o_why3;

  (* Initialize load path *)
  begin
    let theories =
      let myname = Filename.basename Sys.executable_name
      and mydir  = Filename.dirname  Sys.executable_name in
        match myname with
        | "ec.native"
        | "ec.byte" ->
            Filename.concat mydir "theories"

        | _ ->
            List.fold_left
              Filename.concat mydir
              [Filename.parent_dir_name; "lib"; "easycrypt"; "theories"]
    in
      EcCommands.addidir theories
  end;

  oiter !options.o_input
    (fun input ->
      EcCommands.addidir (Filename.dirname input));
  List.iter EcCommands.addidir !options.o_idirs;

  (* Initialize I/O UI interaction module *)
  let io =
    match !options.o_emacs with
    | false -> (module CLI   : InteractiveIO)
    | true  -> (module Emacs : InteractiveIO)
  in

  let module IO = (val io : InteractiveIO) in

  (* Interaction loop *)
  let iparser =
    match !EcOptions.options.o_input with
    | None   -> EcIo.from_channel ~name:"<stdin>" stdin
    | Some f -> EcIo.from_file f
  in
    while true do
      IO.prompt (EcCommands.uuid ());
      try
        match EcIo.parse iparser with
        | EcParsetree.P_Prog (commands, terminate) ->
            let infos =
              List.flatten (List.map EcCommands.process commands)
            in
              if terminate then exit 0;
              IO.success infos

        | EcParsetree.P_Undo i ->
            EcCommands.undo i
      with e ->
        IO.error e;
        if not !EcOptions.options.o_emacs then
          exit 1
    done
