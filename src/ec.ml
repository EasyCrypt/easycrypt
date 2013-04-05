(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions
open EcPrinting

(* -------------------------------------------------------------------- *)
module type InteractiveIO = sig
  val prompt  : EcIo.ecreader -> int -> unit
  val success : EcCommands.info list -> unit
  val error   : exn -> unit
end

(* -------------------------------------------------------------------- *)
module IntCommand : sig
  val prinfo : out_channel -> EcCommands.info -> unit
end = struct
  open EcScope
  open EcCommands
  open EcBaseLogic
  open EcLogic
  open EcPrinting
  open EcPrinting.Pp

  let goalline = String.make 72 '-'

  let prgoal (stream : out_channel) (n, (hyps, concl)) =
    let pr_hyp t (id, k) = 
      let dk = 
        match k with
        | LD_var (ty, _body) -> pr_type t ty (* FIXME body *)
        | LD_mem _           -> tk_memory
        | LD_modty p         -> pr_modtype t p
        | LD_hyp f           -> pr_form t f
      in

      let dh = Pp.join [pr_ident t id; !^":"; dk] in
        Printf.fprintf stream "%t\n%!"
          (fun stream -> Pp.pretty stream dh);
        PPE.add_local t id
    in
      begin
        match n with
        | 0 -> Printf.fprintf stream "Current goal\n%!"
        | _ -> Printf.fprintf stream "Current goal (remaining: %d)\n%!" n
      end;
      Printf.fprintf stream "Type variables: %t\n%!"
        (fun stream ->
          let doc = List.map (pr_tvar EcEnv.initial) hyps.h_tvar in (* FIXME *)
            Pp.pretty stream (Pp.seq ~sep:"," doc));
      let _ =
        List.fold_left pr_hyp EcEnv.initial (List.rev hyps.h_local) (* FIXME *)
      in
        Printf.fprintf stream "%s\n%!" goalline;
        Printf.fprintf stream "%t\n%!"
          (fun stream -> Pp.pretty stream (pr_form EcEnv.initial concl)) (* FIXME *)

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

    | GI_Goal goal ->
        let juc = goal.puc_jdg in

        try 
          let n = List.length (snd (find_all_goals juc)) in
          let g = get_goal (get_first_goal juc) in
            prgoal stream (n, g)
        with EcBaseLogic.NotAnOpenGoal _ -> 
          Printf.fprintf stream "No more goals\n%!"
end

(* -------------------------------------------------------------------- *)
module Emacs : InteractiveIO = struct
  let startpos = ref 0

  let prompt ecreader (uuid : int) =
    startpos := (EcIo.lexbuf ecreader).Lexing.lex_curr_p.Lexing.pos_cnum;
    Printf.printf "[%d]>\n%!" uuid

  let success (infos : EcCommands.info list) =
    List.iter (IntCommand.prinfo stdout) infos

  let error (e : exn) =
    let (loc, e) =
      match e with
      | EcCommands.TopError (loc, e) -> (loc, e)
      | _ -> (EcLocation._dummy, e)
    in
      Format.fprintf Format.err_formatter
        "[error-%d-%d]%s\n%!"
        (max 0 (loc.EcLocation.loc_bchar - !startpos))
        (max 0 (loc.EcLocation.loc_echar - !startpos))
        (EcPException.tostring e)
end

(* -------------------------------------------------------------------- *)
module CLI : InteractiveIO = struct
  let prompt (_ : EcIo.ecreader) (_ : int) =
    Printf.printf "> %!"

  let success (infos : EcCommands.info list) =
    List.iter (IntCommand.prinfo stdout) infos

  let error (e : exn) =
    EcPException.exn_printer Format.err_formatter e
end

(* -------------------------------------------------------------------- *)
let _ =
  options := EcOptions.parse ();

  (* Initialize why3 engine *)
  EcWhy3.initialize !options.o_why3;

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
      EcIo.drain iparser;
      IO.prompt iparser (EcCommands.uuid ());
      try
        match EcIo.parse iparser with
        | EcParsetree.P_Prog (commands, terminate) ->
            let infos =
              List.flatten (List.map EcCommands.process commands)
            in
            if terminate then exit 0;
            IO.success infos

        | EcParsetree.P_Undo i ->
          let info =  EcCommands.undo i in
          IO.success info
      with e ->
        IO.error (EcCommands.toperror_of_exn e);
        if not !EcOptions.options.o_emacs then
          exit 1
    done
