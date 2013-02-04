(* -------------------------------------------------------------------- *)
open EcUtils
open EcOptions
open EcPrinting

(* -------------------------------------------------------------------- *)
let _ = 
  EcPexception.set_default Why3.Exn_printer.exn_printer 

(* -------------------------------------------------------------------- *)
module Emacs : sig
  val prompt  : int -> unit
  val success : EcCommands.info list -> unit
  val error   : exn -> unit
end = struct
  let prompt (uuid : int) =
    Printf.printf "[%d]>\n%!" uuid

  let success (_ : EcCommands.info list) =
    ()

  let error (e : exn) =
    match e with
    | EcTypedtree.TyError (loc, exn) ->
        EcFormat.pp_err
          (EcPrinting.pp_located loc EcPexception.pp_typerror)
          exn;

    | e ->
      EcFormat.pp_err EcPexception.exn_printer e;
end

let if_emacs (doit : unit -> unit) =
  if !options.o_emacs then doit ()

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
      if_emacs (fun () -> Emacs.prompt (EcCommands.uuid ()));
      try
        match EcIo.parse iparser with
        | EcParsetree.P_Prog (commands, terminate) ->
            let infos =
              List.flatten (List.map EcCommands.process commands)
            in
              if terminate then exit 0;
              if_emacs (fun () -> Emacs.success infos)

        | EcParsetree.P_Undo i ->
            EcCommands.undo i
      with e ->
        if_emacs (fun () -> Emacs.error e)
    done

(*
(* -------------------------------------------------------------------- *)
exception Interrupted

let out_added scope p = 
  let doc = process_pr scope p in
  EcPrinting.pretty (!^"add " ^^ doc ^^ Pprint.hardline)

let print_next scope = 
  EcPrinting.pretty (EcScope.Tactic.out_goal scope);
  EcPrinting.pretty (Pprint.empty ^/^ !^">") 


(* -------------------------------------------------------------------- *)
let process (g : global) =
  try
    process g
  with
*)

(*
    out_added scope (Pr_ty (dummy_pqs_of_ps tyd.pty_name));

  out_added scope (Pr_op (dummy_pqs_of_ps op.po_name));

  out_added scope (Pr_pr (dummy_pqs_of_ps p.pp_name));

  out_added scope (Pr_ax (dummy_pqs_of_ps (dummyloc name)));



    oiter name
      (fun name -> 
  begin match name with
  | None -> ()
  | Some name -> out_added scope (Pr_ax (dummy_pqs_of_ps (dummyloc name)))
  end;
  scope

*)
