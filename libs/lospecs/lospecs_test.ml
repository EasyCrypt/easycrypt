(* -------------------------------------------------------------------- *)
open Lospecs


(* -------------------------------------------------------------------- *)
type options = {
  pp_pst : bool;
  pp_ast : bool;
  input  : string;
}

(* -------------------------------------------------------------------- *)
let entry (options : options) =
  try
    let prog = File.with_file_in options.input (Io.parse options.input) in

    if options.pp_pst then begin
      Format.eprintf "%a@."
        (Yojson.Safe.pretty_print ~std:true)
        (Ptree.pprogram_to_yojson prog)
    end;
  
    let ast = Typing.tt_program Typing.Env.empty prog in

    if options.pp_ast then begin
      List.iter (fun (name, def) ->
        Format.eprintf "%s:@.%a@."
        name
          (Yojson.Safe.pretty_print ~std:true)
          (Ast.adef_to_yojson def)
      ) ast
    end;

    (* let _dep = List.map Bitdep.bd_adef (List.map snd ast) in *)

    ()

  with
  | Typing.TypingError (range, msg) ->
      Format.eprintf "%a: %s@." Ptree.Lc.pp_range range msg;
      Format.eprintf "@.";
      Io.print_source_for_range Format.err_formatter range options.input;
      exit 1
  | Ptree.ParseError range ->
      Format.eprintf "%a: %s@." Ptree.Lc.pp_range range "parse error";
      Format.eprintf "@.";
      Io.print_source_for_range Format.err_formatter range options.input;
      exit 1
  | Not_found ->
      Format.eprintf "Something is missing"

(* -------------------------------------------------------------------- *)
let main () : unit =
  let open Cmdliner in

  let cmd =
    let mk (pp_pst : bool) (pp_ast : bool) (input : string) =
      entry { pp_pst; pp_ast; input; }
    in

    let print_pst =
      let doc = "Print the parse tree" in
      Arg.(value & flag & info ["print-pst"] ~doc) in

    let print_ast =
      let doc = "Print the abstract syntax tree" in
      Arg.(value & flag & info ["print-ast"] ~doc) in

    let input =
      let doc = "The specification file" in
      Arg.(required & pos 0 (some string) None & info [] ~docv:"SPEC" ~doc) in

    let info = Cmd.info "lospec" in
    Cmd.v info Term.(const mk $ print_pst $ print_ast $ input)
  in

  exit (Cmd.eval cmd)

(* -------------------------------------------------------------------- *)
let () = main ()
