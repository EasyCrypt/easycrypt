(* -------------------------------------------------------------------- *)
open Lospecs

(* -------------------------------------------------------------------- *)
type options = {
  pp_pst : bool;
  pp_ast : bool;
  input : string;
}

(* -------------------------------------------------------------------- *)
let entry (options : options) =
  let prog = File.with_file_in options.input Io.parse in

  if options.pp_pst then begin
    Format.eprintf "%a@."
      (Yojson.Safe.pretty_print ~std:true)
      (Ptree.pprogram_to_yojson prog)
  end;

  let ast = Typing.tt_program Typing.Env.empty prog in

  if options.pp_ast then begin
    List.iter (fun (_, def) ->
      Format.eprintf "%a@."
        (Yojson.Safe.pretty_print ~std:true)
        (Typing.adef_to_yojson def)
    ) ast
  end;

  let _dep = List.map Bitdep.bd_adef (List.map snd ast) in

  ()

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
      Arg.(value & pos 0 string "" & info [] ~docv:"SPEC" ~doc) in

    let info = Cmd.info "lospec" in
    Cmd.v info Term.(const mk $ print_pst $ print_ast $ input)
  in

  exit (Cmd.eval cmd)

(* -------------------------------------------------------------------- *)
let () = main ()
