(* -------------------------------------------------------------------- *)
open Lospecs


(* -------------------------------------------------------------------- *)
type options = {
  pp_pst : bool;
  pp_ast : bool;
  pp_bd  : bool;
  evalf  : bool;
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

    if options.evalf then begin
      let eval_fun  = "VSAT" in
      let eval_args = [
        (*(Evaluator.from_int_list [0x8000fffe; 0x13; 0xffff; 0x15; 0x21; 0x00; 0x1100; 0x0200] 32); *)
        (Evaluator.from_int_list [0x7000f000] 32)] in
      Evaluator.eval_adef (List.find (fun x -> (compare (fst x) eval_fun) == 0) ast |> snd) eval_args
      |> (fun (bw, bn) -> Format.eprintf "vaL: %s@.size: %d" (Z.format ("%" ^ (string_of_int (bn/16 + 1)) ^ "x") bw) bn)
    end;

    if options.pp_ast then begin
      List.iter (fun (name, def) ->
        Format.eprintf "%s:@.%a@."
        name
          (Yojson.Safe.pretty_print ~std:true)
          (Ast.adef_to_yojson def)
      ) ast
    end;

    if options.pp_bd then begin
      List.iter (fun (name, def) ->
        Format.eprintf "%s:@.%a@."
        name
        Deps.pp_deps
        (Bitdep.bd_adef def) 
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
    let mk (pp_pst : bool) (pp_ast : bool) (pp_bd : bool) (evalf : bool) (input : string) =
      entry { pp_pst; pp_ast; pp_bd; evalf; input; }
    in

    let print_pst =
      let doc = "Print the parse tree" in
      Arg.(value & flag & info ["print-pst"] ~doc) in

    let print_ast =
      let doc = "Print the abstract syntax tree" in
      Arg.(value & flag & info ["print-ast"] ~doc) in

    let print_bd =
      let doc = "Print the bit level dependency" in
      Arg.(value & flag & info ["print-bd"] ~doc) in

    let evalf =
      let doc = "Evaluate hard coded function with arguments" in
      Arg.(value & flag & info ["eval"] ~doc) in

    let input =
      let doc = "The specification file" in
      Arg.(required & pos 0 (some string) None & info [] ~docv:"SPEC" ~doc) in

    let info = Cmd.info "lospec" in
    Cmd.v info Term.(const mk $ print_pst $ print_ast $ print_bd $ evalf $ input)
  in

  exit (Cmd.eval cmd)

(* -------------------------------------------------------------------- *)
let () = main ()
