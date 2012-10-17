(** Program entry point : parse command line and call whatever is needed to
    * process them. *)

open Ec

let cmd_name = ref ""
let init_files = ref [ "src/easycrypt_base.ec" ]
let files = ref [] 
let top_parse = ref false
let top_caml = ref false
let emacs_parse = ref false
let ep_output = ref false

let spec_args = [
  ("-top", Arg.Set top_parse, " Start in parsing mode");
  ("-caml", Arg.Set top_caml, " Start in ocaml toplevel mode");
  ("-emacs", Arg.Set emacs_parse, " Start in emacs parsing mode");
  ("-ep", Arg.Set ep_output,  " Extract 'filename.ep' to generate latex");
  ("-prover", Arg.String (fun s -> Api.set_prover [s]), " Set the default automated prover (alt-ergo, simplify, z3, yices, cvc3, ...)");
  ("-debug", Arg.Int Api.set_debug, " Set debug verbosity level (default is 1)");
  ("-quiet", Arg.Unit (fun _ -> Api.set_debug 0), " Do not print any messages (equivalent to -debug 0)");
  ("-nocheck", Arg.Unit Api.withproof, " Do not try to check proofs");
  ("-prelude", Arg.String (fun s -> init_files := [ s ]), " Specify a prelude file");
]

let top_mode () = !top_parse || !top_caml

let usage_msg () =
  "Usage : "^(!cmd_name)^" [options] file\n"

let parse_args () =
  cmd_name := Sys.argv.(0);
  let memo_arg arg = files := arg :: !files in
  Arg.parse spec_args memo_arg (usage_msg ())


let welcome () =
  Format.printf "\t Welcome to EasyCrypt OCaml toplevel @.";
  Format.printf "\t Use help();; for information on available commands@.@."

let parse_init_files () = match !init_files with
  | [] -> ()
  | lf -> Api.parse_files lf

let parse_files () = match (List.rev !files) with
  | [] ->
    if not (top_mode () || !emacs_parse) then
      Format.printf "[WARNING] No source file given\n"
  | lf -> Api.parse_files lf


let execute () =
  parse_init_files ();
  Api.save_init_state ();
  parse_files ();
  if top_mode () then 
    begin
    Format.printf "@.\t Welcome to EasyCrypt ! @.";
    if !top_parse then Api.parse ();
    welcome ()
    end
  else
    if !emacs_parse then
      Api.emacs_parse ()


let main () =
  parse_args ();
  if !ep_output then
    Api.parse_file_ep (List.hd !files)
  else 
    execute ();
  exit 0



let _ = main ()

