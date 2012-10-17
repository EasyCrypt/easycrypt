
open Why3
open Format



(* produce a realization of a theory *)

let do_theory _env drv _path thname th =
  let oldf = thname ^ ".v" in
  let old =
    if Sys.file_exists oldf
    then
      begin
        let backup = oldf ^ ".bak" in
        Sys.rename oldf backup;
        Some(open_in backup)
      end
    else None
  in
  eprintf "Realizing theory '%s' in file '%s'.@." thname oldf;
  let ch = open_out oldf in
  let fmt = formatter_of_out_channel ch in
  Driver.print_theory ?old drv fmt th;
  fprintf fmt "@.";
  close_out ch

let rdot = (Str.regexp "\\.")

let do_global_theory env drv t =
  let l = Str.split rdot t in
  let p, t = match List.rev l with
    | [] -> assert false
    | [_] ->
        eprintf "Theory name must be qualified.@.";
        exit 1
    | t::p -> List.rev p, t
  in
  let th = try Env.find_theory env p t with Env.TheoryNotFound _ ->
    eprintf "Theory '%s' not found.@." t;
    exit 1
  in
  do_theory env drv p t th

(* command-line options *)

let usage_msg = sprintf
  "Usage: %s [options] <theory>"
  (Filename.basename Sys.argv.(0))

let opt_loadpath = ref []

let add_loadpath s = opt_loadpath := s :: !opt_loadpath

let opt_theory = ref None

let add_opt_theory t =
  match !opt_theory with
    | None -> opt_theory := Some t
    | Some _ -> eprintf "%s@." usage_msg; exit 2

let option_list = Arg.align [
  "-L", Arg.String add_loadpath,
      "<dir> Add <dir> to the library search path";
  "--library", Arg.String add_loadpath,
      " same as -L";
  "-I", Arg.String add_loadpath,
      " same as -L (obsolete)";
  ]

(* parsing command-line options *)
let () =
  try
    Arg.parse option_list add_opt_theory usage_msg
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(* main program *)
let () =
  match !opt_theory with
    | None -> eprintf "%s@." usage_msg; exit 2
    | Some th ->
        try
          let config = Whyconf.read_config None in
          let main = Whyconf.get_main config in
          let env =
            Env.create_env (!opt_loadpath @ Whyconf.loadpath main)
          in
          let coq =
            try Util.Mstr.find "coq-realize" (Whyconf.get_provers config)
            with Not_found ->
              eprintf "Driver for coq-realize prover not found@.";
              exit 2
          in
          let drv = Driver.load_driver env coq.Whyconf.driver in
          do_global_theory env drv th
        with e when not (Debug.test_flag Debug.stack_trace) ->
          eprintf "%a@." Exn_printer.exn_printer e;
          exit 1




