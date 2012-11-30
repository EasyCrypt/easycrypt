(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
let lexer = fun lexbuf ->
  let token = EcLexer.main lexbuf in
    (token, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)

(* -------------------------------------------------------------------- *)
let lexbuf_from_channel = fun name channel ->
  let lexbuf = Lexing.from_channel channel in
    lexbuf.Lexing.lex_curr_p <- {
        Lexing.pos_fname = name;
        Lexing.pos_lnum  = 1;
        Lexing.pos_bol   = 0;
        Lexing.pos_cnum  = 0
      };
    lexbuf

(* -------------------------------------------------------------------- *)
let parserfun = fun () ->
    MenhirLib.Convert.Simplified.traditional2revised EcParser.prog

type parser_t =
  (EcParser.token * Lexing.position * Lexing.position, EcParsetree.prog * bool)
    MenhirLib.Convert.revised

(* -------------------------------------------------------------------- *)
type ecreader_r = {
  ecr_lexbuf   : Lexing.lexbuf;
  ecr_parser   : parser_t;
}

type ecreader = ecreader_r Disposable.t

(* -------------------------------------------------------------------- *)
let from_channel ~name channel =
  let lexbuf = lexbuf_from_channel name channel in

    Disposable.create
      { ecr_lexbuf = lexbuf;
        ecr_parser = parserfun (); }

(* -------------------------------------------------------------------- *)
let from_file filename =
  let channel = open_in filename in
    try
      let lexbuf = lexbuf_from_channel filename channel in

        Disposable.create ~cb:(fun _ -> close_in channel)
          { ecr_lexbuf = lexbuf;
            ecr_parser = parserfun (); }

    with
      | e ->
          (try close_in channel with _ -> ());
          raise e

(* -------------------------------------------------------------------- *)
let from_string data =
  let lexbuf = Lexing.from_string data in

    Disposable.create
      { ecr_lexbuf = lexbuf;
        ecr_parser = parserfun (); }

(* -------------------------------------------------------------------- *)
let finalize (ecreader : ecreader) =
  Disposable.dispose ecreader

(* -------------------------------------------------------------------- *)
let parse (ecreader : ecreader) =
  let ecreader = Disposable.get ecreader in
    ecreader.ecr_parser (fun () -> lexer ecreader.ecr_lexbuf)
  
