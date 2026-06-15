(* -------------------------------------------------------------------- *)
let parse (name : string) (input : IO.input) : Ptree.pprogram =
  let lexbuf = Lexing.from_channel input in
  Lexing.set_filename lexbuf name;
  Parser.program Lexer.main lexbuf
