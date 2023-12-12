(* -------------------------------------------------------------------- *)
let parse (input : IO.input) : Ptree.pprogram =
  Parser.program Lexer.main (Lexing.from_channel input)
