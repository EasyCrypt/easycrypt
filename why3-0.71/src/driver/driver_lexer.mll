(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

{
  open Format
  open Lexing
  open Driver_parser
  open Lexer

  exception IllegalCharacter of char

  let () = Exn_printer.register (fun fmt e -> match e with
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | _ -> raise e)

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "theory", THEORY;
        "end", END;
        "syntax", SYNTAX;
        "remove", REMOVE;
        "meta", META;
        "cloned", CLONED;
        "prelude", PRELUDE;
        "printer", PRINTER;
        "valid", VALID;
        "invalid", INVALID;
        "timeout", TIMEOUT;
        "time",    TIME;
        "unknown", UNKNOWN;
        "fail", FAIL;
        "function", FUNCTION;
        "predicate", PREDICATE;
        "type", TYPE;
        "prop", PROP;
        "filename", FILENAME;
        "transformation", TRANSFORM;
        "plugin", PLUGIN
      ]

}

let space = [' ' '\t' '\r']
let alpha = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let ident = alpha (alpha | digit | '\'')*

let op_char = ['=' '<' '>' '~' '+' '-' '*' '/' '%'
               '!' '$' '&' '?' '@' '^' '.' ':' '|' '#']

rule token = parse
  | '\n'
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { comment lexbuf; token lexbuf }
  | '_'
      { UNDERSCORE }
  | ident as id
      { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | digit+ as i
      { INTEGER (int_of_string i) }
  | "<-"
      { LARROW }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "."
      { DOT }
  | ","
      { COMMA }
  | op_char+ as op
      { OPERATOR op }
  | "\""
      { STRING (string lexbuf) }
  | "import" space*  "\""
      { INPUT (string lexbuf) }
  | eof
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }

{
  let loc lb = Loc.extract (lexeme_start_p lb, lexeme_end_p lb)

  let with_location f lb =
    try f lb with e -> raise (Loc.Located (loc lb, e))

  let parse_file input_lexbuf lexbuf =
    let s = Stack.create () in
    Stack.push lexbuf s;
    let rec multifile lex_dumb =
      let lexbuf = Stack.top s in
      let tok = token lexbuf in
      Loc.transfer_loc lexbuf lex_dumb;
      match tok with
        | INPUT filename ->
          Stack.push (input_lexbuf filename) s;
          multifile lex_dumb
        | EOF -> ignore (Stack.pop s);
          if Stack.is_empty s then EOF else multifile lex_dumb
        | _ -> tok in
    let lex_dumb = Lexing.from_function (fun _ _ -> assert false) in
    Loc.transfer_loc lexbuf lex_dumb;
    with_location (Driver_parser.file multifile) lex_dumb
}
