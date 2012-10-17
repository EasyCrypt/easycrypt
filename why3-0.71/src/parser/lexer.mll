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
  open Term
  open Ptree
  open Parser

  (* lexical errors *)

  exception IllegalCharacter of char
  exception UnterminatedComment
  exception UnterminatedString
  exception AmbiguousPath of string * string

  let () = Exn_printer.register (fun fmt e -> match e with
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | UnterminatedComment -> fprintf fmt "unterminated comment"
    | UnterminatedString -> fprintf fmt "unterminated string"
    | AmbiguousPath (f1, f2) ->
        fprintf fmt "ambiguous path:@ both `%s'@ and `%s'@ match" f1 f2
    | _ -> raise e)

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      [
        "as", AS;
        "axiom", AXIOM;
        "clone", CLONE;
        "else", ELSE;
        "end", END;
        "epsilon", EPSILON;
        "exists", EXISTS;
        "export", EXPORT;
        "false", FALSE;
        "forall", FORALL;
        "function", FUNCTION;
        "goal", GOAL;
        "if", IF;
        "import", IMPORT;
        "in", IN;
        "inductive", INDUCTIVE;
        "lemma", LEMMA;
        "let", LET;
        "match", MATCH;
        "meta", META;
        "namespace", NAMESPACE;
        "not", NOT;
        "predicate", PREDICATE;
        "prop", PROP;
        "then", THEN;
        "theory", THEORY;
        "true", TRUE;
        "type", TYPE;
        "use", USE;
        "with", WITH;
        (* programs *)
        "abstract", ABSTRACT;
        "absurd", ABSURD;
        "any", ANY;
        "assert", ASSERT;
        "assume", ASSUME;
        "begin", BEGIN;
        "check", CHECK;
        "do", DO;
        "done", DONE;
        "downto", DOWNTO;
        "exception", EXCEPTION;
        "for", FOR;
        "fun", FUN;
        (* "ghost", GHOST; *)
        "invariant", INVARIANT;
        "loop", LOOP;
        "model", MODEL;
        "module", MODULE;
        "mutable", MUTABLE;
        "raise", RAISE;
        "raises", RAISES;
        "reads", READS;
        "rec", REC;
        "to", TO;
        "try", TRY;
        "val", VAL;
        "variant", VARIANT;
        "while", WHILE;
        "writes", WRITES;
      ]

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let string_start_loc = ref Loc.dummy_position
  let string_buf = Buffer.create 1024

  let comment_start_loc = ref Loc.dummy_position

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c

  let update_loc lexbuf file line chars =
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with None -> pos.pos_fname | Some s -> s in
    lexbuf.lex_curr_p <-
      { pos with
          pos_fname = new_file;
          pos_lnum = int_of_string line;
          pos_bol = pos.pos_cnum - int_of_string chars;
      }

  let remove_leading_plus s =
    let n = String.length s in
    if n > 0 && s.[0] = '+' then String.sub s 1 (n-1) else s

  let loc lb = Loc.extract (lexeme_start_p lb, lexeme_end_p lb)

  let remove_underscores s =
    if String.contains s '_' then begin
      let count =
        let nb = ref 0 in
        String.iter (fun c -> if c = '_' then incr nb) s;
        !nb in
      let t = String.create (String.length s - count) in
      let i = ref 0 in
      String.iter (fun c -> if c <> '_' then (t.[!i] <-c; incr i)) s;
      t
    end else s
}

let newline = '\n'
let space = [' ' '\t' '\r']
let lalpha = ['a'-'z' '_']
let ualpha = ['A'-'Z']
let alpha = lalpha | ualpha
let digit = ['0'-'9']
let lident = lalpha (alpha | digit | '\'')*
let uident = ualpha (alpha | digit | '\'')*
let hexadigit = ['0'-'9' 'a'-'f' 'A'-'F']

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

let op_char_pref = ['!' '?']

rule token = parse
  | "##" space* ("\"" ([^ '\010' '\013' '"' ]* as file) "\"")?
    space* (digit+ as line) space* (digit+ as char) space* "##"
      { update_loc lexbuf file line char; token lexbuf }
  | "#" space* "\"" ([^ '\010' '\013' '"' ]* as file) "\""
    space* (digit+ as line) space* (digit+ as bchar) space*
    (digit+ as echar) space* "#"
      { POSITION (Loc.user_position file (int_of_string line)
                 (int_of_string bchar) (int_of_string echar)) }
  | newline
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | '_'
      { UNDERSCORE }
  | lident as id
      { try Hashtbl.find keywords id with Not_found -> LIDENT id }
  | uident as id
      { UIDENT id }
  | ['0'-'9'] ['0'-'9' '_']* as s
      { INTEGER (IConstDecimal (remove_underscores s)) }
  | '0' ['x' 'X'] (['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']* as s)
      { INTEGER (IConstHexa (remove_underscores s)) }
  | '0' ['o' 'O'] (['0'-'7'] ['0'-'7' '_']* as s)
      { INTEGER (IConstOctal (remove_underscores s)) }
  | '0' ['b' 'B'] (['0'-'1'] ['0'-'1' '_']* as s)
      { INTEGER (IConstBinary (remove_underscores s)) }
  | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? digit+ as e)
  | (digit+ as i) '.' (digit* as f) (['e' 'E'] (['-' '+']? digit+ as e))?
  | (digit* as i) '.' (digit+ as f) (['e' 'E'] (['-' '+']? digit+ as e))?
      { FLOAT (RConstDecimal (i, f, Util.option_map remove_leading_plus e)) }
  | '0' ['x' 'X'] ((hexadigit* as i) '.' (hexadigit+ as f)
                  |(hexadigit+ as i) '.' (hexadigit* as f)
                  |(hexadigit+ as i) ("" as f))
    ['p' 'P'] (['-' '+']? digit+ as e)
      { FLOAT (RConstHexa (i, f, remove_leading_plus e)) }
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { comment_start_loc := loc lexbuf; comment lexbuf; token lexbuf }
  | "'"
      { QUOTE }
  | ","
      { COMMA }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "{"
      { LEFTBRC }
  | "}"
      { RIGHTBRC }
  | "{|"
      { LEFTREC }
  | "|}"
      { RIGHTREC }
  | ":"
      { COLON }
  | ";"
      { SEMICOLON }
  | "->"
      { ARROW }
  | "<-"
      { LARROW }
  | "<->"
      { LRARROW }
  | "&&"
      { AMPAMP }
  | "||"
      { BARBAR }
  | "/\\"
      { AND }
  | "\\/"
      { OR }
   | "\\"
      { LAMBDA }
  | "\\?"
      { PRED }
  | "\\!"
      { FUNC }
  | "."
      { DOT }
  | "|"
      { BAR }
  | "="
      { EQUAL }
  | "<>"
      { LTGT }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | op_char_pref op_char_4* as s
      { OPPREF s }
  | op_char_1234* op_char_1 op_char_1234* as s
      { OP1 s }
  | op_char_234*  op_char_2 op_char_234*  as s
      { OP2 s }
  | op_char_34*   op_char_3 op_char_34*  as s
      { OP3 s }
  | op_char_4+ as s
      { OP4 s }
  | "\""
      { string_start_loc := loc lexbuf; STRING (string lexbuf) }
  | eof
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }

and comment = parse
  | "(*)"
      { comment lexbuf }
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | newline
      { newline lexbuf; comment lexbuf }
  | eof
      { raise (Loc.Located (!comment_start_loc, UnterminatedComment)) }
  | _
      { comment lexbuf }

and string = parse
  | "\""
      { let s = Buffer.contents string_buf in
        Buffer.clear string_buf;
        s }
  | "\\" (_ as c)
      { Buffer.add_char string_buf (char_for_backslash c); string lexbuf }
  | newline
      { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
  | eof
      { raise (Loc.Located (!string_start_loc, UnterminatedString)) }
  | _ as c
      { Buffer.add_char string_buf c; string lexbuf }

{
  let with_location f lb =
    if Debug.test_flag Debug.stack_trace then f lb else
    try f lb with
      | Loc.Located _ as e -> raise e
      | e -> raise (Loc.Located (loc lb, e))

  let parse_logic_file env path lb =
    pre_logic_file token (Lexing.from_string "") env path;
    with_location (logic_file token) lb

  let parse_program_file = with_location (program_file token)

  let read_channel env path file c =
    let lb = Lexing.from_channel c in
    Loc.set_file file lb;
    parse_logic_file env path lb

  let () = Env.register_format "why" ["why"] read_channel
}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. test"
End:
*)

