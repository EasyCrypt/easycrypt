{
  open Parser

  module L = Parsetree.Location

  exception LexicalError of L.t option * string

  let lex_error lexbuf msg =
    raise (LexicalError (Some (L.of_lexbuf lexbuf), msg))

  let unterminated_comment () =
    raise (LexicalError (None, "unterminated comment"))

  let unterminated_string () =
    raise (LexicalError (None, "unterminated string"))

  let _keywords = [                      (* see [keywords.py] *)

    "forall"      , FORALL     ;        (* KW: prog *)
    "exists"      , EXIST      ;        (* KW: prog *)
    "let"         , LET        ;        (* KW: prog *)
    "in"          , IN         ;        (* KW: prog *)
    "true"        , TRUE       ;        (* KW: prog *)
    "false"       , FALSE      ;        (* KW: prog *)

    "bitstring"   , BITSTR     ;        (* KW: prog *)
    "var"         , VAR        ;        (* KW: prog *)
    "fun"         , FUN        ;        (* KW: prog *)
    "if"          , IF         ;        (* KW: prog *)
    "then"        , THEN       ;        (* KW: prog *)
    "else"        , ELSE       ;        (* KW: prog *)
    "while"       , WHILE      ;        (* KW: prog *)
    "assert"      , ASSERT     ;        (* KW: prog *)
    "return"      , RETURN     ;        (* KW: prog *)

    "using"       , USING      ;        (* KW: tactic *)
    "compute"     , COMPUTE    ;        (* KW: tactic *)
    "same"        , SAME       ;        (* KW: tactic *)
    "split"       , SPLIT      ;        (* KW: tactic *)

    "admit"       , ADMIT      ;        (* KW: dangerous *)

    "axiom"       , AXIOM      ;        (* KW: global *)
    "claim"       , CLAIM      ;        (* KW: global *)
    "cnst"        , CNST       ;        (* KW: global *)
    "drop"        , DROP       ;        (* KW: global *)
    "end"         , END        ;        (* KW: global *)
    "module"      , MODULE     ;        (* KW: global *)
    "op"          , OP         ;        (* KW: global *)
    "pop"         , POP        ;        (* KW: global *)
    "theory"      , THEORY     ;        (* KW: global *)
    "type"        , TYPE       ;        (* KW: global *)
  ]

  let keywords = Hashtbl.create 97

  let _ =
    List.iter
      (fun (x, y) -> Hashtbl.add keywords x y)
      _keywords
}

let blank   = [' ' '\t' '\r']
let newline = '\n'
let letter  = ['a'-'z' 'A'-'Z']
let digit   = ['0'-'9']
let number  = digit+

let ident      = (letter | '_') (letter | digit | '_' | '\'')*
let prim_ident = '\'' ident

let op_char_1    = ['=' '<' '>' '~']
let op_char_2    = ['+' '-']
let op_char_3    = ['*' '/' '%']
let op_char_4    = ['!' '$' '&' '?' '@' '^' ':' '|' '#']
let op_char_34   = op_char_3 | op_char_4
let op_char_234  = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

(* -------------------------------------------------------------------- *)
rule main = parse
  | newline                   { Lexing.new_line lexbuf; main lexbuf }
  | blank+                    { main lexbuf }
  | ident as id               { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | prim_ident                { PRIM_IDENT (Lexing.lexeme lexbuf)}
  | number                    { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | "(*"                      { comment lexbuf; main lexbuf }
  | "\""                      { STRING (Buffer.contents (string (Buffer.create 0) lexbuf)) }

  (* boolean operators *)
  | '!'                       { NOT }
  | "&&"                      { AND }
  | "||"                      { OR }
  | "=>"                      { IMPL }
  | "<=>"                     { IFF }

  (* string symbols *)
  | "<-"                      { LEFTARROW }
  | "->"                      { ARROW  }
  | ".."                      { DOTDOT }

  (* char symbols *)
  | '('                       { LPAREN }
  | ')'                       { RPAREN }
  | '{'                       { LKEY }
  | '}'                       { RKEY }
  | '['                       { LBRACKET }
  | ']'                       { RBRACKET }
  | ','                       { COMMA }
  | ';'                       { SEMICOLON }
  | '.'                       { DOT }
  | ':'                       { COLON }
  | ":>"                      { DCOLON }
  | "}^"                      { RKEY_HAT }
  | '?'                       { QUESTION }
  | '|'                       { PIPE }
  | '\\'                      { BACKSLASH }
  | "*"                       { STAR }
  | "-"                       { MINUS }

  (* comparison *)
  | "="                       { EQ }
  | "<>"                      { NE }

  | op_char_1234* op_char_1 op_char_1234* as s
      { OP1 s }
  | op_char_234*  op_char_2 op_char_234*  as s
      { OP2 s }
  | op_char_34*   op_char_3 op_char_34*  as s
      { OP3 s }
  | op_char_4+ as s
      { OP4 s }

  | eof { EOF }

  |  _ as c  { lex_error lexbuf ("illegal character: " ^ String.make 1 c) }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

and string buf = parse
  | "\""          { buf }
  | "\\n"         { Buffer.add_char buf '\n'; string buf lexbuf }
  | "\\r"         { Buffer.add_char buf '\r'; string buf lexbuf }
  | "\\" (_ as c) { Buffer.add_char buf c   ; string buf lexbuf }
  | newline       { Buffer.add_string buf (Lexing.lexeme lexbuf); string buf lexbuf }
  | _ as c        { Buffer.add_char buf c   ; string buf lexbuf }

  | eof           { unterminated_string () }
