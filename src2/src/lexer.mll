{
  open EcUtil
  open Parser

  let init_filename lexbuf filename =
    let init_pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { init_pos with Lexing.pos_fname = filename };
    lexbuf

  let new_lexbuf filename =
    let chan = match filename with
      | None -> stdin
      | Some filename ->
        try (let ch = open_in filename in EcUtil.verbose "Read %s" filename; ch)
        with Sys_error msg -> EcUtil.user_error "%s" msg
    in
  (* Changed : [Lexing.from_channel] by [Lexing.from_function]
   * because we had  a problem with that when using an input from a file
   * that has Drop in it : because the lexer read the file in advance, so caml
   * doesn't see some of the following commands what were 'eaten' by the lexer.
   * So let's read one char at a time... *)
    let get str _n =
      try str.[0] <- (input_char chan); 1
      with End_of_file -> 0
    in
    let lexbuf = Lexing.from_function get in
    let filename = match filename with None -> "<stdin>" | Some f -> f in
    init_filename lexbuf filename

  let str_lexbuf str =
    let lexbuf = Lexing.from_string str in
    init_filename lexbuf "<string>"

(** Get filename, line number and column number of current lexeme. *)
  let pos_of_lexbuf lexbuf =
    let pos1 = Lexing.lexeme_start_p lexbuf in
    let pos2 = Lexing.lexeme_end_p lexbuf in
    EcUtil.pos_of_lex_pos pos1 pos2

  let newline lb = Lexing.new_line lb
  
  let lex_error lexbuf msg =
    let pos = pos_of_lexbuf lexbuf in
    raise (EcUtil.LexicalError (pos, msg))

  let comment_start_loc = ref EcUtil.dummy_pos

  let unterminated_comment () = 
    raise (EcUtil.LexicalError(!comment_start_loc,"unterminated comment"))


  let comment_start_loc lexbuf =
    comment_start_loc := pos_of_lexbuf lexbuf

  let string_start_loc = ref EcUtil.dummy_pos 

  let unterminated_string () = 
    raise (EcUtil.LexicalError(!string_start_loc,"unterminated string"))

  let string_start_loc lexbuf =
    string_start_loc := pos_of_lexbuf lexbuf

  let string_buf = Buffer.create 1024

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c

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

let blank = [' ' '\t' '\r' ]
let newline = '\n'
let letter =  ['a'-'z' '_'] | ['A'-'Z']
let digit =  ['0'-'9']
let number = digit+

let first_letter = letter
let other_letter = first_letter | digit | '\''
let ident = first_letter other_letter*

let prim_ident = '\'' ident

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234



rule token = parse
  | newline                   { newline lexbuf; token lexbuf }
  | blank+                    { token lexbuf }     (* skip blanks *)
  | ident as id               {
    try Hashtbl.find keywords id with Not_found -> IDENT id }
  | "(*"                      { comment_start_loc lexbuf;
                                comment lexbuf; token lexbuf }
  | number                    { NUM(int_of_string(Lexing.lexeme lexbuf)) }

  (* bool operation *)
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

  | prim_ident                 { PRIM_IDENT (Lexing.lexeme lexbuf)}
  | eof                        { EOF }
  | "\""                       { string_start_loc lexbuf; STRING (string lexbuf) }

  |  _ as c  { lex_error lexbuf ("illegal character: " ^ String.make 1 c) }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { newline lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

and string = parse
  | "\""
      { let s = Buffer.contents string_buf in
        Buffer.clear string_buf;
        s }
  | "\\" (_ as c) { Buffer.add_char string_buf (char_for_backslash c); string lexbuf }
  | newline       { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
  | eof           { unterminated_string () }
  | _ as c        { Buffer.add_char string_buf c; string lexbuf }


{

open EcUtil

let check_exn e = match e with
| (LexicalError _) as e ->  raise e
| (ParseError _) as e -> raise e
| Parsing.Parse_error ->
    bug "Parsing.Parse_error should be catched by EcParser.parse_error"
| _ -> raise e


let read lexbuf =
  (* OCAMLRUNPARAM='p' ocamlyacc -v src/ecParser.mly *)
  let _ = Parsing.set_trace false in
    try
      let prog, stop = Parser.prog token lexbuf in
        if stop then Lexing.flush_input lexbuf;
        prog, stop
    with e -> check_exn e


let read_glob str =
  let lexbuf = str_lexbuf str in
    try  Parser.global token lexbuf
    with e -> check_exn e
}

