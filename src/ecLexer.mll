{
  open EcUtils
  open EcParser

  module L = EcLocation

  exception LexicalError of L.t option * string

  let pp_error fmt = function
    | LexicalError(Some loc, s) ->
        L.pp_located loc (fun fmt -> Format.fprintf fmt "%s") fmt s
    | LexicalError(None, s) ->
        Format.fprintf fmt "%s" s
    | e -> raise e

  let _ = EcPexception.register pp_error

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
    "idtac"       , IDTAC      ;        (* KW: tactic *)
    "assumption"  , ASSUMPTION ;        (* KW: tactic *)
    "intros"      , INTROS     ;        (* KW: tactic *)
    "split"       , SPLIT      ;        (* KW: tactic *)
    "left"        , LEFT       ;        (* KW: tactic *)
    "right"       , RIGHT      ;        (* KW: tactic *)
    "elim"        , ELIM       ;        (* KW: tactic *)
    "apply"       , APPLY      ;        (* KW: tactic *)
    "trivial"     , TRIVIAL    ;        (* KW: tactic *)
    "admit"       , ADMIT      ;        (* KW: dangerous *)

    "axiom"       , AXIOM      ;        (* KW: global *)
    "lemma"       , LEMMA      ;        (* KW: global *)
    "proof"       , PROOF      ;        (* KW: global *)
    "save"        , SAVE       ;        (* KW: global *)
    "claim"       , CLAIM      ;        (* KW: global *)
    "cnst"        , CNST       ;        (* KW: global *)
    "drop"        , DROP       ;        (* KW: global *)
    "end"         , END        ;        (* KW: global *)
    "import"      , IMPORT     ;        (* KW: global *)
    "export"      , EXPORT     ;        (* KW: global *)
    "module"      , MODULE     ;        (* KW: global *)
    "op"          , OP         ;        (* KW: global *)
    "pred"        , PRED       ;        (* KW: global *)
    "require"     , REQUIRE    ;        (* KW: global *)
    "theory"      , THEORY     ;        (* KW: global *)
    "type"        , TYPE       ;        (* KW: global *)
    "print"       , PRINT      ;        (* KW: global *)
    "why3"        , WHY3       ;        (* KW: global *)  
    "as"          , AS         ;        (* KW: global *)  
    "Pr"          , PR         ;        (* KW: global *)  
    "clone"       , CLONE      ;        (* KW: global *)
    "with"        , WITH       ;        (* KW: global *)
    "prover"      , PROVER     ;        (* KW: global *)
    "checkproof"  , CHECKPROOF ;        (* KW: global *)
    "timeout"     , TIMEOUT    ;        (* KW: global *)

    "undo"        , UNDO       ;        (* KW: internal *)
  ]

  let keywords = Hashtbl.create 97

  let _ =
    List.iter
      (fun (x, y) -> Hashtbl.add keywords x y)
      _keywords
  let remove_bracket s = 
    let len = String.length s in
    if len > 2 && s.[0] = '[' then String.sub s 1 (String.length s - 2)
    else s

}

let blank   = [' ' '\t' '\r']
let newline = '\n'
let letter  = ['a'-'z' 'A'-'Z']
let digit   = ['0'-'9']
let number  = digit+

let ichar  = (letter | digit | '_' | '\'')
let ident  = (letter ichar*) | ('_' ichar+)

let prim_ident = '\'' ident

let op_char_1    = ['=' '<' '>' '~']
let op_char_2    = ['+' '-']
let op_char_3    = ['*' '/' '%' '\\']
let op_char_4    = ['!' '$' '&' '?' '@' '^' ':' '|' '#']
let op_char_34   = op_char_3 | op_char_4
let op_char_234  = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

let op1 = op_char_1234* op_char_1 op_char_1234*
let op2 = op_char_234*  op_char_2 op_char_234*  
let op3 = op_char_34*   op_char_3 op_char_34* 
let op4 = op_char_4+ 

let binop = 
  op1 | op2 | op3 | op4 | '!' | "&&" | "||" | "=>" | "<=>" | '>' | "=" 

let pbinop = '[' binop ']'

let qident = (ident '.')+ ident 

let qident_binop = (ident '.')+ pbinop

(* -------------------------------------------------------------------- *)
rule main = parse
  | newline      { Lexing.new_line lexbuf; main lexbuf }
  | blank+       { main lexbuf }
  | ident as id  { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | prim_ident   { PRIM_IDENT (Lexing.lexeme lexbuf)}
  | number       { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | "(*"         { comment lexbuf; main lexbuf }
  | "\""         { STRING (Buffer.contents (string (Buffer.create 0) lexbuf)) }

  | qident as id {
      let path = List.rev (String.split '.' id) in
      let qs = List.rev (List.tl path) in
      let s = List.hd path in
      QIDENT (qs, s)
    }

  | qident_binop as id { 
      let path = List.rev (String.split '.' id) in
      let qs = List.rev (List.tl path) in
      let s = List.hd path in
      let s = remove_bracket s in
      QPBINOP (qs, s)
    }

  | pbinop as s { PBINOP (remove_bracket s) }

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
  | ".["                      { DLBRACKET }
  | ":="                      { CEQ }
  | "%r"                      { FROM_INT }
  (* char symbols *)
  | '_'                       { UNDERSCORE }
  | '('                       { LPAREN }
  | ')'                       { RPAREN }
  | '{'                       { LKEY }
  | '}'                       { RKEY }
  | '['                       { LBRACKET }
  | ']'                       { RBRACKET }
  | "<:"                      { LTCOLON }
  | ">"                       { GT }                      
  | ','                       { COMMA }
  | ';'                       { SEMICOLON }
  | '.'                       { DOT }
  | ':'                       { COLON }
  | "}^"                      { RKEY_HAT }
  | '?'                       { QUESTION }
  | "*"                       { STAR }
  | "$"                       { SAMPLE }
  | "|"                       { PIPE }

  (* comparison *)
  | "="                       { EQ }
  | "<>"                      { NE }

  | op1 as s                  { OP1 s }
  | op2  as s                 { OP2 s }
  | op3  as s                 { OP3 s }
  | op4 as s                  { OP4 s }

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
