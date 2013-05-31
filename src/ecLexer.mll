{
  open EcUtils
  open EcParser

  module L = EcLocation

  exception LexicalError of L.t option * string

  let lex_error lexbuf msg =
    raise (LexicalError (Some (L.of_lexbuf lexbuf), msg))

  let unterminated_comment () =
    raise (LexicalError (None, "unterminated comment"))

  let unterminated_string () =
    raise (LexicalError (None, "unterminated string"))

  let _keywords = [                     (* see [keywords.py] *)
    "admit"       , ADMIT      ;        (* KW: dangerous *)

    "forall"      , FORALL     ;        (* KW: prog *)
    "exists"      , EXIST      ;        (* KW: prog *)
    "lambda"      , LAMBDA     ;        (* KW: prog *)
    "glob"        , GLOB       ;        (* KW: prog *)
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
    "res"         , RES        ;        (* KW: prog *)
    "equiv"       , EQUIV      ;        (* KW: prog *)
    "hoare"       , HOARE      ;        (* KW: prog *)
    "bd_hoare"    , BDHOARE    ;        (* KW: prog *)

    "using"       , USING      ;        (* KW: tactic *)
    "compute"     , COMPUTE    ;        (* KW: tactic *)
    "same"        , SAME       ;        (* KW: tactic *)
    "idtac"       , IDTAC      ;        (* KW: tactic *)
    "try"         , TRY        ;        (* KW: tactic *)

    "assumption"  , ASSUMPTION ;        (* KW: tactic *)
    "intros"      , INTROS     ;        (* KW: tactic *)
    "split"       , SPLIT      ;        (* KW: tactic *)
    "left"        , LEFT       ;        (* KW: tactic *)
    "right"       , RIGHT      ;        (* KW: tactic *)
    "elim"        , ELIM       ;        (* KW: tactic *)
    "apply"       , APPLY      ;        (* KW: tactic *)
    "trivial"     , TRIVIAL    ;        (* KW: tactic *)
    "cut"         , CUT        ;        (* KW: tactic *)
    "generalize"  , GENERALIZE ;        (* KW: tactic *)
    "clear"       , CLEAR      ;        (* KW: tactic *)
    "simplify"    , SIMPLIFY   ;        (* KW: tactic *)
    "delta"       , DELTA      ;        (* KW: tactic *)
    "zeta"        , ZETA       ;        (* KW: tactic *)
    "beta"        , BETA       ;        (* KW: tactic *)
    "iota"        , IOTA       ;        (* KW: tactic *)
    "logic"       , LOGIC      ;        (* KW: tactic *)
    "modpath"     , MODPATH    ;        (* KW: tactic *)
    "change"      , CHANGE     ;        (* KW: tactic *)
    "elimT"       , ELIMT      ;        (* KW: tactic *)
    "case"        , CASE       ;        (* KW: tactic *)
    "rewrite"     , REWRITE    ;        (* KW: tactic *)
    "subst"       , SUBST      ;        (* KW: tactic *)

    (* PHL: tactics *)
    "app"         , APP        ;        (* KW: tactic *)
    "wp"          , WP         ;        (* KW: tactic *)
    "skip"        , SKIP       ;        (* KW: tactic *)
    "call"        , CALL       ;        (* KW: tactic *)
    "rcondt"      , RCONDT     ;        (* KW: tactic *)
    "rcondf"      , RCONDF     ;        (* KW: tactic *)
    "swap"        , SWAP       ;        (* KW: tactic *)
    "rnd"         , RND        ;        (* KW: tactic *)
    "equiv_deno"  , EQUIVDENO  ;        (* KW: tactic *) 
    "conseq"      , CONSEQ     ;        (* KW: tactic *) 
    "inline"      , INLINE     ;        (* KW: tactic *)
    "alias"       , ALIAS      ;        (* KW: tactic *)
    "fission"     , FISSION    ;        (* KW: tactic *)
    "fusion"      , FUSION     ;        (* KW: tactic *)
    "unroll"      , UNROLL     ;        (* KW: tactic *)
    "splitwhile"  , SPLITWHILE ;        (* KW: tactic *)

    "axiom"       , AXIOM      ;        (* KW: global *)
    "lemma"       , LEMMA      ;        (* KW: global *)
    "proof"       , PROOF      ;        (* KW: global *)
    "save"        , SAVE       ;        (* KW: global *)
    "claim"       , CLAIM      ;        (* KW: global *)
    "drop"        , DROP       ;        (* KW: global *)
    "end"         , END        ;        (* KW: global *)
    "import"      , IMPORT     ;        (* KW: global *)
    "export"      , EXPORT     ;        (* KW: global *)
    "module"      , MODULE     ;        (* KW: global *)
    "of"          , OF         ;        (* KW: global *)
    "op"          , OP         ;        (* KW: global *)
    "pred"        , PRED       ;        (* KW: global *)
    "require"     , REQUIRE    ;        (* KW: global *)
    "theory"      , THEORY     ;        (* KW: global *)
    "type"        , TYPE       ;        (* KW: global *)
    "datatype"    , DATATYPE   ;        (* KW: global *)
    "print"       , PRINT      ;        (* KW: global *)
    "why3"        , WHY3       ;        (* KW: global *)  
    "as"          , AS         ;        (* KW: global *)  
    "Pr"          , PR         ;        (* KW: global *)  
    "clone"       , CLONE      ;        (* KW: global *)
    "with"        , WITH       ;        (* KW: global *)
    "prover"      , PROVER     ;        (* KW: global *)
    "checkproof"  , CHECKPROOF ;        (* KW: global *)
    "timeout"     , TIMEOUT    ;        (* KW: global *)
    "on"          , ON         ;        (* KW: global *)
    "off"         , OFF        ;        (* KW: global *)

    "undo"        , UNDO       ;        (* KW: internal *)
    "debug"       , DEBUG      ;        (* KW: internal *)
    "pragma"      , PRAGMA     ;        (* KW: internal *)
  ]

  let keywords = Hashtbl.create 97

  let _ =
    List.iter
      (fun (x, y) -> Hashtbl.add keywords x y)
      _keywords

  exception InvalidCodePosition

  let cposition_of_string =
    let cpos1 x =
      try  int_of_string x
      with Failure "int_of_string" -> raise InvalidCodePosition
    in

    let rec doit = function
      | Str.Text c :: []                  -> (cpos1 c, None)
      | Str.Text c :: Str.Delim "." :: tl -> (cpos1 c, Some (0, doit tl))
      | Str.Text c :: Str.Delim "?" :: tl -> (cpos1 c, Some (1, doit tl))
      | _ -> raise InvalidCodePosition
    in
      fun s -> doit (Str.full_split (Str.regexp "[.?]") s)

  let cposition_of_string s =
    try  Some (cposition_of_string s)
    with InvalidCodePosition -> None
}

let blank   = [' ' '\t' '\r']
let newline = '\n'
let upper   = ['A'-'Z']
let lower   = ['a'-'z']
let letter  = upper | lower
let digit   = ['0'-'9']
let number  = digit+

let ichar  = (letter | digit | '_' | '\'')
let lident = (lower ichar*) | ('_' ichar+)
let uident = upper ichar*
let tident = '\'' lident
let mident = '&'  (lident | number)

let op_char_1    = ['=' '<' '>']
let op_char_2    = ['+' '-']
let op_char_3    = ['*' '/' '%' '\\']
let op_char_4    = ['!' '$' '&' '?' '@' '^' ':' '|' '#']
let op_char_34   = op_char_3 | op_char_4
let op_char_234  = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

let op1 = op_char_1234* op_char_1 op_char_1234*
let op2 = op_char_234*  op_char_2 op_char_234+
let op3 = op_char_34*   op_char_3 op_char_34*
let op4 = op_char_4+

let binop = 
  op1 | op2 | op3 | op4 | '+' | '-' |
  '!' | "&&" | "/\\" | "||" | "\\/" | "=>" | "<=>" | '>' | "="

(* -------------------------------------------------------------------- *)
rule main = parse
  | newline      { Lexing.new_line lexbuf; main lexbuf }
  | blank+       { main lexbuf }
  | lident as id { try Hashtbl.find keywords id with Not_found -> LIDENT id }
  | uident as id { try Hashtbl.find keywords id with Not_found -> UIDENT id }
  | tident       { TIDENT (Lexing.lexeme lexbuf) }
  | mident       { MIDENT (Lexing.lexeme lexbuf) }
  | number       { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | "<<"         {BACKS}
  | ">>"         {FWDS }

  | "(*" binop "*)" { main lexbuf }
  | '(' blank* (binop as s) blank* ')' { PBINOP s }

  | "(*" { comment lexbuf; main lexbuf }
  | "\"" { STRING (Buffer.contents (string (Buffer.create 0) lexbuf)) }

  (* boolean operators *)
  | '!'   { NOT }
  | "&&"  { AND true }
  | "/\\" { AND false }
  | "||"  { OR true }
  | "\\/" { OR false }
  | "=>"  { IMPL }
  | "<=>" { IFF }

  (* string symbols *)
  | "<-"    { LEFTARROW }
  | "->"    { ARROW  }
  | ".."    { DOTDOT }
  | ".["    { DLBRACKET }
  | ":="    { CEQ }
  | "%r"    { FROM_INT }
  | "{0,1}" { RBOOL }

  (* position *)
  | (digit+ ['.' '?'])+ digit+ {
      CPOS (oget (cposition_of_string (Lexing.lexeme lexbuf)))
    } 

  (* punctuation *)
  | '_'  { UNDERSCORE }
  | '('  { LPAREN }
  | ')'  { RPAREN }
  | '{'  { LBRACE }
  | '}'  { RBRACE }
  | '['  { LBRACKET }
  | ']'  { RBRACKET }
  | "<:" { LTCOLON }
  | ">"  { GT }
  | ','  { COMMA }
  | ';'  { SEMICOLON }
  | ':'  { COLON }
  | '?'  { QUESTION }
  | "*"  { STAR }
  | "$"  { SAMPLE }
  | "|"  { PIPE }
  | "`|" { TICKPIPE }
  | "@"  { AT }
  | "~"  { TILD }

  | "==>" { LONGARROW }

  (* comparison *)
  | "="  { EQ }
  | "<>" { NE }

  | "<="  { LE }
  | ">="  { GE }

  | "-" { MINUS }
  | "+" { ADD }

  | op1 as s  { OP1 s }
  | op2 as s  { OP2 s }
  | op3 as s  { OP3 s }
  | op4 as s  { OP4 s }

  (* end of sentence / stream *)
  | '.' (eof | blank | newline as r) { 
      if r = "\n" then
        Lexing.new_line lexbuf;
      FINAL
    }

  | "." { DOT }

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
