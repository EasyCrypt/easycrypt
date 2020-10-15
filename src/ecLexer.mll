(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
{
  open EcUtils
  open EcParser

  module BI = EcBigInt
  module L  = EcLocation

  (* ------------------------------------------------------------------ *)
  exception LexicalError of L.t option * string

  let pp_lex_error fmt msg =
    Format.fprintf fmt "parse error: %s" msg

  let () =
    let pp fmt exn =
      match exn with
      | LexicalError (_, msg) -> pp_lex_error fmt msg
      | _ -> raise exn
    in
      EcPException.register pp

  (* ------------------------------------------------------------------ *)
  let lex_error lexbuf msg =
    raise (LexicalError (Some (L.of_lexbuf lexbuf), msg))

  let unterminated_comment () =
    raise (LexicalError (None, "unterminated comment"))

  let unterminated_string () =
    raise (LexicalError (None, "unterminated string"))

  (* ------------------------------------------------------------------ *)
  let _keywords = [                     (* see [keywords.py] *)
    "admit"       , ADMIT      ;        (* KW: dangerous *)
    "admitted"    , ADMITTED   ;        (* KW: dangerous *)

    "forall"      , FORALL     ;        (* KW: prog *)
    "exists"      , EXIST      ;        (* KW: prog *)
    "fun"         , FUN        ;        (* KW: prog *)
    "glob"        , GLOB       ;        (* KW: prog *)
    "let"         , LET        ;        (* KW: prog *)
    "in"          , IN         ;        (* KW: prog *)
    "for"         , FOR        ;        (* KW: prog *)
    "var"         , VAR        ;        (* KW: prog *)
    "proc"        , PROC       ;        (* KW: prog *)
    "if"          , IF         ;        (* KW: prog *)
    "then"        , THEN       ;        (* KW: prog *)
    "else"        , ELSE       ;        (* KW: prog *)
    "elif"        , ELIF       ;        (* KW: prog *)
    "for"         , FOR        ;        (* KW: prog *)
    "while"       , WHILE      ;        (* KW: prog *)
    "assert"      , ASSERT     ;        (* KW: prog *)
    "return"      , RETURN     ;        (* KW: prog *)
    "res"         , RES        ;        (* KW: prog *)
    "equiv"       , EQUIV      ;        (* KW: prog *)
    "hoare"       , HOARE      ;        (* KW: prog *)
    "phoare"      , PHOARE     ;        (* KW: prog *)
    "islossless"  , LOSSLESS   ;        (* KW: prog *)
    "async"       , ASYNC      ;        (* KW: prog *)

    "try"         , TRY        ;        (* KW: tactical *)
    "first"       , FIRST      ;        (* KW: tactical *)
    "last"        , LAST       ;        (* KW: tactical *)
    "do"          , DO         ;        (* KW: tactical *)
    "strict"      , STRICT     ;        (* KW: tactical *)
    "expect"      , EXPECT     ;        (* KW: tactical *)

    (* Lambda tactics *)
    "beta"        , BETA       ;        (* KW: tactic *)
    "iota"        , IOTA       ;        (* KW: tactic *)
    "zeta"        , ZETA       ;        (* KW: tactic *)
    "eta"         , ETA        ;        (* KW: tactic *)
    "logic"       , LOGIC      ;        (* KW: tactic *)
    "delta"       , DELTA      ;        (* KW: tactic *)
    "simplify"    , SIMPLIFY   ;        (* KW: tactic *)
    "cbv"         , CBV        ;        (* KW: tactic *)
    "congr"       , CONGR      ;        (* KW: tactic *)

    (* Logic tactics *)
    "change"      , CHANGE     ;        (* KW: tactic *)
    "split"       , SPLIT      ;        (* KW: tactic *)
    "left"        , LEFT       ;        (* KW: tactic *)
    "right"       , RIGHT      ;        (* KW: tactic *)
    "case"        , CASE       ;        (* KW: tactic *)

    "pose"        , POSE       ;        (* KW: tactic *)
    "cut"         , CUT        ;        (* KW: tactic *)
    "have"        , HAVE       ;        (* KW: tactic *)
    "suff"        , SUFF       ;        (* KW: tactic *)
    "elim"        , ELIM       ;        (* KW: tactic *)
    "exlim"       , EXLIM      ;        (* KW: tactic *)
    "ecall"       , ECALL      ;        (* KW: tactic *)
    "clear"       , CLEAR      ;        (* KW: tactic *)
    "wlog"        , WLOG       ;        (* KW: tactic *)

    (* Auto tactics *)
    "apply"       , APPLY      ;        (* KW: tactic *)
    "rewrite"     , REWRITE    ;        (* KW: tactic *)
    "rwnormal"    , RWNORMAL   ;        (* KW: tactic *)
    "subst"       , SUBST      ;        (* KW: tactic *)
    "progress"    , PROGRESS   ;        (* KW: tactic *)
    "trivial"     , TRIVIAL    ;        (* KW: tactic *)
    "auto"        , AUTO       ;        (* KW: tactic *)

    (* Other tactics *)
    "idtac"       , IDTAC      ;        (* KW: tactic *)
    "move"        , MOVE       ;        (* KW: tactic *)
    "modpath"     , MODPATH    ;        (* KW: tactic *)
    "field"       , FIELD `Raw ;        (* KW: tactic *)
    "fieldeq"     , FIELD `Eq  ;        (* KW: tactic *)
    "ring"        , RING `Raw  ;        (* KW: tactic *)
    "ringeq"      , RING `Eq   ;        (* KW: tactic *)
    "algebra"     , ALGNORM    ;        (* KW: tactic *)

    "exact"       , EXACT      ;        (* KW: bytac *)
    "assumption"  , ASSUMPTION ;        (* KW: bytac *)
    "smt"         , SMT        ;        (* KW: bytac *)
    "by"          , BY         ;        (* KW: bytac *)
    "reflexivity" , REFLEX     ;        (* KW: bytac *)
    "done"        , DONE       ;        (* KW: bytac *)
    "solve"       , SOLVE      ;        (* KW: bytac *)

    (* PHL: tactics *)
    "replace"     , REPLACE    ;        (* KW: tactic *)
    "transitivity", TRANSITIVITY;       (* KW: tactic *)
    "symmetry"    , SYMMETRY   ;        (* KW: tactic *)
    "seq"         , SEQ        ;        (* KW: tactic *)
    "wp"          , WP         ;        (* KW: tactic *)
    "sp"          , SP         ;        (* KW: tactic *)
    "sim"         , SIM        ;        (* KW: tactic *)
    "skip"        , SKIP       ;        (* KW: tactic *)
    "call"        , CALL       ;        (* KW: tactic *)
    "rcondt"      , RCONDT     ;        (* KW: tactic *)
    "rcondf"      , RCONDF     ;        (* KW: tactic *)
    "swap"        , SWAP       ;        (* KW: tactic *)
    "cfold"       , CFOLD      ;        (* KW: tactic *)
    "rnd"         , RND        ;        (* KW: tactic *)
    "pr_bounded"  , PRBOUNDED  ;        (* KW: tactic *)
    "bypr"        , BYPR       ;        (* KW: tactic *)
    "byphoare"    , BYPHOARE   ;        (* KW: tactic *)
    "byequiv"     , BYEQUIV    ;        (* KW: tactic *)
    "fel"         , FEL        ;        (* KW: tactic *)

    "conseq"      , CONSEQ     ;        (* KW: tactic *)
    "exfalso"     , EXFALSO    ;        (* KW: tactic *)
    "inline"      , INLINE     ;        (* KW: tactic *)
    "interleave"  , INTERLEAVE ;        (* KW: tactic *)
    "alias"       , ALIAS      ;        (* KW: tactic *)
    "fission"     , FISSION    ;        (* KW: tactic *)
    "fusion"      , FUSION     ;        (* KW: tactic *)
    "unroll"      , UNROLL     ;        (* KW: tactic *)
    "splitwhile"  , SPLITWHILE ;        (* KW: tactic *)
    "kill"        , KILL       ;        (* KW: tactic *)
    "eager"       , EAGER      ;        (* KW: tactic *)

    "axiom"       , AXIOM      ;        (* KW: global *)
    "axiomatized" , AXIOMATIZED;        (* KW: global *)
    "lemma"       , LEMMA      ;        (* KW: global *)
    "realize"     , REALIZE    ;        (* KW: global *)
    "proof"       , PROOF      ;        (* KW: global *)
    "qed"         , QED        ;        (* KW: global *)
    "abort"       , ABORT      ;        (* KW: global *)
    "goal"        , GOAL       ;        (* KW: global *)
    "end"         , END        ;        (* KW: global *)
    "from"        , FROM       ;        (* KW: global *)
    "import"      , IMPORT     ;        (* KW: global *)
    "export"      , EXPORT     ;        (* KW: global *)
    "include"     , INCLUDE    ;        (* KW: global *)
    "local"       , LOCAL      ;        (* KW: global *)
    "declare"     , DECLARE    ;        (* KW: global *)
    "hint"        , HINT       ;        (* KW: global *)
    "nosmt"       , NOSMT      ;        (* KW: global *)
    "module"      , MODULE     ;        (* KW: global *)
    "of"          , OF         ;        (* KW: global *)
    "const"       , CONST      ;        (* KW: global *)
    "op"          , OP         ;        (* KW: global *)
    "pred"        , PRED       ;        (* KW: global *)
    "inductive"   , INDUCTIVE  ;        (* KW: global *)
    "notation"    , NOTATION   ;        (* KW: global *)
    "abbrev"      , ABBREV     ;        (* KW: global *)
    "require"     , REQUIRE    ;        (* KW: global *)
    "theory"      , THEORY     ;        (* KW: global *)
    "abstract"    , ABSTRACT   ;        (* KW: global *)
    "section"     , SECTION    ;        (* KW: global *)
    "type"        , TYPE       ;        (* KW: global *)
    "class"       , CLASS      ;        (* KW: global *)
    "instance"    , INSTANCE   ;        (* KW: global *)
    "print"       , PRINT      ;        (* KW: global *)
    "search"      , SEARCH     ;        (* KW: global *)
    "as"          , AS         ;        (* KW: global *)
    "Pr"          , PR         ;        (* KW: global *)
    "clone"       , CLONE      ;        (* KW: global *)
    "with"        , WITH       ;        (* KW: global *)
    "rename"      , RENAME     ;        (* KW: global *)
    "prover"      , PROVER     ;        (* KW: global *)
    "timeout"     , TIMEOUT    ;        (* KW: global *)
    "why3"        , WHY3       ;        (* KW: global *)
    "dump"        , DUMP       ;        (* KW: global *)
    "remove"      , REMOVE     ;        (* KW: global *)

    "time"        , TIME       ;        (* KW: internal *)
    "undo"        , UNDO       ;        (* KW: internal *)
    "debug"       , DEBUG      ;        (* KW: internal *)
    "pragma"      , PRAGMA     ;        (* KW: internal *)

    "Top"         , TOP        ;        (* KW: global *)
    "Self"        , SELF       ;        (* KW: global *)
  ]

  (* ------------------------------------------------------------------ *)
  let _operators = [
    (":"   , (COLON            , true ));
    ("#"   , (SHARP            , true ));
    ("#|"   ,(SHARPPIPE        , true ));
    ("//"  , (SLASHSLASH       , true ));
    ("//#" , (SLASHSLASHSHARP  , true ));
    ("/="  , (SLASHEQ          , true ));
    ("/#"  , (SLASHSHARP       , true ));
    ("//=" , (SLASHSLASHEQ     , true ));
    ("/>"  , (SLASHGT          , true ));
    ("|>"  , (PIPEGT           , true ));
    ("//>" , (SLASHSLASHGT     , true ));
    ("||>" , (PIPEPIPEGT       , true ));
    ("=>"  , (IMPL             , true ));
    ("|"   , (PIPE             , true ));
    (":="  , (CEQ              , true ));
    ("/"   , (SLASH            , true ));
    ("\\"  , (BACKSLASH        , true ));
    ("<-"  , (LARROW           , true ));
    ("->"  , (RARROW           , true ));
    ("<<-" , (LLARROW          , true ));
    ("->>" , (RRARROW          , true ));
    ("!"   , (NOT              , false));
    ("^"   , (HAT              , false));
    ("&"   , (AMP              , false));
    ("&&"  , (ANDA             , false));
    ("/\\" , (AND              , false));
    ("||"  , (ORA              , false));
    ("\\/" , (OR               , false));
    ("<=>" , (IFF              , false));
    ("%"   , (PCENT            , false));
    ("+"   , (PLUS             , false));
    ("-"   , (MINUS            , false));
    ("*"   , (STAR             , false));
    ("<<"  , (BACKS            , false));
    (">>"  , (FWDS             , false));
    ("<:"  , (LTCOLON          , false));
    ("==>" , (LONGARROW        , false));
    ("="   , (EQ               , false));
    ("<>"  , (NE               , false));
    (">"   , (GT               , false));
    ("<"   , (LT               , false));
    (">="  , (GE               , false));
    ("<="  , (LE               , false));
    ("<*>" , (LTSTARGT         , false));
    ("<<*>", (LTLTSTARGT       , false));
    ("<*>>", (LTSTARGTGT       , false));
  ]

  (* ------------------------------------------------------------------ *)
  let keywords =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _keywords; table

  (* ------------------------------------------------------------------ *)
  let operators =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _operators; table

  let opre =
    let ops = List.map fst (List.filter (snd |- snd) _operators) in
    let ops = List.ksort ~key:(String.length) ~cmp:compare ~rev:true ops in
    let ops = String.join "|" (List.map EcRegexp.quote ops) in
    let ops = Printf.sprintf "(%s)" ops in
    EcRegexp.regexp ops

  (* ----------------------------------------------------------------- *)
  let lex_std_op ?name op =
    match op.[0] with
    | '=' | '<' | '>'       -> LOP1 (name |> odfl op)
    | '+' | '-' | '|'       -> LOP2 (name |> odfl op)
    | '*' | '/' | '&' | '%' -> LOP3 (name |> odfl op)
    | _                     -> LOP4 (name |> odfl op)

  (* ------------------------------------------------------------------ *)
  let lex_operators (op : string) =
    let baseop (op : string) =
      try  fst (Hashtbl.find operators op)
      with Not_found ->
        if   EcRegexp.match_ (`S "^:+$") op
        then ROP4 op else begin
          if   EcRegexp.match_ (`S "^%+.$") op
          then lex_std_op ~name:op (String.make 1 op.[String.length op -1])
          else raise Not_found
        end
    in
      try  [baseop op]
      with Not_found ->
        List.map
        (function
          | EcRegexp.Delim op ->
              fst (Hashtbl.find operators op)
          | EcRegexp.Text op ->
              try baseop op with Not_found -> lex_std_op op)
        (EcRegexp.split (`C opre) op)

  (* ------------------------------------------------------------------ *)
  let lex_tick_operator (op : string) =
    let name = Printf.sprintf "`%s`" op in
    lex_std_op ~name op
}

let empty   = ""
let blank   = [' ' '\t' '\r']
let newline = '\n'
let upper   = ['A'-'Z']
let lower   = ['a'-'z']
let letter  = upper | lower
let digit   = ['0'-'9']
let uint    = digit+

let ichar  = (letter | digit | '_' | '\'')
let lident = (lower ichar*) | ('_' ichar+)
let uident = upper ichar*
let tident = '\'' lident
let mident = '&'  (lident | uint)

let opchar = ['=' '<' '>' '+' '-' '*' '/' '\\' '%' '&' '^' '|' ':' '#' '$']

let sop = opchar+ | '`' opchar+ '`'
let nop = '\\' ichar+

let uniop = nop | ['-' '+']+ | '!'
let binop = sop | nop
let numop = '\'' digit+

(* -------------------------------------------------------------------- *)
rule main = parse
  | newline      { Lexing.new_line lexbuf; main lexbuf }
  | blank+       { main lexbuf }
  | lident as id { try [Hashtbl.find keywords id] with Not_found -> [LIDENT id] }
  | uident as id { try [Hashtbl.find keywords id] with Not_found -> [UIDENT id] }
  | tident       { [TIDENT (Lexing.lexeme lexbuf)] }
  | mident       { [MIDENT (Lexing.lexeme lexbuf)] }
  | uint         { [UINT (BI.of_string (Lexing.lexeme lexbuf))] }

  | (digit+ as n) '.' (digit+ as f) {
      let nv, fv = BI.of_string n, BI.of_string f in
      [DECIMAL (nv, (String.length f, fv))]
    }

  | "(*" binop "*)" { main lexbuf }
  | '(' blank* (binop as s) blank* ')' { [PBINOP s] }
  | '(' blank* (numop as s) blank* ')' { [PNUMOP s] }

  | '[' blank* (uniop as s) blank* ']' {
      let name = Printf.sprintf "[%s]" s in
      try
        let (tk, ok) = Hashtbl.find operators s in
          if ok then [LBRACKET; tk; RBRACKET] else [PUNIOP name]
      with Not_found -> [PUNIOP name]
  }

  | "(*" { comment lexbuf; main lexbuf }
  | "\"" { [STRING (Buffer.contents (string (Buffer.create 0) lexbuf))] }

  (* string symbols *)
  | ".."    { [DOTDOT   ] }
  | ".["    { [DLBRACKET] }
  | ".`"    { [DOTTICK  ] }
  | "{0,1}" { [RBOOL    ] }

  (* punctuation *)
  | '_'   { [UNDERSCORE] }
  | "#<"  { [DASHLT    ] }
  | '('   { [LPAREN    ] }
  | ')'   { [RPAREN    ] }
  | '{'   { [LBRACE    ] }
  | '}'   { [RBRACE    ] }
  | '['   { [LBRACKET  ] }
  | ']'   { [RBRACKET  ] }
  | ','   { [COMMA     ] }
  | ';'   { [SEMICOLON ] }
  | '?'   { [QUESTION  ] }
  | "~"   { [TILD      ] }
  | "!"   { [NOT       ] }
  | "@"   { [AT        ] }
  | "{|"  { [LPBRACE   ] }
  | "|}"  { [RPBRACE   ] }
  | "`|"  { [TICKPIPE  ] }
  | "<$"  { [LESAMPLE  ] }
  | "<@"  { [LEAT      ] }
  | ":~"  { [COLONTILD ] }

  | "/~="  { [SLASHTILDEQ     ] }
  | "//~=" { [SLASHSLASHTILDEQ] }

  (* operators *)
  | nop as x { [NOP x] }

  | '`' (opchar+ as op) '`' {
      [lex_tick_operator op]
    }

  | opchar as op {
      let op = operator (Buffer.from_char op) lexbuf in
      lex_operators (Buffer.contents op)
    }

  | numop as op {
      [NUMOP op]
    }

  (* end of sentence / stream *)
  | '.' (eof | blank | newline as r) {
      if r = "\n" then
        Lexing.new_line lexbuf;
      [FINAL]
    }

  | "." { [DOT] }

  | eof { [EOF] }

  (* errors *)

  | '\'' uident     { lex_error lexbuf "type variables must be low-identifiers" }
  | ['\'' '`'] as c { lex_error lexbuf (Printf.sprintf "illegal use of character: %c" c) }
  |  _         as c { lex_error lexbuf (Printf.sprintf "illegal character: %c" c) }

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

and operator buf = parse
  | opchar* as x { Buffer.add_string buf x; buf }
