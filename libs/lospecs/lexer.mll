{
  open Parser

  let keywords = [
    ("fun"     , FUN     );
    ("let"     , LET     );
    ("in"      , IN      );
  ]

  let keywords =
    let table = Hashtbl.create 0 in
    List.iter (fun (x, k) -> Hashtbl.add table x k) keywords;
    table
}

let lower    = ['a'-'z']
let upper    = ['A'-'Z']
let alpha    = lower | upper
let digit    = ['0'-'9']
let hexdigit = digit | ['a'-'f'] | ['A'-'F']
let alnum    = alpha | digit

let ident = (alpha | '_') (alnum | '_')*

let decnum = digit+
let hexnum = "0x" hexdigit+

let whitespace = [' ' '\t' '\r']

rule main = parse
  | '<'  { LT       }
  | '>'  { GT       }
  | '('  { LPAREN   }
  | ')'  { RPAREN   }
  | '['  { LBRACKET }
  | ']'  { RBRACKET }
  | '@'  { AT       }
  | "<-" { LARROW   }
  | "->" { RARROW   }
  | ','  { COMMA    }
  | '='  { EQUAL    }
  | ':'  { COLON    }
  | '.'  { DOT      }
  | '|'  { PIPE     }
  | '?'  { QMARK    }

  | ident as x
      { Hashtbl.find_default keywords x (IDENT x) }

  | decnum as d
      { NUMBER (int_of_string d) }

  | hexnum as d
      { NUMBER (int_of_string d) }

  | whitespace+
      { main lexbuf }

  | '\n'
      { Lexing.new_line lexbuf; main lexbuf }

  | '#' [^'\n']*
      { main lexbuf }

(* DEBUG FEATURE: for binary searching for syntax errors
   to be switched for better error output *)
  | '^' _* 
      { main lexbuf }

  | eof
      { EOF }

  | _ {
        raise (Ptree.ParseError (Ptree.Lc.of_lexbuf lexbuf))
    }
