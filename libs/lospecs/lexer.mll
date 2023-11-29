{
  open Parser

  let keywords = [
    ("fun"     , FUN     );
    ("let"     , LET     );
    ("in"      , IN      );
    ("signed"  , SIGNED  );
    ("unsigned", UNSIGNED);
  ]

  let keywords =
    let table = Hashtbl.create 0 in
    List.iter (fun (x, k) -> Hashtbl.add table x k) keywords;
    table
}

let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = lower | upper
let digit = ['0'-'9']
let alnum = alpha | digit

let ident = (alpha | '_') (alnum | '_')*

let decnum = digit+

let whitespace = [' ' '\t' '\r' '\n']

rule main = parse
  | '<'  { LT       }
  | '>'  { GT       }
  | '('  { LPAREN   }
  | ')'  { RPAREN   }
  | '['  { LBRACKET }
  | ']'  { RBRACKET }
  | '@'  { AT       }
  | "->" { RARROW   }
  | ','  { COMMA    }
  | '='  { EQUAL    }
  | ':'  { COLON    }
  | '.'  { DOT      }

  | ident as x
      { Hashtbl.find_default keywords x (IDENT x) }

  | decnum as d
      { NUMBER (int_of_string d) }

  | whitespace+
      { main lexbuf }

  | '#' [^'\r' '\n']* ['\r' '\n']*
      { main lexbuf }

(* DEBUG FEATURE: for binary searching for syntax errors
   to be switched for better error output *)
  | '^' _* 
      { main lexbuf }

  | eof
      { EOF }

  | _ as c {
      Format.eprintf "%c@." c;
      assert false
    }
