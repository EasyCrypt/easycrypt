{ 
  open EpParser
    
}

let num      = ['0'-'9']
let alpha    = ['_' 'a'-'z' 'A'-'Z'] 
let alphanum = alpha | num | '.'
  
let id    = alpha alphanum*

rule token = parse
  | '\n'         { token lexbuf }
  | [' ' '\t']   { token lexbuf }
  | eof          { EOF }

  | "item"       { K_ITEM }
  | "block"      { K_BLOCK }
  | "seq"        { K_SEQ }
  | "iseq"       { K_ISEQ }
  | "pack"       { K_PACK }
  | "cascade"    { K_CASCADE }
  | "instr"      { K_INSTR }
  | "newline"    { K_NEWLINE }
  | "break"      { K_BREAK }
  | "ipack"      { K_IPACK }
  | "group"      { K_GROUP }

  | '['          { LSQ }
  | ']'          { RSQ }
      
  | id as lxm    { ID lxm }
  | '"' [^'"']* '"' as lxm { STR (String.sub 
				    lxm 1 (String.length lxm -2 ) )
				 }
