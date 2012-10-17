%{
  open EpLayout

%}

%token LSQ RSQ EOF
%token K_ITEM K_ISEQ K_BLOCK K_SEQ K_PACK K_INSTR K_GROUP
%token K_CASCADE K_BREAK K_IPACK K_NEWLINE

%token <string> ID STR

%start codeplus
%type <EpLayout.code list> codeplus

%%


code:
  | K_ITEM STR          { citem $2 }
  | K_CASCADE code code { Ccascade ($2,$3) }
  | K_BLOCK codels      { Cblock $2 }
  | K_SEQ codels        { Cseq $2 }
  | K_ISEQ codels       { Ciseq $2 }
  | K_PACK codels       { Cpack $2 }
  | K_INSTR codels      { Cinstr $2 }
  | K_NEWLINE           { Cnewline }
  | K_IPACK codels      { Cipack $2 }
//  | K_GROUP code        { Cgroup $2 }
  | K_BREAK             { Cbreak }
;  

codels:
  | LSQ codestar RSQ { $2 }
;

codestar:
  |          { [] }     
  | codeplus { $1 }
;

codeplus:
  | code          { [ $1 ] } 
  | code codeplus { $1 :: $2 } 
;
