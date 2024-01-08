%{
  open Ptree

  let string_of_position ((p1, p2) : Lexing.position * Lexing.position) =
    Format.sprintf "%d.%d:%d.%d"
      p1.pos_lnum (p1.pos_cnum - p1.pos_bol + 1)
      p2.pos_lnum (p2.pos_cnum - p2.pos_bol + 1)
%}

%token AT
%token COLON
%token COMMA
%token DOT
%token EOF
%token EQUAL
%token FUN
%token GT
%token LBRACKET
%token LET
%token LPAREN
%token LT
%token IN
%token PIPE
%token RARROW
%token RBRACKET
%token RPAREN

%token<string> IDENT
%token<int>    NUMBER

%type <Ptree.pprogram> program

%start program

%%

%inline vname:
| x=IDENT
    { x }

%inline wname:
| x=vname t=wtype
    { (x, t) }

%inline wtype:
| AT x=NUMBER
    { `W x }

fname:
| f=IDENT
    { (f, None) }

| f=IDENT p=angled(list0(NUMBER, COMMA))
    { (f, Some (List.map (fun x -> `W x) p)) }

sexpr:
| f=fname
    { PEFName f }

| f=fname args=parens(list0(earg, COMMA))
    { PEApp (f, args) }

| e=parens(expr)
    { PEParens e }

| i=NUMBER
    { PEInt i }

expr:
| e=sexpr
    { e }

| FUN args=wname* DOT body=expr
    { PEFun (args, body) }

| LET x=IDENT args=parens(wname*)? EQUAL e1=expr IN e2=expr
    { PELet ((x, args, e1), e2) }

| e=sexpr LBRACKET
    s=option(AT s=expr PIPE { s }) i=expr j=prefix(COLON, expr)?
  RBRACKET
    { PESlice (e, (i, j, s)) }

earg:
| DOT
    { None }

| e=expr
    { Some e }

def:
| name=IDENT args=parens(list0(wname, COMMA)) RARROW rty=wtype EQUAL body=expr
    { { name; args; rty; body; } }

program:
| defs=def* EOF
    { defs }

| error
    { failwith (string_of_position $loc) }

%inline parens(X):
| LPAREN x=X RPAREN { x }

%inline angled(X):
| LT x=X GT { x }

%inline list0(X, S):
| x=separated_list(S, X) { x }

%inline prefix(S, X):
| S x=X { x }
