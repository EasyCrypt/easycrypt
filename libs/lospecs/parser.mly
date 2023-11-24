%{
  open Ptree
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
%token RARROW
%token RBRACKET
%token RPAREN
%token SIGNED
%token UNSIGNED

%token<string> IDENT
%token<int>    NUMBER

%type <Ptree.pprogram> program

%start program

%%

(*
%inline empty:
| (* empty *) { () }
*)

%inline wname:
| x=IDENT t=wtype
    { (x, t) }

%inline wtype:
| AT x=NUMBER
    { W x }

type_:
| x=wtype
    { let W x = x in Word x }

| UNSIGNED
    { Unsigned }

| SIGNED
    { Signed }

fname:
| f=IDENT
    { (f, None) }

| f=IDENT p=angled(list0(NUMBER, COMMA))
    { (f, Some (List.map (fun x -> W x) p)) }

sexpr:
| f=fname args=parens(list0(expr, COMMA))?
    { PEApp (f, Option.default [] args) }

| e=parens(expr)
    { PEParens e }

| i=NUMBER
    { PEInt i }

expr:
| e=sexpr
    { e }

| FUN args=wname* DOT body=expr
    { PEFun (args, body) }

| LET x=IDENT EQUAL e1=expr IN e2=expr
    { PELet ((x, e1), e2) }

| e=sexpr LBRACKET i1=expr COLON i2=expr RBRACKET
    { PESlice (e, (i1, i2, None)) }

| e=sexpr LBRACKET i1=expr COLON i2=expr COLON i3=expr RBRACKET
    { PESlice (e, (i1, i2, Some i3)) }

| LPAREN t=type_ RPAREN e=expr
    { PECast (t, e) }

def:
| name=IDENT args=parens(list0(wname, COMMA)) RARROW rty=wtype EQUAL body=expr
    { { name; args; rty; body; } }

program:
| defs=def* EOF
    { defs }

%inline parens(X):
| LPAREN x=X RPAREN { x }

%inline angled(X):
| LT x=X GT { x }

%inline list0(X, S):
| x=separated_list(S, X) { x }
