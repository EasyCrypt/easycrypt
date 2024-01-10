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
%token LARROW
%token LBRACKET
%token LET
%token LPAREN
%token LT
%token IN
%token PIPE
%token QMARK
%token RARROW
%token RBRACKET
%token RPAREN

%token<string> IDENT
%token<int>    NUMBER

%type <Ptree.pprogram> program

%start program

%nonassoc below_TERNARY
%left QMARK
%left COLON

%%

%inline vname:
| x=loc(IDENT)
    { x }

%inline wname:
| x=vname t=wtype
    { (x, t) }

%inline wtype_:
| AT x=NUMBER
    { `W x }

%inline wtype:
| w=loc(wtype_) { w }

fname_:
| f=loc(IDENT)
    { (f, None) }

| f=loc(IDENT) p=angled(list0(loc(NUMBER), COMMA))
    { (f, Some (List.map (Lc.map (fun x -> `W x)) p)) }

%inline fname:
| f=loc(fname_) { f }

sexpr_:
| f=fname
    { PEFName f }

| f=fname args=parens(list0(loc(earg), COMMA))
    { PEApp (f, args) }

| e=parens(expr)
    { PEParens e }

| i=NUMBER
    { PEInt (i, None) }

| i=NUMBER w=wtype
    { PEInt (i, Some w) }

%inline sexpr:
| e=loc(sexpr_) { e }

expr_:
| e=sexpr_
    { e }

| FUN args=wname* DOT body=expr %prec below_TERNARY
    { PEFun (args, body) }

| LET x=loc(IDENT) args=parens(list0(wname, COMMA))? EQUAL e1=expr IN e2=expr %prec below_TERNARY
    { PELet ((x, args, e1), e2) }

| e=sexpr LBRACKET
    s=ioption(AT s=expr PIPE { s }) i=expr j=prefix(COLON, expr)?
  RBRACKET
    { PESlice (e, (i, j, s)) }

| e=sexpr LBRACKET
    s=ioption(AT s=expr PIPE { s }) i=expr j=prefix(COLON, expr)?
    LARROW r=expr
  RBRACKET
    { PEAssign (e, (i, j, s), r) }

| c=expr QMARK e1=expr COLON e2=expr
    { PECond (c, (e1, e2)) }

%inline expr:
| e=loc(expr_) { e }

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
    { raise (ParseError (Lc.of_positions (fst $loc) (snd $loc))) }

%inline parens(X):
| LPAREN x=X RPAREN { x }

%inline angled(X):
| LT x=X GT { x }

%inline list0(X, S):
| x=separated_list(S, X) { x }

%inline prefix(S, X):
| S x=X { x }

%inline loc(X):
| data=X {
    let range = Lc.of_positions $startpos $endpos in
    { range; data; }
  }
