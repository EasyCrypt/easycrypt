%{
  open Parsetree
  open Lparsetree
  let error pos msg = failwith msg

  let pos_of_lex_pos _ _ = ()

  let mk_mod ?isig name body = {
    m_name         = name;
    m_subinterface = isig;
    m_body         = body;
  }

%}

%token <int> NUM
%token <string> IDENT
%token <string> PRIM_IDENT
%token <string> STRING

(* Tokens + keywords *)
%token ABSTRACT
%token ADMIT
%token ADVERSARY
%token AND
%token ARROW
%token AS
%token ASPEC
%token ASSERT
%token AXIOM
%token BACKSLASH
%token BITSTR
%token CHECKPROOF
%token CLAIM
%token CNST
%token COLON
%token COMMA
%token COMPUTE
%token DCOLON
%token DOT
%token DOTDOT
%token DROP
%token ELSE
%token EOF
%token EQ
%token EQEQLBRACKET
%token EQUIV
%token EXIST
%token FALSE
%token FORALL
%token FUN
%token IF
%token IFF
%token IMPL
%token IN
%token INCLUDE
%token INTERFACE
%token KW_AND
%token LBRACKET
%token LEFTARROW
%token LEMMA
%token LET
%token LKEY
%token LLIMP
%token LPAREN
%token MINUS
%token MODULE
%token NE
%token NOT
%token OP
%token OR
%token PIPE
%token POP
%token PR
%token PRED
%token PROVER
%token QUESTION
%token RBRACKET
%token RBRACKETLLIMP
%token REMOVE
%token RETURN
%token RKEY
%token RKEY_HAT
%token ROI
%token RPAREN
%token SAME
%token SEMICOLON
%token SET
%token SPLIT
%token STAR
%token THEN
%token TILD
%token TRUE
%token TYPE
%token UNSET
%token UPTO
%token USING
%token VAR
%token WHERE
%token WHILE
%token WITH

(* Tactics *)
%token ABORT
%token ALL
%token APP
%token APPLY
%token APRHL
%token ASSIGN
%token AT
%token AUTO
%token AUTOSYNC
%token BACKWARDS
%token BY
%token CALL
%token CASE
%token CHECK
%token CONDF
%token CONDT
%token DERANDOMIZE
%token EAGER
%token EQOBSIN
%token FORWARDS
%token IDTAC
%token IFNEG
%token IFSYNC
%token INLINE
%token LAST
%token OPAQUE
%token PRHL
%token PRINT
%token RANDOM
%token SAVE
%token SIMPL
%token SP
%token SPLITWHILE
%token SWAP
%token TIMEOUT
%token TRANSPARENT
%token TRIVIAL
%token TRY
%token UNDO
%token UNFOLD
%token UNROLL
%token WP

%token <string> OP1 OP2 OP3 OP4

%nonassoc COMMA ELSE

%nonassoc IN
%right IMPL IFF
%right OR
%right AND

%nonassoc NOT
%left EQ NE OP1

%right QUESTION
%left OP2 MINUS
%left OP3 STAR
%left OP4

%nonassoc prec_prefix_op
%nonassoc RKEY_HAT

%type <Parsetree.global> global
%type <Parsetree.prog * bool> prog

%start prog global
%%

(* -------------------------------------------------------------------- *)
%inline ident      : x=IDENT               { x };
%inline number     : n=NUM                 { n };
%inline prim_ident : x=PRIM_IDENT          { x };

namespace:
| x=ident { [x] }
| x=ident DCOLON np=namespace { x :: np }
;

qident:
| np=namespace DOT x=ident { (np, x) }
;

znumber:
| /*-*/ n=NUM {  n }
| MINUS n=NUM { -n }
;

(* -------------------------------------------------------------------- *)
%inline ident_list1: aout=plist1(ident, COMMA) { aout };
%inline ident_list0: aout=plist0(ident, COMMA) { aout };

%inline prim_ident_list1: aout=plist1(prim_ident, COMMA) { aout };

%inline number_list1: aout=plist1(number, COMMA) { aout };

(* -------------------------------------------------------------------- *)
%inline binop:
| EQ     { "="  }
| MINUS  { "-"  }
| AND    { "&&" }
| OR     { "||" }
| STAR   { "*"  }
| x=OP1  { x    }
| x=OP2  { x    }
| x=OP3  { x    }
| x=OP4  { x    }
;

(* -------------------------------------------------------------------- *)
prog_num:
| LKEY n=number RKEY {
    match n with
      | 1 -> `Left
      | 2 -> `Right
      | _ -> error
               (pos_of_lex_pos $startpos(n) $endpos(n))
               "variable side must be 1 or 2"
  }
;

side:
| prog_num { if $1 = 1 then ApiTypes.Left else ApiTypes.Right }
| empty { ApiTypes.Both }


op_ident:
| x=IDENT { (false, x) }
| LBRACKET op=binop RBRACKET { (true, op) }
;

(* -------------------------------------------------------------------- *)
(* Expressions: program expression, logical formula and real expression *)

lpattern:
| x=ident { LPSymbol x }
| LPAREN p=plist2(ident, COMMA) RPAREN { LPTuple p }
;

simpl_exp:
| TRUE                                   { PEbool true  }
| FALSE                                  { PEbool false }
| n=number                               { PEint n }
| x=ident                                { PEident ([], x) }
| se=simpl_exp LBRACKET e=exp RBRACKET   { PEapp (qsymb_of_symb "<get>", [se; e]) }
| se=simpl_exp LBRACKET e1=exp LEFTARROW e2=exp RBRACKET
                                         { PEapp (qsymb_of_symb "<set>", [se; e1; e2]) }
| x=ident LPAREN es=exp_list0 RPAREN     { PEapp (qsymb_of_symb x, es) }
| x=ident LKEY s=prog_num RKEY           { PErelvar (x, s) }
| LPAREN es=exp_list2 RPAREN             { PEtuple es }
| LPAREN e=exp RPAREN                    { e }
| LBRACKET es=p_exp_sm_list0 RBRACKET    { PElist es }
;

exp:
| NOT   e=exp                      { PEapp (qsymb_of_symb "!", [e]) }
| MINUS e=exp %prec prec_prefix_op { PEapp (qsymb_of_symb "-", [e]) }

| e1=exp    IMPL  e2=exp  { PEapp (qsymb_of_symb "=>" , [e1; e2]) }
| e1=exp    IFF   e2=exp  { PEapp (qsymb_of_symb "<=>", [e1; e2]) }
| e1=exp    OR    e2=exp  { PEapp (qsymb_of_symb "||" , [e1; e2]) }
| e1=exp    AND   e2=exp  { PEapp (qsymb_of_symb "&&" , [e1; e2]) }
| e1=exp    EQ    e2=exp  { PEapp (qsymb_of_symb "="  , [e1; e2]) }
| e1=exp    NE    e2=exp  { PEapp (qsymb_of_symb "<>" , [e1; e2]) }
| e1=exp op=OP1   e2=exp  { PEapp (qsymb_of_symb op   , [e1; e2]) }
| e1=exp op=OP2   e2=exp  { PEapp (qsymb_of_symb op   , [e1; e2]) }
| e1=exp    MINUS e2=exp  { PEapp (qsymb_of_symb "-"  , [e1; e2]) }
| e1=exp op=OP3   e2=exp  { PEapp (qsymb_of_symb op   , [e1; e2]) }
| e1=exp    STAR  e2=exp  { PEapp (qsymb_of_symb "*"  , [e1; e2]) }
| e1=exp op=OP4   e2=exp  { PEapp (qsymb_of_symb op   , [e1; e2]) }

| c=exp QUESTION e1=exp COLON e2=exp %prec OP2 { PEif (c, e1, e2) }
| IF c=exp THEN e1=exp ELSE e2=exp             { PEif (c, e1, e2) }

| LET p=lpattern EQ e1=exp IN e2=exp { PElet (p, e1, e2) }

| e=simpl_exp { e }
| re=rnd_exp  { PErnd re }
;



(* -------------------------------------------------------------------- *)
rnd_exp:
| LKEY n1=number COMMA n2=number RKEY
    { if   n1 = 0 && n2 = 1
      then PRbool
      else error (pos_of_lex_pos $startpos $endpos) "malformed bool random" }

| LKEY n1=number COMMA n2=number RKEY_HAT e=exp
    { if   n1 = 0 && n2 = 1
      then PRbitstr e
      else error (pos_of_lex_pos $startpos $endpos) "malformed random bitstring" }

| LBRACKET e1=exp DOTDOT e2=exp RBRACKET
    { PRinter (e1, e2) }

| LPAREN re=rnd_exp BACKSLASH e=exp RPAREN
    { PRexcepted (re, e) }
;

(* -------------------------------------------------------------------- *)
%inline p_exp_sm_list0: aout=plist0(exp, SEMICOLON) { aout }

%inline exp_list0: aout=plist0(exp, COMMA) { aout }
%inline exp_list1: aout=plist1(exp, COMMA) { aout }
%inline exp_list2: aout=plist2(exp, COMMA) { aout }

%inline trigger: aout=plist1(exp, COMMA) { aout }

%inline triggers:
| LBRACKET aout=plist1(trigger, PIPE) RBRACKET { aout }
;

(* -------------------------------------------------------------------- *)
(* Formulas                                                             *)
form:
| NOT   e=form              { PFapp (qsymb_of_symb "!", [e]) }
| e1=form    IMPL  e2=form  { PFapp (qsymb_of_symb "=>" , [e1; e2]) }
| e1=form    IFF   e2=form  { PFapp (qsymb_of_symb "<=>", [e1; e2]) }
| e1=form    OR    e2=form  { PFapp (qsymb_of_symb "||" , [e1; e2]) }
| e1=form    AND   e2=form  { PFapp (qsymb_of_symb "&&" , [e1; e2]) }
| e1=form    EQ    e2=form  { PFapp (qsymb_of_symb "="  , [e1; e2]) }
| e1=form    NE    e2=form  { PFapp (qsymb_of_symb "<>" , [e1; e2]) }
| IF c=form  THEN  e1=form ELSE e2=form             
                            { PFif (c, e1, e2) }
| LET p=lpattern EQ e1=form IN e2=form 
                            { PFlet (p, e1, e2) }
| e=simpl_exp               { PFexpr e }
| FORALL pd=param_decl COMMA e=form { PFforall(pd, e) }
| EXIST  pd=param_decl COMMA e=form { PFexists(pd,e) }
;



(* -------------------------------------------------------------------- *)
(* Type expressions                                                     *)

simpl_type_exp:
| x=ident                   { Pnamed x }
| x=prim_ident              { Pvar x }
| tya=type_args x=ident     { Papp (x, tya) }
| BITSTR LKEY e=exp RKEY    { Pbitstring e }
| LPAREN ty=type_exp RPAREN { ty }
;

type_args:
| ty=simpl_type_exp                          { [ty] }
| LPAREN tys=plist2(type_exp, COMMA) RPAREN  { tys  }
;

type_exp:
| ty=simpl_type_exp               { ty }
| ty=plist2(simpl_type_exp, STAR) { Ptuple ty }
;

type_exp_dom:
| LPAREN RPAREN                             { [  ] }
| ty=type_exp                               { [ty] }
| LPAREN tys=plist2(type_exp, COMMA) RPAREN { tys  }
;

type_exp_pred_dom:
| LPAREN RPAREN                             { [  ] }
| ty=type_exp                               { [ty] }
| LPAREN tys=plist2(type_exp, COMMA) RPAREN { tys  }
;

fun_type:
| dom=type_exp_pred_dom ARROW codom=type_exp { (dom, codom) }
;

(* -------------------------------------------------------------------- *)
(* Parameter declarations                                              *)

typed_vars:
| xs=ident_list1 COLON ty=type_exp { List.map (fun v -> (v, ty)) xs }
;

param_decl:
| LPAREN aout=plist0(typed_vars, COMMA) RPAREN { List.flatten aout }
;

(* -------------------------------------------------------------------- *)
(* Statements                                                           *)

lvalue:
| x=qident                              { LVSymbol x      }
| LPAREN p=plist2(qident, COMMA) RPAREN { LVTuple  p      }
| x=qident LBRACKET e=exp RBRACKET      { LVMap    (x, e) }
;

rvalue:
| e=exp                               { `Expr e }
| x=qident LPAREN es=exp_list0 RPAREN { `Call (x, es) }
;

base_instr:
| f=qident LPAREN es=exp_list0 RPAREN
    { Scall (f, es) }

| x=lvalue EQ e=rvalue
    { Sasgn (x, e) }

| ASSERT LPAREN c=exp RPAREN 
     { Sassert c }
;

instr:
| bi=base_instr SEMICOLON                       { bi }
| IF LPAREN c=exp RPAREN b1=block ELSE b2=block { Sif (c, b1, b2) }
| IF LPAREN c=exp RPAREN b =block               { Sif (c, b , []) }
| WHILE LPAREN c=exp RPAREN b=block             { Swhile (c, b) }
;

block:
| i=base_instr SEMICOLON { [i] }
| LKEY stmt=stmt RKEY    { stmt }
;

stmt: aout=instr* { aout }

(* -------------------------------------------------------------------- *)
(* Functions                                                            *)

var_decl:
| VAR xs=ident_list1 COLON ty=type_exp { (xs, ty) }
;

var_decl_list:
| var_decl { [$1] }
| var_decl var_decl_list { $1::$2 }
;

(* -------------------------------------------------------------------- *)
(* Module definition                                                    *)

loc_decl:
| VAR xs=ident_list1 COLON ty=type_exp          SEMICOLON { (xs, ty, None  ) }
| VAR xs=ident_list1 COLON ty=type_exp EQ e=exp SEMICOLON { (xs, ty, Some e) }
;

ret_stmt:
| RETURN e=exp SEMICOLON { Some e }
| empty                  { None }
;

fun_def_body:
| LKEY decl=loc_decl* s=stmt rs=ret_stmt RKEY
    { { fb_locals = decl;
        fb_body   = s   ;
        fb_return = rs  ; }
    }
;

fun_decl:
| x=ident pd=param_decl COLON ty=type_exp
    { { fd_name     = x ;
        fd_tyargs   = pd;
        fd_tyresult = ty; }
    }
;

mod_item:
| v=var_decl
    { PEVar v }

| m=mod_def
    { PEMod m }

| FUN decl=fun_decl EQ body=fun_def_body
    { PEFun (decl, body) }

| FUN x=ident EQ qf=qident
    { PERedef (x, qf) }
;

(* -------------------------------------------------------------------- *)
(* Modules                                                              *)

mod_body:
| LKEY mod_item* RKEY { $2 }
;

mod_def:
| MODULE x=ident EQ body=mod_body { mk_mod x body }
| MODULE x=ident COLON i=ident EQ body=mod_body { mk_mod ~isig:i x body }
;

(* -------------------------------------------------------------------- *)
(* Modules interfaces                                                   *)

sig_elem:
| FUN decl=fun_decl { `FunctionDecl decl }
;

sig_body:
| x=sig_elem* { { s_context = x } }
;

sig_def:
| MODULE INTERFACE x=ident EQ LKEY body=sig_body RKEY {
    { i_name      = x;
      i_signature = body; }
  }
;

(* -------------------------------------------------------------------- *)
(* Types declarations / definitions                                     *)

poly_type_decl:
| empty                              { []  }
| x=prim_ident                       { [x] }
| LPAREN xs=prim_ident_list1 RPAREN  { xs  }
;

type_decl:
| TYPE tydecl=poly_type_decl x=ident { (tydecl, x) }
;

type_decl_or_def:
| type_decl { ($1,None) }
| type_decl EQ type_exp { ($1, Some $3) }
;

(* -------------------------------------------------------------------- *)
(* Constant declarations / definitions                                  *)

cnst_decl:
| CNST xs=ident_list1 COLON ty=type_exp { (xs, ty) }
;

cnst_decl_or_def:
| cn=cnst_decl          { (cn, None  ) }
| cn=cnst_decl EQ e=exp { (cn, Some e) }
;

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

%inline ident_exp:
| x=ident COMMA e=exp { (x, e) }
;

real_hint:
| USING x=ident { Husing x }
| ADMIT         { Hadmit }
| COMPUTE       { Hcompute }
| COMPUTE n=NUM e1=exp COMMA e2=exp 
                { Hfailure (n, e1, e2, []) }
| COMPUTE n=NUM e1=exp COMMA e2=exp COLON l=plist1(ident_exp, COLON) 
                { Hfailure (n, e1, e2, l) }
| SPLIT         { Hsplit }
| SAME          { Hsame }
| AUTO          { Hauto }
| empty         { Hnone }
;

claim:
| CLAIM x=ident COLON e=exp h=real_hint { (x, (e, h)) }
;

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

global_:
| mod_def          { Gmodule    $1 }
| sig_def          { Ginterface $1 }
| type_decl_or_def { Gtype      $1 }
| cnst_decl_or_def { Gcnst      $1 }
| claim            { Gclaim     $1 }
;

stop:
| EOF { }
| DROP DOT { }
;

global:
| g=global_ DOT { g }
;

prog:
| g=global { ([g], false) }
| stop     { ([ ], true ) }
| error    { error (pos_of_lex_pos $startpos $endpos) "" }
;

(* -------------------------------------------------------------------- *)
%inline plist0(X, S):
| aout=separated_list(S, X) { aout }
;

%inline plist1(X, S):
| aout=separated_nonempty_list(S, X) { aout }
;

%inline plist2(X, S):
| x=X S xs=plist1(X, S) { x :: xs }
;

%inline empty:
| /**/ { () }
;
