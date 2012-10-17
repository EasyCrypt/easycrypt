%{
open EcUtil
open AstYacc

let error pos msg = raise (ParseError (pos, msg))

let exp_bool    b          = Ast.Ecnst  (Ast.Ebool b)
let exp_int     x          = Ast.Ecnst  (Ast.Eint x)
let exp_var     v          = Ast.Ebase  (Eident v)
let exp_rnd     v          = Ast.Ernd   v
let exp_pair    x y        = Ast.Epair  (x :: y)
let exp_if      c e1 e2    = Ast.Eif    (c, e1, e2)
let exp_app     fname args = Ast.Eapp   (fname, args)
let mk_unop     op e       = Ast.Eapp   (op, [e])
let mk_binop    op e1 e2   = Ast.Ebase  (Ebinop (op, e1, e2))
let exp_upd_map e1 e2 e3   = Ast.Eapp   ("upd", [e1; e2; e3])
let exp_get_map e1 e2      = Ast.Eapp   ("get", [e1; e2])
let exp_proba   name e     = Ast.Ebase  (Epr(name, e))
let exp_itr     e          = Ast.Eapp   ("real_of_int", [e])
let exp_abs     e          = Ast.Eapp   ("abs", [e])
let exp_forall  p t e      = Ast.Ebase  (Eforall(p, t, e))
let exp_exists  p t e      = Ast.Ebase  (Eexists(p, t, e))
let exp_list    l          = Ast.Ebase  (Elist l)
let exp_eqvar   l          = Ast.Ebase  (Eeqvar l)
let exp_at      e n        = Ast.Ebase  (Eat(e, n))
let exp_let     x e1 e2    = Ast.Elet   (x, e1, e2)
%}

%token <int> NUM
%token <string> IDENT
%token <string * string > QFNAME
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
%token CNST
%token COLON
%token COMMA
%token COMPUTE
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
%token GAME
%token IF
%token IFF
%token IMPL
%token IN
%token INCLUDE
%token KW_AND
%token LBRACKET
%token LEFTARROW
%token LEMMA
%token LET
%token LKEY
%token LLIMP
%token LPAREN
%token MINUS
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

%type <AstYacc.p_global>    global
%type <AstYacc.prog * bool> prog

%start prog global
%%

(* -------------------------------------------------------------------- *)
%inline ident           : x=IDENT      { x };
%inline number          : n=NUM        { n };
%inline prim_ident      : x=PRIM_IDENT { x };
%inline qualif_fct_name : x=QFNAME     { x };

znumber:
| /*-*/ n=NUM {  n }
| MINUS n=NUM { -n }
;

(* -------------------------------------------------------------------- *)
%inline ident_list1: aout=plist1(ident, COMMA) { aout };
%inline ident_list0: aout=plist0(ident, COMMA) { aout };

%inline p_ident_list1: aout=plist1(loc(ident), COMMA) { aout };

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
     if n <> 1 && n <> 2 then
       error
         (pos_of_lex_pos $startpos(n) $endpos(n))
         "variable side must be 1 or 2"
     else
       n
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

simpl_exp:
| TRUE                                   { exp_bool true }
| FALSE                                  { exp_bool false }
| n=number                               { exp_int n }
| x=ident                                { exp_var x }
| se=loc(simpl_exp) LBRACKET e=loc(exp) RBRACKET
                                         { exp_get_map se e }
| se=loc(simpl_exp)
    LBRACKET e1=loc(exp) LEFTARROW e2=loc(exp) RBRACKET
                                         { exp_upd_map se e1 e2 }
| x=ident LPAREN es=p_exp_list0 RPAREN   { exp_app x es }
| e=loc(simpl_exp) LKEY s=prog_num RKEY  { exp_at e s }
| se=loc(simpl_exp) ROI                  { exp_itr se }
| f=qualif_fct_name LBRACKET e=loc(exp) RBRACKET
                                         { exp_proba f e }
| LPAREN e=loc(exp) COMMA es=p_exp_list1 RPAREN
                                         { exp_pair e es }
| LPAREN e=exp RPAREN                    { e }
| LBRACKET es=p_exp_sm_list0 RBRACKET    { exp_list es }
| EQ LKEY xs=p_ident_list1 RKEY          { exp_eqvar xs }
| PIPE e=loc(exp) PIPE                   { exp_abs e }
| se=loc(simpl_exp) s=prog_num           { exp_at se s }
;

exp:
| NOT   e=loc(exp)                      { mk_unop "!" e }
| MINUS e=loc(exp) %prec prec_prefix_op { mk_unop "-" e }

| e1=loc(exp)    IMPL  e2=loc(exp)  { mk_binop "=>"  e1 e2 }
| e1=loc(exp)    IFF   e2=loc(exp)  { mk_binop "<=>" e1 e2 }
| e1=loc(exp)    OR    e2=loc(exp)  { mk_binop "||"  e1 e2 }
| e1=loc(exp)    AND   e2=loc(exp)  { mk_binop "&&"  e1 e2 }
| e1=loc(exp)    EQ    e2=loc(exp)  { mk_binop "="   e1 e2 }
| e1=loc(exp)    NE    e2=loc(exp)  { mk_binop "<>"  e1 e2 }
| e1=loc(exp) op=OP1   e2=loc(exp)  { mk_binop op    e1 e2 }
| e1=loc(exp) op=OP2   e2=loc(exp)  { mk_binop op    e1 e2 }
| e1=loc(exp)    MINUS e2=loc(exp)  { mk_binop "-"   e1 e2 }
| e1=loc(exp) op=OP3   e2=loc(exp)  { mk_binop op    e1 e2 }
| e1=loc(exp)    STAR  e2=loc(exp)  { mk_binop "*"   e1 e2 }
| e1=loc(exp) op=OP4   e2=loc(exp)  { mk_binop op    e1 e2 }

| c=loc(exp) QUESTION e1=loc(exp) COLON e2=loc(exp) %prec OP2 { exp_if c e1 e2 }
| IF c=loc(exp) THEN e1=loc(exp) ELSE e2=loc(exp)             { exp_if c e1 e2 }

| FORALL pd=param_decl t=triggers? COMMA e=loc(exp) { exp_forall pd (unopt [] t) e }
| EXIST  pd=param_decl t=triggers? COMMA e=loc(exp) { exp_exists pd (unopt [] t) e }

| LET xs=p_ident_list1 EQ e1=loc(exp) IN e2=loc(exp) { exp_let xs e1 e2 }

| e=simpl_exp { e }
| re=rnd_exp  { exp_rnd re }
;

(* -------------------------------------------------------------------- *)
rnd_exp:
| LKEY n1=number COMMA n2=number RKEY
    { if   n1 = 0 && n2 = 1
      then Ast.Rbool
      else error (pos_of_lex_pos $startpos $endpos) "malformed bool random" }

| LKEY n1=number COMMA n2=number RKEY_HAT e=loc(exp)
    { if   n1 = 0 && n2 = 1
      then Ast.Rbitstr e
      else error (pos_of_lex_pos $startpos $endpos) "malformed random bitstring" }

| LBRACKET e1=loc(exp) DOTDOT e2=loc(exp) RBRACKET
    { Ast.Rinter (e1, e2) }

  (* TODO : Santiago, is it needed? Can we do it with pop ? *)
| LPAREN re=rnd_exp BACKSLASH e=loc(exp) RPAREN
    { Ast.Rexcepted (re, e) }
;

(* -------------------------------------------------------------------- *)
%inline p_exp_sm_list0: aout=plist0(loc(exp), SEMICOLON) { aout }

%inline p_exp_list0: aout=plist0(loc(exp), COMMA) { aout }
%inline p_exp_list1: aout=plist1(loc(exp), COMMA) { aout }

%inline trigger: aout=plist1(loc(exp), COMMA) { aout }

%inline triggers:
| LBRACKET aout=plist1(trigger, PIPE) RBRACKET { aout }
;

(* -------------------------------------------------------------------- *)
(* Type expressions                                                     *)

simpl_type_exp:
| x=ident                     { Tbase x }
| x=prim_ident                { Tvar x }
| tya=type_args x=ident       { Tapp (tya, x) }
| BITSTR LKEY e=loc(exp) RKEY { Tbitstring e }
| LPAREN ty=type_exp RPAREN   { ty }
;

type_args:
| ty=simpl_type_exp                          { [ty] }
| LPAREN tys=plist2(type_exp, COMMA) RPAREN  { tys  }
;

type_exp:
| ty=simpl_type_exp               { ty }
| ty=plist2(simpl_type_exp, STAR) { Tpair ty }
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
| xs=p_ident_list1 COLON ty=type_exp { List.map (fun v -> (v, ty)) xs }
;

param_decl:
| LPAREN aout=plist0(typed_vars, COMMA) RPAREN { List.flatten aout }
;

(* -------------------------------------------------------------------- *)
(* Statements                                                           *)

base_instr:
| x=loc(ident) LPAREN es=p_exp_list0 RPAREN
    { Ast.Scall (Ast.Ltuple [], x, es) }

| x=loc(ident) EQ e=loc(exp)
    { Ast.Sasgn (Ast.Ltuple [x], e) }

| LPAREN xs=p_ident_list1 RPAREN EQ e=loc(exp)
    { Ast.Sasgn (Ast.Ltuple xs, e) }

| x=loc(ident) LBRACKET e1=loc(exp) RBRACKET EQ e2=loc(exp)
     { Ast.Sasgn (Ast.Lupd (x, e1), e2) }

| ASSERT LPAREN c=loc(exp) RPAREN 
     { Ast.Sassert c }
;

instr:
| bi=base_instr SEMICOLON                            { bi }
| IF LPAREN c=loc(exp) RPAREN b1=block ELSE b2=block { Ast.Sif (c, b1, b2) }
| IF LPAREN c=loc(exp) RPAREN b=block                { Ast.Sif (c, b, []) }
| WHILE LPAREN c=loc(exp) RPAREN b=block             { Ast.Swhile (c, b) }
;

block:
| i=loc(base_instr) SEMICOLON { [i] }
| LKEY stmt=stmt RKEY { stmt }
;

stmt: aout=loc(instr)* { aout }

(* -------------------------------------------------------------------- *)
(* Functions and Games                                                  *)

var_decl:
| VAR xs=p_ident_list1 COLON ty=type_exp { (xs, ty) }
;

var_decl_list:
| var_decl { [$1] }
| var_decl var_decl_list { $1::$2 }
;

(* -------------------------------------------------------------------- *)
(* Game definition                                                      *)

loc_decl:
| VAR xs=p_ident_list1 COLON ty=type_exp               SEMICOLON { (xs, ty, None  ) }
| VAR xs=p_ident_list1 COLON ty=type_exp EQ e=loc(exp) SEMICOLON { (xs, ty, Some e) }
;

ret_stmt:
| RETURN e=loc(exp) SEMICOLON { Some e }
| empty                       { None }
;

fun_def_body:
| LKEY decl=loc_decl* s=stmt rs=ret_stmt RKEY { (decl, s, rs) }
;

fun_decl:
| x=loc(ident) pd=param_decl COLON ty=type_exp { (x, pd, ty) }
;

pg_elem:
| v=var_decl
    {  PEvar v }

| FUN decl=fun_decl EQ body=fun_def_body
    { PEfun (decl, body) }

| FUN x=ident EQ qf=qualif_fct_name
    { PEredef (x, qf) }

| ABSTRACT x1=ident EQ x2=ident LKEY xs=ident_list0 RKEY
    { PEabs (x1, x2, xs) }
;

(* -------------------------------------------------------------------- *)
(* Game redefinition                                                    *)

remove_var:
| empty { [] }
| REMOVE xs=p_ident_list1 { xs }
;

add_var:
| empty { [] }
| var_decl_list { $1 }
;

var_modifier:
| remove_var add_var { ($1,$2) }
;

redef:
| x=ident EQ body=fun_def_body {  (x, body) }
;

%inline redef_conj: aout=plist1(redef, KW_AND) { aout }

(* -------------------------------------------------------------------- *)
(* Games                                                                *)

pg_body:
| LKEY loc(pg_elem)* RKEY { PGdef $2 }
| x=ident vm=var_modifier WHERE rl=redef_conj {  PGredef (x, vm, rl) }
;

pg_def:
| GAME x=ident EQ body=pg_body { (x, body) }
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
| cn=cnst_decl               { (cn, None  ) }
| cn=cnst_decl EQ e=loc(exp) { (cn, Some e) }
;

(* -------------------------------------------------------------------- *)
(* Op declarations / definitions                                        *)

%inline as_id:
| AS x=ident { x }
;

op_body:
| COLON ft=fun_type
    { OpDecl ft }

| pd=param_decl EQ e=loc(exp)
    { OpDef (pd, e) }
;

op_decl:
| OP op=op_ident body=op_body alias=as_id? { (None, 0, op, body, alias)}
;

pop_body:
| COLON ft=fun_type
    { PopDecl ft }

| pd=param_decl EQ LPAREN x=loc(ident) COLON ty=type_exp RPAREN ARROW e=loc(exp)
     { PopDef(pd, (x, ty), e) }
;

pop_decl:
| POP x=ident body=pop_body { (x, body) }
;

(* -------------------------------------------------------------------- *)
(* Predicate declarations / definitions                                 *)

pred_decl:
| PRED x=ident pd=param_decl EQ e=loc(exp) { (x, pd, e) }
;

apred_decl:
| PRED x=ident COLON dom=type_exp_pred_dom { (x, dom) }
;

(* -------------------------------------------------------------------- *)
(* Axiom and lemma declarations                                         *)

axiom:
| AXIOM x=ident COLON e=loc(exp)  { (x, true , e) }
| LEMMA x=ident COLON e=loc(exp)  { (x, false, e) }
;

(* -------------------------------------------------------------------- *)
(* Probabilistic operator specification                                 *)

pop_spec: (* two-sided *)
| AXIOM x=ident pd=param_decl COLON
     y1=loc(ident) EQ e1=loc(exp) TILD
     y2=loc(ident) EQ e2=loc(exp) COLON
     cl=equiv_concl

     { (x, true, (pd, (y1, e1, None), (y2, e2, None), cl)) }

| LEMMA x=ident pd=param_decl COLON
     y1=loc(ident) EQ e1=loc(exp) TILD
     y2=loc(ident) EQ e2=loc(exp) COLON
     cl=equiv_concl

     { (x, false, (pd, (y1, e1, None), (y2, e2, None), cl)) }

  (* relational prob. operator specification + assert *)
| AXIOM x=ident pd=param_decl COLON
      y1=loc(ident) EQ e1=loc(exp) SEMICOLON ASSERT LPAREN ea1=loc(exp) RPAREN TILD
      y2=loc(ident) EQ e2=loc(exp) SEMICOLON ASSERT LPAREN ea2=loc(exp) RPAREN COLON
      cl=equiv_concl

    { (x, true, (pd, (y1, e1, Some ea1), (y2, e2, Some ea2), cl)) }

  (* non-relational prob. operator specification. Used by WP. *)
%inline aspec_params: LPAREN aout=plist0(loc(ident), COMMA) RPAREN { aout }

pop_aspec:
| ASPEC x=ident pd=param_decl
    COLON y=loc(ident) EQ y_op=op_ident y_prms=aspec_params
    COLON e1=loc(exp) LLIMP e2=loc(exp)

    { (x, (pd, (y, y_op, y_prms), (e1, e2))) }


(* -------------------------------------------------------------------- *)
(* Adversary declarations                                               *)

adv_decl:
| ADVERSARY decl=fun_decl LKEY ty=plist0(fun_type, SEMICOLON) RKEY
    { (decl, ty) }
;

(* -------------------------------------------------------------------- *)
(* Equivalences                                                         *)

upto:
| UPTO LPAREN e=loc(exp) RPAREN
    { (e, e) }

| UPTO LPAREN e1=loc(exp) RPAREN KW_AND LPAREN e2=loc(exp) RPAREN
    { (e1, e2) }
;

eager:
| EAGER b=block { b }
;

inv_info:
| LPAREN e=loc(exp) RPAREN              { AstLogic.Inv_global e }
| ut=upto                               { AstLogic.Inv_upto (ut, None) }
| ut=upto WITH LPAREN e=loc(exp) RPAREN { AstLogic.Inv_upto (ut, Some e) }
;

using:
| USING xs=ident_list1 { xs }
;

auto_info:
| info=inv_info? using=loption(using) { (info, using) }
;

auto:
| AUTO ai=auto_info { ai }
;

auto_eager:
| BY x=auto  { AstLogic.Helper_inv x }
| BY x=eager { AstLogic.Helper_eager x }
;

equiv_concl:
| e1=loc(exp) LLIMP e2=loc(exp)
    { Aequiv_spec (e1, e2, None) }

| e1=loc(exp)
    EQEQLBRACKET ei1=loc(exp) SEMICOLON ei2=loc(exp)
    RBRACKETLLIMP e2=loc(exp)

    { Aequiv_spec (e1, e2, Some (ei1, ei2))  }

| ivi=inv_info
    { Aequiv_inv ivi }
;

equiv:
| EQUIV x=ident
    COLON f1=qualif_fct_name TILD f2=qualif_fct_name
    COLON ec=equiv_concl at=auto_eager?

    { (x, f1, f2, ec, at) }
;

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

%inline ident_exp:
| x=ident COMMA e=loc(exp) { (x,e) }
;

real_hint:
| USING x=ident { Husing x }
| ADMIT         { Hadmit }
| COMPUTE       { Hcompute }
| COMPUTE n=NUM e1=loc(exp) COMMA e2=loc(exp) 
                { Hfailure (n, e1, e2, []) }
| COMPUTE n=NUM e1=loc(exp) COMMA e2=loc(exp) COLON l=plist1(ident_exp,COLON) 
                { Hfailure (n, e1, e2, l) }
| SPLIT         { Hsplit }
| SAME          { Hsame }
| AUTO          { Hauto }
| empty         { Hnone }
;

claim:
| PR x=ident COLON e=loc(exp) h=real_hint { (x, (e, h)) }
;

(* -------------------------------------------------------------------- *)
(* Tactics                                                              *)

at_pos:
| empty              { AstLogic.At_empty  }
| AT ns=number_list1 { AstLogic.At_pos ns }
| LAST               { AstLogic.At_last   }
;

inline_info:
| p=at_pos       { AstLogic.IKat  p  }
| xs=ident_list1 { AstLogic.IKfct xs }
;

rnd_info:
| pr=backw_or_forw LPAREN e1=loc(exp) RPAREN COMMA LPAREN e2=loc(exp) RPAREN
     { pr, AstLogic.RIpara (AstLogic.RIbij ((None, e1), (None, e2))) }

| pr=backw_or_forw
    LPAREN x1=ident ARROW e1=loc(exp) RPAREN COMMA
    LPAREN x2=ident ARROW e2=loc(exp) RPAREN

    { pr, AstLogic.RIpara (AstLogic.RIbij ((Some x1, e1), (Some x2, e2))) }

| pr=backw_or_forw LPAREN e=loc(exp) RPAREN
    { pr, AstLogic.RIpara (AstLogic.RIidempotant (None, e)) }

| pr=backw_or_forw LPAREN x=ident ARROW e=loc(exp) RPAREN
    { pr, AstLogic.RIpara (AstLogic.RIidempotant (Some x, e)) }

| pr=backw_or_forw
     { pr, AstLogic.RIpara AstLogic.RIid }

| n=prog_num pr=backw_or_forw {
    match n with
    | 1 -> (pr, AstLogic.RIdisj ApiTypes.Left )
    | 2 -> (pr, AstLogic.RIdisj ApiTypes.Right)
    | _ -> assert false
  }
;

interval:
| LBRACKET n1=number MINUS n2=number RBRACKET {
    if n2 < n1 then
      user_error "[interval [%d:%d] is empty" n1 n2;
    (n1, n2 - n1 + 1)
  }

| n=number { (n, 1) }
;

backw_or_forw :
| empty     { AstLogic.Backwards }
| BACKWARDS { AstLogic.Backwards }
| FORWARDS  { AstLogic.Forwards  }
;

tactic:
| IDTAC                       { AstLogic.Tidtac }
| CALL a=auto_info            { AstLogic.Tcall a }
| INLINE s=side i=inline_info { AstLogic.Tinline (s, i) }
| ASSIGN                      { AstLogic.Tasgn }
| RANDOM ri=rnd_info          { AstLogic.Trnd ri }

| SWAP side interval znumber
     { AstLogic.Tswap($2, AstLogic.SKswap(fst $3 - 1, snd $3, $4)) }


| SWAP side znumber {
       if $3 < 0 then AstLogic.Tswap($2,AstLogic.SKpop (-$3))
       else AstLogic.Tswap($2,AstLogic.SKpush $3) }

| SIMPL                        { AstLogic.Tsimplify_post }
| TRIVIAL                      { AstLogic.Ttrivial }
| a=auto                       { AstLogic.Tauto a }
| DERANDOMIZE s=side           { AstLogic.Tderandomize s }
| WP                           { AstLogic.Twp None }
| WP n1=number n2=number       { AstLogic.Twp (Some (n1, n2)) }
| SP                           { AstLogic.Tsp None }
| SP n1=number n2=number       { AstLogic.Tsp (Some (n1, n2)) }
| CASE s=side COLON e=loc(exp) { AstLogic.Tcase (s, e) }
  (* TODO change the keywords *)
| IF s=side                    { AstLogic.Tif s }
| IFSYNC n1=number n2=number   { AstLogic.Tifsync (Some (n1, n2)) }
| IFSYNC                       { AstLogic.Tifsync None }
| IFNEG s=side p=at_pos        { AstLogic.Tifneg (s, p) }
| AUTOSYNC                     { AstLogic.Tautosync }
| CONDT s=side p=at_pos        { AstLogic.Treduce(s, p, true) }
| CONDF s=side p=at_pos        { AstLogic.Treduce(s, p, false) }

| EQOBSIN
     LPAREN e1=loc(exp) RPAREN
     LPAREN e2=loc(exp) RPAREN
     LPAREN e3=loc(exp) RPAREN
     us=using
    { AstLogic.Teqobsin (e1, e2, e3, us) }

  (* TODO change the keywords *)
| WHILE s=side pr=backw_or_forw COLON e=loc(exp)
    { AstLogic.Twhile(s, pr, e, None) }

| WHILE s=side pr=backw_or_forw COLON e=loc(exp) COLON e1=loc(exp) COMMA e2=loc(exp)
     { if s = ApiTypes.Both then
         error
           (pos_of_lex_pos $startpos $endpos)
           "variant expression not allowed";
       AstLogic.Twhile (s, pr, e, Some (e1, e2)) }

| WHILE
     e1=loc(exp) COMMA e2=loc(exp) COMMA e3=loc(exp) COMMA
     e4=loc(exp) COMMA e5=loc(exp) COLON e=loc(exp)
      { AstLogic.TwhileApp (e1, e2, e3, e4, e5, e) }

| WHILE x=loc(ident)
    ARROW e1=loc(exp) COMMA e2=loc(exp) COMMA e3=loc(exp)
    COMMA n1=number   COMMA n2=number
    COLON ef=loc(exp)
    COLON ef1=loc(exp) COMMA ef2=loc(exp)
    { AstLogic.TwhileAppGen (x, e1, e2, e3, n1, n2, ef, ef1, ef2) }

(*
| WHILE COLON pos_fol COLON
    LPAREN loc(ident) ARROW loc(exp) COMMA loc(exp) COMMA loc(exp) COMMA number
    COMMA number RPAREN
    LPAREN loc(exp) COMMA loc(exp) RPAREN
    { AstLogic.TwhileAppGen ($6,$8,$10,$12,$14,$16,$19,$21,$3) }
*)

| APPLY s=side COLON x=loc(ident) LPAREN es=p_exp_list0 RPAREN
    { AstLogic.Tpopspec(s, x, es) }

  (* TODO merge the two keywords *)
| PRHL  { AstLogic.Tprhl  }
| APRHL { AstLogic.Taprhl }

| UNROLL s=side p=at_pos { AstLogic.Tunroll (s, p) }

| SPLITWHILE s=side p=at_pos COLON e=loc(exp) { AstLogic.Tsplitwhile (s, p, e) }

| APP n1=number n2=number e=loc(exp) { AstLogic.Tapp(n1, n2, e, None) }

| APP n1=number n2=number e=loc(exp)
    COLON te1=loc(exp)  COMMA te2=loc(exp)
    COLON te1p=loc(exp) COMMA te2p=loc(exp)

    { AstLogic.Tapp(n1, n2, e, Some (te1, te2, te1p, te2p)) }

| TRY ta=tactics                { AstLogic.Ttry ta }
| STAR ta=tactics               { AstLogic.Trepeat ta }
| NOT n=number ta=tactics       { AstLogic.Tdo(n, ta) }
| ADMIT                         { AstLogic.Tadmit }
| UNFOLD xs=ident_list0         { AstLogic.Tunfold xs }

| LET s=side p=at_pos x=loc(ident) COLON ty=type_exp EQ e=loc(exp)
    { AstLogic.Tset (s, p, x, ty, e) }
;

tactic_part:
| tc=tactic
    { tc }

| LPAREN tc=tactics RPAREN
    { tc }

| LBRACKET tc=plist1(tactics?, PIPE) RBRACKET
    { AstLogic.Tsubgoal (List.map (unopt AstLogic.Tidtac) tc) }
;

tactic_parts:
| t=tactic_part { t }
| t=tactic_part SEMICOLON ts=tactic_parts { AstLogic.Tseq(t, ts) }
;

tactics_sentence:
| t=tactic { t }
| t=tactic SEMICOLON ts=tactic_parts { AstLogic.Tseq(t, ts) }
;

tactics:
| t=tactic { t }
| LPAREN ts=tactics_sentence RPAREN { ts }
;

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

setunset:
| SET   xs=ident_list1 { (true , xs) }
| UNSET xs=ident_list1 { (false, xs) }
;

check:
| CHECK x=ident { x }
| CHECK o=binop { o }
;

print:
| PRINT x=ident            { Pi_string x }
| PRINT op=binop           { Pi_string op }
| PRINT qf=qualif_fct_name { Pi_fct qf }
| PRINT SET                { Pi_set_axiom true }
| PRINT UNSET              { Pi_set_axiom false }
| PRINT AXIOM              { Pi_all_axiom }
| PRINT OP                 { Pi_all_op }
| PRINT CNST               { Pi_all_cnst }
| PRINT PRED               { Pi_all_pred }
| PRINT TYPE               { Pi_all_type }

setunset_all:
| UNSET ALL { false }
| SET   ALL { true }
;

%inline prover:
| x=ident  { x }
| s=STRING { s }
;

%inline prover_list:
| aout=plist1(prover, COMMA) { aout }
;

global_:
| INCLUDE s=STRING                       { Ginclude s }
| pg_def                                 { Ggame $1 }
| type_decl_or_def                       { Gtype $1 }
| cnst_decl_or_def                       { Gcnst $1 }
| opd=loc(op_decl)                       { let l, opd = opd in Gop (l, opd) }
| pop_decl                               { Gpop $1 }
| pred_decl                              { Gpred $1 }
| apred_decl                             { Gapred $1 }
| axiom                                  { Gaxiom $1 }
| pop_spec                               { Gpop_spec $1 }
| pop_aspec                              { Gpop_aspec $1 }
| adv_decl                               { Gadv $1 }
| equiv                                  { Gequiv $1 }
| claim                                  { Gclaim $1  }
| tactics_sentence                       { Gtactic $1 }
| SAVE                                   { Gsave }
| ABORT                                  { Gabort }
| setunset_all                           { Gset_all $1 }
| setunset                               { Gset $1 }
| PROVER pl=prover_list                  { Gprover pl }
| CHECKPROOF                             { Gwithproof }
| TRANSPARENT xs=ident_list1             { Gopacity(false, xs) }
| OPAQUE xs=ident_list1                  { Gopacity(true , xs) }
| UNDO n1=number n2=number x=ident m1=number m2=number
                                         { Gundo (n1, n2, x, m1, m2)}
| TIMEOUT n=number                       { Gtimeout n }
| ck=check                               { Gcheck ck }
| pr=print                               { Gprint pr }
;

stop:
| EOF { }
| DROP DOT { }
;

global:
| g=loc(global_) DOT { g }
;

prog:
| g=global { ([g], false) }
| stop     { ([ ], true ) }
| error    { error (pos_of_lex_pos $startpos $endpos) "" }
;

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X { (pos_of_lex_pos $startpos $endpos, x) }
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
