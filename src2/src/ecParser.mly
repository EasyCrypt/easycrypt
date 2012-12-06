%{
  open EcParsetree

  let error pos msg =
    let msg =
      Printf.sprintf "%s: %s" (Location.tostring pos) msg
    in
      failwith msg

  let mk_mod ?modtype params body = Pm_struct {
    ps_params    = params;
    ps_signature = modtype;
    ps_body      = body;
  }

  let mk_tydecl (tyvars, name) body = {
    pty_name   = name;
    pty_tyvars = tyvars;
    pty_body   = body;
  }

  let peget e1 e2    = PEapp (([], "get"), [e1; e2])
  let peset e1 e2 e3 = PEapp (([], "set"), [e1; e2; e3])

  let penil  ()   = PEapp (EcPath.toqsymbol EcCoreLib.nil , [])
  let pecons e es = PEapp (EcPath.toqsymbol EcCoreLib.cons, [e; es])

  let pelist (es : pexpr    list) : pexpr_r    = assert false
  let pflist (es : pformula    list)  : pformula_r    = assert false
%}

%token <int> NUM
%token <string> IDENT
%token <string> PRIM_IDENT
%token <string> STRING

(* Tokens + keywords *)
// %token ABSTRACT
%token UNDERSCORE
%token ADMIT
// %token ADVERSARY
%token AND
%token ARROW
// %token AS
// %token ASPEC
%token ASSERT
%token AXIOM
%token LEMMA
%token BACKSLASH
%token BITSTR
// %token CHECKPROOF
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
%token END
%token EOF
%token EQ
// %token EQEQLBRACKET
// %token EQUIV
%token EXIST
%token FALSE
%token FORALL
%token FUN
%token IF
%token IFF
%token IMPL
%token IMPORT
%token IN
// %token INCLUDE
// %token INTERFACE
// %token KW_AND
%token LBRACKET
%token LEFTARROW
// %token LEMMA
%token LET
%token LKEY
// %token LLIMP
%token LPAREN
%token MINUS
%token MODULE
%token NE
%token NOT
%token OP
%token OR
%token PIPE
%token POP
// %token PR
%token PRED
// %token PROVER
%token QUESTION
%token RBRACKET
// %token RBRACKETLLIMP
// %token REMOVE
%token RETURN
%token REQUIRE
%token RKEY
%token RKEY_HAT
// %token ROI
%token RPAREN
%token SAME
%token SEMICOLON
// %token SET
%token SPLIT
%token STAR
%token THEN
%token THEORY
// %token TILD
%token TRUE
%token TYPE
// %token UNSET
// %token UPTO
%token USING
%token VAR
// %token WHERE
%token WHILE
// %token WITH

(* Tactics *)
// %token ABORT
// %token ALL
// %token APP
// %token APPLY
// %token APRHL
// %token ASSIGN
// %token AT
%token AUTO
// %token AUTOSYNC
// %token BACKWARDS
// %token BY
// %token CALL
// %token CASE
// %token CHECK
// %token CONDF
// %token CONDT
// %token DERANDOMIZE
// %token EAGER
// %token EQOBSIN
// %token FORWARDS
// %token IDTAC
// %token IFNEG
// %token IFSYNC
// %token INLINE
// %token LAST
// %token OPAQUE
// %token PRHL
// %token PRINT
// %token RANDOM
// %token SAVE
// %token SIMPL
// %token SP
// %token SPLITWHILE
// %token SWAP
// %token TIMEOUT
// %token TRANSPARENT
// %token TRIVIAL
// %token TRY
// %token UNDO
// %token UNFOLD
// %token UNROLL
// %token WP

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

%type <EcParsetree.global> global
%type <EcParsetree.prog * bool> prog

%start prog global
%%

(* -------------------------------------------------------------------- *)
%inline ident      : x=IDENT               { x };
%inline number     : n=NUM                 { n };
%inline prim_ident : x=PRIM_IDENT          { x };

qident:
| x=ident DCOLON qx=qident { (x :: fst qx, snd qx) }
| x=ident                  { ([]         , x     ) }

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
  if n > 0 then n else 
  error
    (Location.make $startpos(n) $endpos(n))
    "variable side must be greater than 0"
  }
;

side:
| prog_num { if $1 = 1 then ApiEcTypes.Left else ApiEcTypes.Right }
| empty { ApiEcTypes.Both }

(* -------------------------------------------------------------------- *)
(* Expressions: program expression, real expression                     *)

lpattern:
| x=ident { LPSymbol x }
| LPAREN p=plist2(ident, COMMA) RPAREN { LPTuple p }
;

sexp:
| TRUE                                   { PEbool true  }
| FALSE                                  { PEbool false }
| n=number                               { PEint n }
| x=qident                                { PEident x }
| se=loc(sexp) LBRACKET e=loc(exp) RBRACKET
                                         { peget se e }
| se=loc(sexp) LBRACKET e1=loc(exp) LEFTARROW e2=loc(exp) RBRACKET
                                         { peset se e1 e2 }
| x=ident LPAREN es=exp_list0 RPAREN     { PEapp (qsymb_of_symb x, es) }
| LPAREN es=exp_list2 RPAREN             { PEtuple es }
| LPAREN e=exp RPAREN                    { e }
| LBRACKET es=p_exp_sm_list0 RBRACKET    { pelist es }
;

exp:
| NOT   e=loc(exp)                      { PEapp (qsymb_of_symb "!", [e]) }
| MINUS e=loc(exp) %prec prec_prefix_op { PEapp (qsymb_of_symb "-", [e]) }

| e1=loc(exp)    IMPL  e2=loc(exp)  { PEapp (qsymb_of_symb "=>" , [e1; e2]) }
| e1=loc(exp)    IFF   e2=loc(exp)  { PEapp (qsymb_of_symb "<=>", [e1; e2]) }
| e1=loc(exp)    OR    e2=loc(exp)  { PEapp (qsymb_of_symb "||" , [e1; e2]) }
| e1=loc(exp)    AND   e2=loc(exp)  { PEapp (qsymb_of_symb "&&" , [e1; e2]) }
| e1=loc(exp)    EQ    e2=loc(exp)  { PEapp (qsymb_of_symb "="  , [e1; e2]) }
| e1=loc(exp)    NE    e2=loc(exp)  { PEapp (qsymb_of_symb "<>" , [e1; e2]) }
| e1=loc(exp) op=OP1   e2=loc(exp)  { PEapp (qsymb_of_symb op   , [e1; e2]) }
| e1=loc(exp) op=OP2   e2=loc(exp)  { PEapp (qsymb_of_symb op   , [e1; e2]) }
| e1=loc(exp)    MINUS e2=loc(exp)  { PEapp (qsymb_of_symb "-"  , [e1; e2]) }
| e1=loc(exp) op=OP3   e2=loc(exp)  { PEapp (qsymb_of_symb op   , [e1; e2]) }
| e1=loc(exp)    STAR  e2=loc(exp)  { PEapp (qsymb_of_symb "*"  , [e1; e2]) }
| e1=loc(exp) op=OP4   e2=loc(exp)  { PEapp (qsymb_of_symb op   , [e1; e2]) }

| c=loc(exp) QUESTION e1=loc(exp) COLON e2=loc(exp) %prec OP2
| IF c=loc(exp) THEN e1=loc(exp) ELSE e2=loc(exp)
   { PEif (c, e1, e2) }

| LET p=lpattern EQ e1=loc(exp) IN e2=loc(exp)
   { PElet (p, e1, e2) }

| e=sexp { e }

| re=loc(rnd_exp) { PErnd re }
;

(* -------------------------------------------------------------------- *)
rnd_exp:
| LKEY n1=number COMMA n2=number RKEY
    { if   n1 = 0 && n2 = 1
      then PRbool
      else error (Location.make $startpos $endpos) "malformed bool random" }

| LKEY n1=number COMMA n2=number RKEY_HAT e=loc(exp)
    { if   n1 = 0 && n2 = 1
      then PRbitstr e
      else error (Location.make $startpos $endpos) "malformed random bitstring" }

| LBRACKET e1=loc(exp) DOTDOT e2=loc(exp) RBRACKET
    { PRinter (e1, e2) }

| LPAREN re=loc(rnd_exp) BACKSLASH e=loc(exp) RPAREN
    { PRexcepted (re, e) }

| x=qident LPAREN es=exp_list0 RPAREN
    { PRapp (x, es) }
;

(* -------------------------------------------------------------------- *)
%inline p_exp_sm_list0: aout=plist0(loc(exp), SEMICOLON) { aout }

%inline exp_list0: aout=plist0(loc(exp), COMMA) { aout }
%inline exp_list1: aout=plist1(loc(exp), COMMA) { aout }
%inline exp_list2: aout=plist2(loc(exp), COMMA) { aout }

(* -------------------------------------------------------------------- *)
(* Formulas                                                             *)

sform:
| TRUE                                   { PFbool true  }
| FALSE                                  { PFbool false }
| n=number                               { PFint n }
| x=qident                                { PFident x }
| se=loc(sform) LBRACKET e=loc(form) RBRACKET { PFapp (qsymb_of_symb "<get>", [se; e]) }
| se=loc(sform) LBRACKET e1=loc(form) LEFTARROW e2=loc(form) RBRACKET
                                         { PFapp (qsymb_of_symb "<set>", [se; e1; e2]) }
| x=qident LPAREN es=form_list0 RPAREN     { PFapp (x, es) }
| x=loc(sform) LKEY s=prog_num RKEY      { PFside (x, s) }
| LPAREN es=form_list2 RPAREN            { PFtuple es }
| LPAREN e=form RPAREN                   { e }
| LBRACKET es=p_form_sm_list0 RBRACKET   { pflist es }
                          
form:
| NOT   e=loc(form)                      { PFnot e }
| MINUS e=loc(form) %prec prec_prefix_op { PFapp (qsymb_of_symb "-", [e]) }
| e1=loc(form)    IMPL  e2=loc(form)  { PFbinop (e1, PPimp, e2) }
| e1=loc(form)    IFF   e2=loc(form)  { PFbinop (e1, PPiff, e2) }
| e1=loc(form)    OR    e2=loc(form)  { PFbinop (e1, PPor, e2)  }
| e1=loc(form)    AND   e2=loc(form)  { PFbinop (e1, PPand, e2) }
| e1=loc(form)    EQ    e2=loc(form)  { PFapp (qsymb_of_symb "="  , [e1; e2]) }
| e1=loc(form)    NE    e2=loc(form)  { PFapp (qsymb_of_symb "<>" , [e1; e2]) }
| e1=loc(form) op=OP1   e2=loc(form)  { PFapp (qsymb_of_symb op   , [e1; e2]) }
| e1=loc(form) op=OP2   e2=loc(form)  { PFapp (qsymb_of_symb op   , [e1; e2]) }
| e1=loc(form)    MINUS e2=loc(form)  { PFapp (qsymb_of_symb "-"  , [e1; e2]) }
| e1=loc(form) op=OP3   e2=loc(form)  { PFapp (qsymb_of_symb op   , [e1; e2]) }
| e1=loc(form)    STAR  e2=loc(form)  { PFapp (qsymb_of_symb "*"  , [e1; e2]) }
| e1=loc(form) op=OP4   e2=loc(form)  { PFapp (qsymb_of_symb op   , [e1; e2]) }

| c=loc(form) QUESTION e1=loc(form) COLON e2=loc(form) %prec OP2 { PFif (c, e1, e2) }
| IF c=loc(form) THEN e1=loc(form) ELSE e2=loc(form)             { PFif (c, e1, e2) }

| LET p=lpattern EQ e1=loc(form) IN e2=loc(form) { PFlet (p, e1, e2) }
| LET p=lpattern EQ e1=loc(form) IN e2=loc(form) 
                            { PFlet (p, e1, e2) }
| e=sform              { e }
| FORALL pd=param_decl COMMA e=loc(form) { PFforall(pd, e) }
| EXIST  pd=param_decl COMMA e=loc(form) { PFexists(pd,e) }
;

%inline p_form_sm_list0: aout=plist0(loc(form), SEMICOLON) { aout }
%inline form_list0: aout=plist0(loc(form), COMMA) { aout }
%inline form_list2: aout=plist2(loc(form), COMMA) { aout }

(* -------------------------------------------------------------------- *)
(* Type expressions                                                     *)

simpl_type_exp:
| UNDERSCORE                  { PTunivar       }
| x=qident                    { PTnamed x      }
| x=prim_ident                { PTvar x        }
| tya=type_args x=qident      { PTapp (x, tya) }
| LPAREN ty=type_exp RPAREN   { ty             }
;

type_args:
| ty=loc(simpl_type_exp)                          { [ty] }
| LPAREN tys=plist2(loc(type_exp), COMMA) RPAREN  { tys  }
;

type_exp:
| ty=simpl_type_exp                    { ty }
| ty=plist2(loc(simpl_type_exp), STAR) { PTtuple ty }
;

type_exp_dom:
| LPAREN RPAREN                                  { [  ] }
| ty=loc(type_exp)                               { [ty] }
| LPAREN tys=plist2(loc(type_exp), COMMA) RPAREN { tys  }
;

type_exp_pred_dom:
| LPAREN RPAREN                                  { [  ] }
| ty=loc(type_exp)                               { [ty] }
| LPAREN tys=plist2(loc(type_exp), COMMA) RPAREN { tys  }
;

fun_type:
| dom=type_exp_pred_dom ARROW codom=type_exp { (dom, codom) }
;

(* -------------------------------------------------------------------- *)
(* Parameter declarations                                              *)

typed_vars:
| xs=ident_list1 COLON ty=loc(type_exp) { List.map (fun v -> (v, ty)) xs }
;

param_decl:
| LPAREN aout=plist0(typed_vars, COMMA) RPAREN { List.flatten aout }
;

(* -------------------------------------------------------------------- *)
(* Statements                                                           *)

lvalue:
| x=qident                              { PLvSymbol x      }
| LPAREN p=plist2(qident, COMMA) RPAREN { PLvTuple  p      }
| x=qident LBRACKET e=loc(exp) RBRACKET { PLvMap    (x, e) }
;

rvalue:
| e=loc(exp)                          { `Expr e }
| x=qident LPAREN es=exp_list0 RPAREN { `Call (x, es) }
;

base_instr:
| f=qident LPAREN es=exp_list0 RPAREN
    { PScall (f, es) }

| x=lvalue EQ e=rvalue
    { PSasgn (x, e) }

| ASSERT LPAREN c=loc(exp) RPAREN 
     { PSassert c }
;

instr:
| bi=base_instr SEMICOLON                            { bi }
| IF LPAREN c=loc(exp) RPAREN b1=block ELSE b2=block { PSif (c, b1, b2) }
| IF LPAREN c=loc(exp) RPAREN b =block               { PSif (c, b , []) }
| WHILE LPAREN c=loc(exp) RPAREN b=block             { PSwhile (c, b) }
;

block:
| i=base_instr SEMICOLON { [i] }
| LKEY stmt=stmt RKEY    { stmt }
;

stmt: aout=instr* { aout }

(* -------------------------------------------------------------------- *)
(* Functions                                                            *)

var_decl:
| VAR xs=ident_list1 COLON ty=loc(type_exp) { (xs, ty) }
;

var_decl_list:
| var_decl { [$1] }
| var_decl var_decl_list { $1::$2 }
;

(* -------------------------------------------------------------------- *)
(* Module definition                                                    *)

loc_decl:
| VAR xs=ident_list1 COLON ty=loc(type_exp) SEMICOLON
     { (xs, ty, None  ) }

| VAR xs=ident_list1 COLON ty=loc(type_exp) EQ e=loc(exp) SEMICOLON
     { (xs, ty, Some e) }
;

ret_stmt:
| RETURN e=loc(exp) SEMICOLON { Some e }
| empty                       { None }
;

fun_def_body:
| LKEY decl=loc_decl* s=stmt rs=ret_stmt RKEY
    { { pfb_locals = decl;
        pfb_body   = s   ;
        pfb_return = rs  ; }
    }
;

fun_decl:
| x=ident pd=param_decl COLON ty=loc(type_exp)
    { { pfd_name     = x   ;
        pfd_tyargs   = pd  ;
        pfd_tyresult = ty  ;
        pfd_uses     = None; }
    }
;

mod_item:
| v=var_decl
    { Pst_var v }

| m=mod_def
    { let x, m = m in Pst_mod (x, m) }

| FUN decl=fun_decl EQ body=fun_def_body
    { Pst_fun (decl, body) }

| FUN x=ident EQ f=qident
    { Pst_alias (x, f) }
;

(* -------------------------------------------------------------------- *)
(* Modules                                                              *)

mod_body:
| LKEY stt=mod_item* RKEY { stt }
;

mod_def:
| MODULE x=ident EQ body=mod_body
    { (x, mk_mod [] body) }

| MODULE x=ident EQ m=qident
    { (x, Pm_ident (m, [])) }

| MODULE x=ident EQ m=qident LPAREN a=plist1(qident, COMMA) RPAREN
    { (x, Pm_ident (m, a)) }

| MODULE x=ident LPAREN a=plist1(sig_arg, COMMA) RPAREN EQ body=mod_body
    { (x, mk_mod a body) }
;

(* -------------------------------------------------------------------- *)
(* Modules interfaces                                                   *)

sig_def:
| MODULE TYPE x=ident EQ i=sig_body
    { (x, i) }

| MODULE TYPE x=ident LPAREN a=plist1(sig_arg, COMMA) RPAREN EQ i=signature
    { (x, Pty_func (a, i)) }
;

sig_arg:
| x=ident COLON i=qident { (x, i) }
;

sig_body:
| x=qident LPAREN a=plist1(qident, COMMA) RPAREN
    { Pty_app (x, a) }

| x=signature
   { Pty_sig x }
;

signature:
| LKEY x=signature_item* RKEY { x }
;

signature_item:
| VAR decl=ivar_decl
    { `VariableDecl decl }

| FUN decl=ifun_decl
    { `FunctionDecl decl }
;

ifun_decl:
| x=ident pd=param_decl COLON ty=loc(type_exp)
    { { pfd_name     = x   ;
        pfd_tyargs   = pd  ;
        pfd_tyresult = ty  ;
        pfd_uses     = None; }
    }

| x=ident pd=param_decl COLON ty=loc(type_exp) LKEY us=qident* RKEY
    { { pfd_name     = x      ;
        pfd_tyargs   = pd     ;
        pfd_tyresult = ty     ;
        pfd_uses     = Some us; }
    }
;

ivar_decl:
| x=ident COLON ty=loc(type_exp)
    { { pvd_name = x; pvd_type = ty } }
;

(* -------------------------------------------------------------------- *)
(* EcTypes declarations / definitions                                     *)

poly_type_decl:
| empty                              { []  }
| x=prim_ident                       { [x] }
| LPAREN xs=prim_ident_list1 RPAREN  { xs  }
;

type_decl:
| TYPE tydecl=poly_type_decl x=ident { (tydecl, x) }
;

type_decl_or_def:
| td=type_decl { mk_tydecl td None }
| td=type_decl EQ te=loc(type_exp) { mk_tydecl td (Some te) }
;

(* -------------------------------------------------------------------- *)
(* Operator definitions                                                 *)

op_tydom:
| LPAREN RPAREN                                  { [  ] }
| ty=loc(type_exp)                               { [ty] }
| LPAREN tys=plist2(loc(type_exp), COMMA) RPAREN { tys  }
;

op_sig:
| dom=op_tydom ARROW codom=loc(type_exp) { (Some dom, codom) }
;

op_ident:
| x=ident { x }
| LBRACKET x=binop RBRACKET { x }
;

tyvars_decl:
| LBRACKET tyvars=prim_ident* RBRACKET { Some tyvars }
| empty { None }
    
operator:
| OP x=op_ident tyvars=tyvars_decl COLON sty=op_sig {
    { po_name   = x      ;
      po_tyvars = tyvars ;
      po_dom    = fst sty;
      po_codom  = snd sty;
      po_body   = None   ;
      po_prob   = false  ; }
  }

| OP x=op_ident tyvars=tyvars_decl p=param_decl COLON codom=loc(type_exp)
    EQ b=loc(exp) {
    { po_name   = x      ;
      po_tyvars = tyvars ;
      po_dom    = Some(List.map snd p);
      po_codom  = codom  ;
      po_body   = Some(List.map fst p, b);
      po_prob   = false  ; }
  }

| POP x=ident tyvars=tyvars_decl COLON sty=op_sig {
    { po_name   = x      ;
      po_tyvars = tyvars ;
      po_dom = fst sty   ;
      po_codom = snd sty ;
      po_body  = None    ;
      po_prob   = true   ; }
  }

| CNST x=ident tyvars=tyvars_decl COLON ty=loc(type_exp) {
    { po_name   = x    ;
      po_tyvars = tyvars   ;
      po_dom = None    ;
      po_codom = ty    ;
      po_body = None   ;
      po_prob   = false; }
  }
| CNST x=ident tyvars=tyvars_decl COLON ty=loc(type_exp) EQ e=loc(exp) {
    { po_name   = x     ;
      po_tyvars = tyvars;
      po_dom = None     ;
      po_codom = ty     ;
      po_body = Some([], e) ;
      po_prob   = false ; }
  }
;

predicate:
| PRED x = op_ident { 
  { pp_name = x;
    pp_tyvars = None;
    pp_def = AbstrDef (Some []) }
  }
| PRED x = op_ident EQ f=loc(form) {
  { pp_name = x;
    pp_tyvars = None;
    pp_def = ConcrDef([], f) }
  }
| PRED x = op_ident tyvars=tyvars_decl COLON sty = op_tydom { 
  { pp_name = x;
    pp_tyvars = tyvars;
    pp_def = AbstrDef(Some sty) }
  } 
| PRED x = op_ident tyvars=tyvars_decl params=param_decl EQ f=loc(form) { 
  { pp_name = x;
    pp_tyvars = tyvars;
    pp_def = ConcrDef(params, f) }
  }
;

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

%inline ident_exp:
| x=ident COMMA e=loc(exp) { (x, e) }
;

real_hint:
| USING x=ident { Husing x }
| ADMIT         { Hadmit }
| COMPUTE       { Hcompute }
| COMPUTE n=NUM e1=loc(exp) COMMA e2=loc(exp)
                { Hfailure (n, e1, e2, []) }
| COMPUTE n=NUM e1=loc(exp) COMMA e2=loc(exp) COLON l=plist1(ident_exp, COLON)
                { Hfailure (n, e1, e2, l) }
| SPLIT         { Hsplit }
| SAME          { Hsame }
| AUTO          { Hauto }
| empty         { Hnone }
;

claim:
| CLAIM x=ident COLON e=loc(exp) h=real_hint { (x, (e, h)) }
;

axiom_kind:
| AXIOM { PAxiom }
| LEMMA { PLemma }

axiom:
| k=axiom_kind x=ident COLON e=loc(form) { 
      { pa_name = x; pa_formula = e; pa_kind = k } }
;
(* -------------------------------------------------------------------- *)
(* Theory dynamic manipulation                                          *)

theory_open    : THEORY  x=ident { x }
theory_close   : END     x=ident { x }
theory_require : REQUIRE x=ident { x }
theory_import  : IMPORT  x=qident { x }

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

global_:
| theory_open      { GthOpen    $1 }
| theory_close     { GthClose   $1 }
| theory_require   { GthRequire $1 }
| theory_import    { GthImport  $1 }
| mod_def          { Gmodule    $1 }
| sig_def          { Ginterface $1 }
| type_decl_or_def { Gtype      $1 }
| operator         { Goperator  $1 }
| predicate        { Gpredicate $1 }
| axiom            { Gaxiom     $1 }
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
| error    { error (Location.make $startpos $endpos) "Parsing error" }
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

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X {
    { pl_desc = x;
      pl_loc  = Location.make $startpos $endpos;
    }
  }
;
