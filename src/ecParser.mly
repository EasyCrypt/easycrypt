%{
  open EcUtils
  open EcParsetree

  let error pos msg =
    let msg =
      Printf.sprintf "%s: %s" (EcLocation.tostring pos) msg
    in
      failwith msg

  let mk_loc loc e = { pl_desc = e;  pl_loc  = loc;}

  let pqsymb_of_psymb (x : psymbol) : pqsymbol =
    mk_loc x.pl_loc ([], x.pl_desc)

  let pqsymb_of_symb loc x : pqsymbol =
    mk_loc loc ([], x)

  let mk_mod ?(modtypes = []) params body = Pm_struct {
    ps_params    = params;
    ps_signature = modtypes;
    ps_body      = body;
  }

  let mk_tydecl (tyvars, name) body = {
    pty_name   = name;
    pty_tyvars = tyvars;
    pty_body   = body;
  }

  let mk_peid_symb loc s ti = 
    mk_loc loc (PEident(pqsymb_of_symb loc s, ti))

  let mk_pfid_symb loc s ti = 
    mk_loc loc (PFident(pqsymb_of_symb loc s, ti))

  let peapp_symb loc s ti es = 
    PEapp(mk_peid_symb loc s ti, es)

  let peget loc ti e1 e2    = 
    peapp_symb loc EcCoreLib.s_get ti [e1;e2]

  let peset loc ti e1 e2 e3 = 
    peapp_symb loc EcCoreLib.s_set ti [e1;e2;e3]

  let pfapp_symb loc s ti es = 
    PFapp(mk_pfid_symb loc s ti, es)

  let pfget loc ti e1 e2    = 
    pfapp_symb loc EcCoreLib.s_get ti [e1;e2]

  let pfset loc ti e1 e2 e3 = 
    pfapp_symb loc EcCoreLib.s_set ti [e1;e2;e3]

  let pe_nil loc ti = 
    mk_peid_symb loc EcCoreLib.s_nil ti

  let pe_cons loc ti e1 e2 = 
    mk_loc loc (peapp_symb loc EcCoreLib.s_cons ti [e1; e2])
      
  let pelist loc ti (es : pexpr    list) : pexpr    = 
    List.fold_right (fun e1 e2 -> pe_cons loc ti e1 e2) es (pe_nil loc ti)

  let pf_nil loc ti = 
    mk_pfid_symb loc EcCoreLib.s_nil ti

  let pf_cons loc ti e1 e2 = 
    mk_loc loc (pfapp_symb loc EcCoreLib.s_cons ti [e1; e2])
      
  let pflist loc ti (es : pformula    list) : pformula    = 
    List.fold_right (fun e1 e2 -> pf_cons loc ti e1 e2) es (pf_nil loc ti)

  let mk_axiom p k = 
    { pa_name = fst p; pa_formula = snd p; pa_kind = k }

  let str_and b = if b then "&&" else "/\\"
  let str_or b  = if b then "||" else "\\/"

  let mk_simplify l = 
    if l = [] then 
      { pbeta  = true; pdelta = None; 
        pzeta  = true; piota  = true; plogic = true; }
    else
      let zeta = ref false and beta = ref false and iota = ref false
      and logic = ref false and delta = ref (Some []) in
      let doarg = function
        | `Delta l -> 
          if l = [] || !delta = None then delta := None
          else delta := Some (odfl [] !delta @ l)
        | `Zeta    -> zeta  := true
        | `Iota    -> iota  := true
        | `Beta    -> beta  := true
        | `Logic   -> logic := true in
      List.iter doarg l;
      { pbeta  = !beta; pdelta = !delta; 
        pzeta  = !zeta; piota  = !iota; plogic = !logic; }

  let simplify_red = [`Zeta; `Iota; `Beta; `Logic]

%}

%token <EcSymbols.symbol> LIDENT
%token <EcSymbols.symbol> UIDENT
%token <EcSymbols.symbol> TIDENT
%token <EcSymbols.symbol> PBINOP

%token <int> NUM
%token <string> STRING

(* Tokens + keywords *)
%token SAMPLE
// %token ABSTRACT
%token UNDERSCORE
%token ADMIT
%token CUT
// %token ADVERSARY
%token ARROW
%token AS
%token AT
// %token ASPEC
%token ASSERT
%token AXIOM
%token LEMMA
%token PROOF
%token CHECKPROOF
%token CLAIM
%token CLONE
%token CNST
%token COLON
%token COMMA
%token COMPUTE
%token DOT
%token DOTDOT
%token DROP
%token ELSE
%token END
%token EOF
%token EQ
%token CEQ
// %token EQEQLBRACKET
%token EQUIV
%token EXPORT
%token EXIST
%token FINAL
%token FORALL
%token LAMBDA
%token FUN
%token HOARE
%token IF
%token IFF
%token IMPL
%token IMPORT
%token IN
// %token INCLUDE
// %token INTERFACE
// %token KW_AND
%token DLBRACKET
%token LBRACKET
%token LEFTARROW
// %token LEMMA
%token LET
%token LKEY
// %token LLIMP
%token LONGARROW
%token LPAREN
%token MODULE
%token FROM_INT
%token NE
%token NOT
%token OP
%token <bool> AND (* true asym : &&, false sym : /\ *)
%token <bool> OR  (* true asym : ||, false sym : \/ *)
%token PIPE
// %token PR
%token PRED
%token PROVER
%token TIMEOUT
%token QUESTION
%token RBRACKET
// %token RBRACKETLLIMP
// %token REMOVE
%token RES
%token RETURN
%token REQUIRE
// %token USE
%token RKEY
%token RKEY_HAT
// %token ROI
%token RPAREN
%token SAME
%token SEMICOLON
// %token SET
%token STAR
%token THEN
%token THEORY
%token TILD
%token TYPE
// %token UNSET
// %token UPTO
%token USING
%token VAR
// %token WHERE
%token WHILE
%token WITH
%token PR

(* Tactics *)
// %token ABORT
// %token ALL
// %token APP
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
%token IDTAC
%token RIGHT
%token LEFT
%token TRIVIAL
%token INTROS
%token ASSUMPTION
%token GENERALIZE 
%token CLEAR
%token SPLIT
%token ELIM
%token ELIMT
%token CASE
%token REWRITE
%token SUBST
%token SIMPLIFY
%token DELTA
%token ZETA 
%token IOTA 
%token BETA 
%token LOGIC

%token CHANGE
%token APPLY
// %token IFNEG
// %token IFSYNC
// %token INLINE
// %token LAST
// %token OPAQUE
// %token PRHL
%token PRINT
// %token RANDOM
%token SAVE
// %token SIMPL
// %token SP
// %token SPLITWHILE
// %token SWAP
// %token TRANSPARENT
// %token TRY
%token UNDO
// %token UNFOLD
// %token UNROLL
// %token WP
%token WHY3
%token ON
%token OFF

(* PHL Tactics *)
%token APP
%token WP
%token SKIP

%token <string> OP1 OP2 OP3 OP4
%token LTCOLON GT

%nonassoc COMMA ELSE

%nonassoc IN
%right IMPL IFF
%right OR 
%right AND 

%nonassoc NOT
%nonassoc PIPE
%left EQ NE OP1 GT

%right QUESTION
%left OP2 
%right ARROW
%left OP3 STAR
%left OP4 

%nonassoc prec_prefix_op
%nonassoc above_OP

%type <EcParsetree.global> global
%type <EcParsetree.prog> prog

%start prog global
%%

(* -------------------------------------------------------------------- *)
%inline lident: x=loc(LIDENT) { x };
%inline uident: x=loc(UIDENT) { x };
%inline tident: x=loc(TIDENT) { x };

%inline _ident:
| x=LIDENT { x }
| x=UIDENT { x }
;

%inline ident:
| x=loc(_ident) { x }
;

%inline number: n=NUM { n };

(* -------------------------------------------------------------------- *)
namespace:
| x=UIDENT { [x] }
| xs=namespace DOT x=UIDENT { xs @ [x] }
;

qident:
| x=ident { pqsymb_of_psymb x }

| xs=namespace DOT x=_ident {
    { pl_desc = (xs, x);
      pl_loc  = EcLocation.make $startpos(xs) $endpos(xs);
    }
  }
;

(* -------------------------------------------------------------------- *)
uqident:
| x=UIDENT {
    { pl_desc = ([], x);
      pl_loc  = EcLocation.make $startpos $endpos; }
  }

| xs=namespace DOT x=UIDENT {
    { pl_desc = (xs, x);
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }
;

(* -------------------------------------------------------------------- *)
%inline _oident:
| x=LIDENT { x }
| x=UIDENT { x }
| x=PBINOP { x }
;

%inline oident:
| x=loc(_oident) { x }
;

qident_pbinop:
| x=oident
    { pqsymb_of_psymb x }

| xs=namespace DOT x=oident {
    { pl_desc = (xs, unloc x);
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }
;

(* -------------------------------------------------------------------- *)
mident1:
| x=uident
    { (x, []) }

| x=uident LPAREN args=plist1(loc(mident), COMMA) RPAREN
    { (x, args) }
;

mident:
| x=plist1(mident1, DOT) { (x : pmsymbol) }
;

(* -------------------------------------------------------------------- *)
%inline binop:
| EQ      { "=" }
| x=AND   { str_and x }
| x=OR    { str_or x  }
| STAR    { "*" }
| GT      { ">" }
| x=OP1   { x   }
| x=OP2   { x   }
| x=OP3   { x   }
| x=OP4   { x   }
;

(* -------------------------------------------------------------------- *)
pside:
| x=qident {
    let (qn, id) = x.pl_desc in
      if qn <> [] then
        error
          (EcLocation.make $startpos(x) $endpos(x))
          "memory names cannot be qualified"
      else
        { x with pl_desc = id }
  }

| x=loc(number) {
    { x with pl_desc = Printf.sprintf "$%d" x.pl_desc }
  }
;

(* -------------------------------------------------------------------- *)
(* Expressions: program expression, real expression                     *)
tvar_instance:
| x=tident EQ ty=loc(type_exp) { x,ty }
;

tvars_instance_kind:
| lt = plist1(loc(type_exp), COMMA) { TVIunamed lt }
| lt = plist1(tvar_instance, COMMA) { TVInamed lt }
;

%inline tvars_app:
| LTCOLON k=tvars_instance_kind GT { k }
;

lpattern:
| x=ident { LPSymbol x }
| LPAREN p=plist2(ident, COMMA) RPAREN { LPTuple p }
;

sexp:
| n=number
   { PEint n }

| x=qident_pbinop ti=tvars_app?
   { PEident (x,ti) }

| se=loc(sexp) op=loc(FROM_INT)
   { let id = PEident(mk_loc op.pl_loc EcCoreLib.s_from_int, None) in
     PEapp (mk_loc op.pl_loc id, [se]) }

| se=loc(sexp) DLBRACKET ti=tvars_app? e=loc(exp) RBRACKET
   { peget (EcLocation.make $startpos $endpos) ti se e }

| se=loc(sexp) DLBRACKET ti=tvars_app? e1=loc(exp) LEFTARROW e2=loc(exp) RBRACKET  
   { peset (EcLocation.make $startpos $endpos) ti se e1 e2 }

| PIPE ti=tvars_app? e=loc(exp) PIPE 
    { peapp_symb e.pl_loc EcCoreLib.s_abs ti [e] }

| LPAREN es=exp_list2 RPAREN
   { PEtuple es }

| LPAREN e=exp RPAREN
   { e }

| LBRACKET ti=tvars_app? es=loc(p_exp_sm_list0) RBRACKET  
   { unloc (pelist es.pl_loc ti es.pl_desc) } 

| LBRACKET ti=tvars_app? e1=loc(exp) op=loc(DOTDOT) e2=loc(exp) RBRACKET
    { let id = PEident(mk_loc op.pl_loc EcCoreLib.s_dinter, ti) in
      PEapp(mk_loc op.pl_loc id, [e1; e2]) }

| LKEY n1=number op=loc(COMMA) n2=number RKEY
    { if   n1 = 0 && n2 = 1
      then PEident (mk_loc op.pl_loc EcCoreLib.s_dbool, None)
      else error (EcLocation.make $startpos $endpos) "malformed bool random" }
;

op1:
| OP1 { $1  }
| GT  { ">" }
;

exp:
| e=sexp { e }  %prec above_OP

| e=loc(sexp) args=sexp_list1 { PEapp (e, args) }

| op=loc(NOT) ti=tvars_app? e=loc(exp)
   { peapp_symb op.pl_loc "!" ti [e] }

| op=loc(binop) ti=tvars_app? e=loc(exp) %prec prec_prefix_op
   { peapp_symb op.pl_loc op.pl_desc ti [e] } 

| e1=loc(exp) op=loc(op1) ti=tvars_app? e2=loc(exp) %prec OP1
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=loc(exp) op=loc(OP2) ti=tvars_app? e2=loc(exp) 
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=loc(exp) op=loc(OP3) ti=tvars_app? e2=loc(exp) 
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=loc(exp) op=loc(OP4) ti=tvars_app? e2=loc(exp) 
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=loc(exp) op=loc(IMPL) ti=tvars_app? e2=loc(exp)
    { peapp_symb op.pl_loc "=>" ti [e1; e2] }

| e1=loc(exp) op=loc(IFF) ti=tvars_app? e2=loc(exp) 
    { peapp_symb op.pl_loc "<=>" ti [e1; e2] }

| e1=loc(exp) op=loc(OR) ti=tvars_app? e2=loc(exp)  
    { peapp_symb op.pl_loc (str_or op.pl_desc) ti [e1; e2] }

| e1=loc(exp) op=loc(AND) ti=tvars_app? e2=loc(exp) 
    { peapp_symb op.pl_loc (str_and op.pl_desc) ti [e1; e2] }

| e1=loc(exp) op=loc(EQ) ti=tvars_app? e2=loc(exp)  
    { peapp_symb op.pl_loc "=" ti [e1; e2] }

| e1=loc(exp) op=loc(NE) ti=tvars_app? e2=loc(exp) 
    { peapp_symb op.pl_loc "!" None 
      [ mk_loc op.pl_loc (peapp_symb op.pl_loc "=" ti [e1; e2])] }

| e1=loc(exp) op=loc(STAR) ti=tvars_app?  e2=loc(exp)  
    { peapp_symb op.pl_loc "*" ti [e1; e2] }

| c=loc(exp) QUESTION e1=loc(exp) COLON e2=loc(exp) %prec OP2
| IF c=loc(exp) THEN e1=loc(exp) ELSE e2=loc(exp)
   { PEif (c, e1, e2) }

| LET p=lpattern EQ e1=loc(exp) IN e2=loc(exp)
   { PElet (p, e1, e2) }

(* Distribution *)
| LKEY n1=number op=loc(COMMA) n2=number RKEY_HAT e=loc(sexp)
    { if   n1 = 0 && n2 = 1 then 
        let id = PEident(mk_loc op.pl_loc EcCoreLib.s_dbitstring, None) in
        PEapp (mk_loc op.pl_loc id, [e])
      else error (EcLocation.make $startpos $endpos) "malformed random bitstring" }
;

(* -------------------------------------------------------------------- *)
%inline p_exp_sm_list0: aout=plist0(loc(exp), SEMICOLON) { aout }

%inline exp_list0: aout=plist0(loc(exp), COMMA) { aout }
%inline sexp_list1: aout=plist1(loc(sexp), empty) { aout }
%inline exp_list2: aout=plist2(loc(exp), COMMA) { aout }

(* -------------------------------------------------------------------- *)
(* Formulas                                                             *)

sform:
| n=number
   { PFint n }

| x=loc(RES)
   { PFident (mk_loc x.pl_loc ([], "$res"), None) }

| x=qident_pbinop ti=tvars_app?
   { PFident (x,ti) }

| se=loc(sform) op=loc(FROM_INT)
   { let id = PFident(mk_loc op.pl_loc EcCoreLib.s_from_int, None) in
     PFapp (mk_loc op.pl_loc id, [se]) }

| se=loc(sform) DLBRACKET ti=tvars_app? e=loc(form) RBRACKET
   { pfget (EcLocation.make $startpos $endpos) ti se e }

| se=loc(sform) DLBRACKET ti=tvars_app? e1=loc(form) LEFTARROW e2=loc(form) RBRACKET
   { pfset (EcLocation.make $startpos $endpos) ti se e1 e2 }

| x=loc(sform) LKEY s=pside RKEY
   { PFside (x, s) }

| LPAREN es=form_list2 RPAREN
   { PFtuple es }

| LPAREN e=form RPAREN
   { e }

| LBRACKET ti=tvars_app? es=loc(p_form_sm_list0) RBRACKET
   { (pflist es.pl_loc ti es.pl_desc).pl_desc }

| HOARE LBRACKET
    x=lident AT nm=mident COLON pre=loc(form) LONGARROW post=loc(form)
  RBRACKET

    { let mp = mk_loc (EcLocation.make $startpos(x) $endpos(nm)) (nm, x) in
        PFhoareF (pre, mp, post) }

| EQUIV LBRACKET eb=equiv_body RBRACKET { eb }

| PR LBRACKET
    x=lident args=paren(plist0(loc(sform), COMMA))
    AT nm=mident COMMA LKEY pn=pside RKEY
    COLON event=loc(form)
  RBRACKET

    { let mp= mk_loc (EcLocation.make $startpos(x) $endpos(nm)) (nm, x) in
        PFprob (mp, args, pn, event) }

| PIPE ti=tvars_app? e =loc(form) PIPE 
    { pfapp_symb e.pl_loc EcCoreLib.s_abs ti [e] }

| LKEY n1=number op=loc(COMMA) n2=number RKEY
    { if   n1 = 0 && n2 = 1
      then PFident (mk_loc op.pl_loc EcCoreLib.s_dbool, None)
      else error (EcLocation.make $startpos $endpos) "malformed bool random" }

| LBRACKET ti=tvars_app? e1=loc(form) op=loc(DOTDOT) e2=loc(form) RBRACKET
    { let id = PFident(mk_loc op.pl_loc EcCoreLib.s_dinter, ti) in
      PFapp(mk_loc op.pl_loc id, [e1; e2]) } 
;
                          
form:
| e=sform { e } %prec above_OP

| e=loc(sform) args=sform_list1 { PFapp (e, args) } 

| op=loc(NOT) ti=tvars_app? e=loc(form) 
    { pfapp_symb  op.pl_loc "!" ti [e] }

| op=loc(binop) ti=tvars_app? e=loc(form) %prec prec_prefix_op
   { pfapp_symb op.pl_loc op.pl_desc ti [e] } 

| e1=loc(form) op=loc(op1) ti=tvars_app? e2=loc(form) %prec OP1 
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] } 

| e1=loc(form) op=loc(OP2) ti=tvars_app? e2=loc(form)  
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=loc(form) op=loc(OP3) ti=tvars_app? e2=loc(form)  
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=loc(form) op=loc(OP4) ti=tvars_app? e2=loc(form)  
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=loc(form) op=loc(IMPL) ti=tvars_app? e2=loc(form)  
    { pfapp_symb op.pl_loc "=>" ti [e1; e2] }

| e1=loc(form) op=loc(IFF) ti=tvars_app? e2=loc(form)  
    { pfapp_symb op.pl_loc "<=>" ti [e1; e2] }

| e1=loc(form) op=loc(OR) ti=tvars_app? e2=loc(form)  
    { pfapp_symb op.pl_loc (str_or op.pl_desc) ti [e1; e2] }

| e1=loc(form) op=loc(AND) ti=tvars_app? e2=loc(form)  
    { pfapp_symb op.pl_loc (str_and op.pl_desc) ti [e1; e2] }

| e1=loc(form) op=loc(EQ   ) ti=tvars_app? e2=loc(form)  
    { pfapp_symb op.pl_loc "=" ti [e1; e2] }

| e1=loc(form) op=loc(NE   ) ti=tvars_app? e2=loc(form) 
    { pfapp_symb op.pl_loc "!" None 
      [ mk_loc op.pl_loc (pfapp_symb op.pl_loc "=" ti [e1; e2])] }

| e1=loc(form) op=loc(STAR ) ti=tvars_app? e2=loc(form)  
    { pfapp_symb op.pl_loc "*" ti [e1; e2] }

| c=loc(form) QUESTION e1=loc(form) COLON e2=loc(form) %prec OP2 { PFif (c, e1, e2) }
| IF c=loc(form) THEN e1=loc(form) ELSE e2=loc(form)             { PFif (c, e1, e2) }

| LET p=lpattern EQ e1=loc(form) IN e2=loc(form) { PFlet (p, e1, e2) }

| FORALL pd=pgtybindings COMMA e=loc(form) { PFforall (pd, e) }
| EXIST  pd=pgtybindings COMMA e=loc(form) { PFexists (pd, e) }
| LAMBDA pd=pgtybindings COMMA e=loc(form) { PFlambda (pd, e) }

(* Distribution *)
| LKEY n1=number op=loc(COMMA) n2=number RKEY_HAT e=loc(sform)
    { if n1 = 0 && n2 = 1 then 
        let id =
          PFident (mk_loc op.pl_loc EcCoreLib.s_dbitstring, None)
        in
          PFapp (mk_loc op.pl_loc id, [e])
      else
        error
          (EcLocation.make $startpos $endpos)
          "malformed random bitstring" }
;

equiv_body:
  x1=lident AT nm1=mident TILD x2=lident AT nm2=mident
  COLON pre=loc(form) LONGARROW post=loc(form)

    { let mp1 = mk_loc (EcLocation.make $startpos(x1) $endpos(nm1)) (nm1, x1) in
      let mp2 = mk_loc (EcLocation.make $startpos(x2) $endpos(nm2)) (nm2, x2) in
        PFequivF (pre, (mp1, mp2), post) }


%inline p_form_sm_list0: aout=plist0(loc(form), SEMICOLON) { aout }
%inline form_list2: aout=plist2(loc(form), COMMA) { aout }
%inline sform_list1: aout=plist1(loc(sform), empty) { aout }

%inline pgty_varty:
| x=ident COLON ty=loc(type_exp) { (x, ty) }
;

pgtybinding1:
| LPAREN x=uident LTCOLON mi=qident RPAREN
    { [(x, PGTY_ModTy mi)] }

| LPAREN x1=ident x2=ident xs=ident* COLON t=loc(type_exp) RPAREN
    { List.map (fun x -> (x, PGTY_Type t)) (x1 :: x2 :: xs) }

| LPAREN bds=plist1(pgty_varty, COMMA) RPAREN
    { List.map (fun (x, ty) -> (x, PGTY_Type ty)) bds }

| x=ident
    { List.map (fun x -> (x, PGTY_Type (mk_loc x.pl_loc PTunivar))) [x] }

| LKEY pn=pside RKEY
    { [(pn, PGTY_Mem)] }
;

pgtybindings:
| x=pgtybinding1+ { List.flatten x }
;

(* -------------------------------------------------------------------- *)
(* Type expressions                                                     *)

simpl_type_exp:
| UNDERSCORE                  { PTunivar       }
| x=qident                    { PTnamed x      }
| x=tident                    { PTvar x        }
| tya=type_args x=qident      { PTapp (x, tya) }
| LPAREN ty=type_exp RPAREN   { ty             }
;

type_args:
| ty=loc(simpl_type_exp)                          { [ty] }
| LPAREN tys=plist2(loc(type_exp), COMMA) RPAREN  { tys  }
;

type_exp:
| ty=simpl_type_exp                              { ty }
| ty=plist2(loc(simpl_type_exp), STAR)           { PTtuple ty }
| ty1=loc(type_exp) ARROW ty2=loc(type_exp)      { PTfun(ty1,ty2) }
;

(* -------------------------------------------------------------------- *)
(* Parameter declarations                                              *)

typed_vars:
| xs=ident+ COLON ty=loc(type_exp)
   { List.map (fun v -> (v, ty)) xs }

| xs=ident+
    { List.map (fun v -> (v, mk_loc v.pl_loc PTunivar)) xs }
;

param_decl:
| LPAREN aout=plist0(typed_vars, COMMA) RPAREN { List.flatten aout }
;

param_decl1:
| LPAREN aout=plist1(typed_vars, COMMA) RPAREN { List.flatten aout }
;


(* -------------------------------------------------------------------- *)
(* Statements                                                           *)

lvalue:
| x=qident                                           { PLvSymbol x      }
| LPAREN p=plist2(qident, COMMA) RPAREN              { PLvTuple p       }
| x=qident DLBRACKET ti=tvars_app? e=loc(exp) RBRACKET { PLvMap(x, ti, e) }
;

base_instr:
| x=lvalue EQ e=loc(exp)
    { PSasgn (x, e) }

| x=lvalue EQ SAMPLE e=loc(exp)
    { PSrnd(x,e) }

| x=lvalue CEQ f=qident LPAREN es=exp_list0 RPAREN 
    { PScall (Some x, f, es) } 

| f=qident LPAREN es=exp_list0 RPAREN
    { PScall (None, f, es) }

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
(* Module definition                                                    *)

var_decl:
| VAR xs=plist1(lident, COMMA) COLON ty=loc(type_exp)
   { (xs, ty) }
;

loc_decl:
| VAR xs=plist1(ident, COMMA) COLON ty=loc(type_exp) SEMICOLON
     { (xs, ty, None  ) }

| VAR xs=plist1(ident, COMMA) COLON ty=loc(type_exp) EQ e=loc(exp) SEMICOLON
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
| x=lident pd=param_decl COLON ty=loc(type_exp)
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
    { let (x, m) = m in Pst_mod (x, m) }

| FUN decl=fun_decl EQ body=fun_def_body
    { Pst_fun (decl, body) }

| FUN x=lident EQ f=qident
    { Pst_alias (x, f) }
;

(* -------------------------------------------------------------------- *)
(* Modules                                                              *)

mod_body:
| m=qident
    { `App (m, []) }

| m=qident LPAREN a=plist1(qident, COMMA) RPAREN
    { `App (m, a) }

| LKEY stt=mod_item* RKEY
    { `Struct stt }
;

mod_def:
| MODULE x=uident p=mod_params? t=mod_ty? EQ body=mod_body
    { let p = EcUtils.odfl [] p in
        match body with
        | `App (m, args) ->
             if p <> [] then
               error (EcLocation.make $startpos $endpos)
                 "cannot parameterized module aliase";
             if t <> None then
               error (EcLocation.make $startpos $endpos)
                 "cannot bind module type to module aliase";
             (x, Pm_ident (m, args))

        | `Struct st ->
             (x, mk_mod ?modtypes:t p st) }
;

mod_params:
| LPAREN a=plist1(sig_param, COMMA) RPAREN  { a }
;

mod_ty:
| COLON t=plist1(mod_type, COMMA) { t }
;

mod_type:
| x=qident { x }
;

(* -------------------------------------------------------------------- *)
(* Modules interfaces                                                   *)

sig_def:
| MODULE TYPE x=uident args=sig_params? EQ i=sig_body
    {
      let args = EcUtils.odfl [] args in
      (x, Pmty_struct { pmsig_params = args;
                        pmsig_body   = i; })
    }
;

sig_body:
| body=sig_struct_body { body }
;

sig_struct_body:
| LKEY ty=signature_item* RKEY
    { ty }
;

sig_params:
| LPAREN params=plist1(sig_param, COMMA) RPAREN
    { params }
;

sig_param:
| x=uident COLON i=mod_type { (x, i) }
;

signature_item:
| VAR decl=ivar_decl
    { `VariableDecl decl }

| FUN decl=ifun_decl
    { `FunctionDecl decl }
;

ifun_decl:
| x=lident pd=param_decl COLON ty=loc(type_exp)
    { { pfd_name     = x   ;
        pfd_tyargs   = pd  ;
        pfd_tyresult = ty  ;
        pfd_uses     = None; }
    }

| x=lident pd=param_decl COLON ty=loc(type_exp) LKEY us=qident* RKEY
    { { pfd_name     = x      ;
        pfd_tyargs   = pd     ;
        pfd_tyresult = ty     ;
        pfd_uses     = Some us; }
    }
;

ivar_decl:
| x=lident COLON ty=loc(type_exp)
    { { pvd_name = x; pvd_type = ty } }
;

(* -------------------------------------------------------------------- *)
(* EcTypes declarations / definitions                                   *)

poly_typarams:
| empty
    { []  }

| x=tident
   { [x] }

| LPAREN xs=plist1(tident, COMMA) RPAREN
    { xs }
;

type_decl:
| TYPE tydecl=poly_typarams x=ident { (tydecl, x) }
;

type_decl_or_def:
| td=type_decl { mk_tydecl td None }
| td=type_decl EQ te=loc(type_exp) { mk_tydecl td (Some te) }
;

(* -------------------------------------------------------------------- *)
(* Operator definitions                                                 *)

op_tydom:
| LPAREN RPAREN                                  { [  ] }
| ty=loc(simpl_type_exp)                          { [ty] }
| LPAREN tys=plist2(loc(type_exp), COMMA) RPAREN { tys  }
;

op_sig:
| dom=op_tydom ARROW codom=loc(type_exp) { (Some dom, codom) }
;

op_ident:
| x=ident       { x }
| x=loc(PBINOP) { x }
;

tyvars_decl:
| LBRACKET tyvars=tident* RBRACKET { Some tyvars }
| empty { None }
    
operator:
| OP x=op_ident tyvars=tyvars_decl COLON sty=op_sig {
    { po_name   = x      ;
      po_tyvars = tyvars ;
      po_dom    = fst sty;
      po_codom  = snd sty;
      po_body   = None   ; }
  }

| OP x=op_ident tyvars=tyvars_decl p=param_decl1 COLON codom=loc(type_exp)
    EQ b=loc(exp) {
    { po_name   = x      ;
      po_tyvars = tyvars ;
      po_dom    = Some(List.map snd p);
      po_codom  = codom  ;
      po_body   = Some(List.map fst p, b); }
  }

| CNST x=ident tyvars=tyvars_decl COLON ty=loc(type_exp) {
    { po_name   = x    ;
      po_tyvars = tyvars   ;
      po_dom = None    ;
      po_codom = ty    ;
      po_body = None   ; }
  }
| CNST x=ident tyvars=tyvars_decl COLON ty=loc(type_exp) EQ e=loc(exp) {
    { po_name   = x     ;
      po_tyvars = tyvars;
      po_dom = None     ;
      po_codom = ty     ;
      po_body = Some([], e) ; }
  }
;

predicate:
| PRED x = op_ident { 
  { pp_name = x;
    pp_tyvars = None;
    pp_dom = None;
    pp_body = None; }
  }
| PRED x = op_ident tyvars=tyvars_decl COLON sty = op_tydom { 
  { pp_name = x;
    pp_tyvars = tyvars;
    pp_dom = Some sty;
    pp_body = None;
  } }
| PRED x = op_ident tyvars=tyvars_decl EQ f=loc(form) {
  { pp_name = x;
    pp_tyvars = tyvars;
    pp_dom = None;
    pp_body = Some([], f) }
  }
| PRED x = op_ident tyvars=tyvars_decl params=param_decl1 EQ f=loc(form) { 
  { pp_name = x;
    pp_tyvars = tyvars;
    pp_dom = Some(List.map snd params);
    pp_body =Some(List.map fst params, f) }
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
| SPLIT         { Hsplit }
| SAME          { Hsame }
| AUTO          { Hauto }
| empty         { Hnone }

| COMPUTE n=NUM e1=loc(exp) COMMA e2=loc(exp)
   { Hfailure (n, e1, e2, []) }

| COMPUTE n=NUM e1=loc(exp) COMMA e2=loc(exp) COLON l=plist1(ident_exp, COLON)
   { Hfailure (n, e1, e2, l) }
;

claim:
| CLAIM x=ident COLON e=loc(exp) h=real_hint { (x, (e, h)) }
;

axiom:
| AXIOM x=ident COLON e=loc(form)
    { mk_axiom (x, e) PAxiom }

| LEMMA x=ident COLON e=loc(form) i=boption(PROOF)
    { mk_axiom (x, e) (if i then PILemma else PLemma) }

| EQUIV x=ident COLON p=loc(equiv_body) i=boption(PROOF)
    { mk_axiom (x, p) (if i then PILemma else PLemma) }
;

(* -------------------------------------------------------------------- *)
(* Theory interactive manipulation                                      *)

theory_open    : THEORY  x=uident  { x }
theory_close   : END     x=uident  { x }

theory_require : 
| REQUIRE x=uident { x, None }
| REQUIRE IMPORT x=uident { x, Some false }
| REQUIRE EXPORT x=uident { x, Some true }
;

theory_import: IMPORT x=uqident { x }
theory_export: EXPORT x=uqident { x }

theory_w3:
| IMPORT WHY3 path=string_list r=plist0(renaming,SEMICOLON)
    { 
      let l = List.rev path in
      let th = List.hd l in
      let path = List.rev (List.tl l) in
      path,th,r }
;

renaming:
| TYPE l=string_list AS s=STRING { l, RNty, s }
| OP   l=string_list AS s=STRING { l, RNop, s }
| AXIOM l=string_list AS s=STRING {l, RNpr, s }
;

%inline string_list: l=plist1(STRING,empty) { l };

(* -------------------------------------------------------------------- *)
(* tactic                                                               *)

assumption_args:
| empty                   { None  , None }
| p=qident tvi=tvars_app? { Some p, tvi }
;

underscore_or_ident:
| UNDERSCORE { None }
| s=_ident   { Some s }
;

intro_args: l=plist1(loc(underscore_or_ident),empty) { l };

elim_arg :
| UNDERSCORE        { EA_none }
| f=loc(sform)      { EA_form f }
| LKEY s=pside RKEY { EA_mem s }
;

exists_args: l=plist1(loc(elim_arg), COMMA) { l };


elim_kind:
| p=qident tvi=tvars_app?           { ElimHyp(p,tvi)  }
| COLON LPAREN f=loc(form) RPAREN   { ElimForm f }
;
elim_args:
| empty { [] }
| LPAREN l=plist1(loc(elim_arg), COMMA) RPAREN { l }
;

elim: 
| k=elim_kind a=elim_args  { { elim_kind = k; elim_args = a } } 
;

simplify_arg : 
| DELTA l=plist0(qident,empty) { `Delta l }
| ZETA                         { `Zeta }
| IOTA                         { `Iota }
| BETA                         { `Beta }
| LOGIC                        { `Logic }
;
simplify :
| l=plist1(simplify_arg,empty)    { l }
| SIMPLIFY                        { simplify_red }
| SIMPLIFY l=plist1(qident,empty) { `Delta l :: simplify_red  }
| SIMPLIFY DELTA                  { `Delta [] :: simplify_red }
;

rwside :
| LEFTARROW                    { false }
| ARROW                        { true }
| empty                        { true }
;

tactic:
| IDTAC                         { Pidtac }
| ASSUMPTION a=assumption_args  { Passumption a } 
| GENERALIZE l=plist1(loc(sform), empty) {Pgeneralize l } 
| CLEAR l=plist1(ident, empty)  { Pclear l }
| TRIVIAL pi=prover_info        { Ptrivial pi }
| INTROS a=intro_args           { Pintro a }
| SPLIT                         { Psplit }
| EXIST a=exists_args           { Pexists a }
| LEFT                          { Pleft }
| RIGHT                         { Pright }
| ELIM e=elim                   { Pelim e }
| APPLY e=elim                  { Papply e }
| l=simplify                    { Psimplify (mk_simplify l) }
| CHANGE f=loc(sform)           { Pchange f }
| REWRITE s=rwside e=elim       { Prewrite (s,e) }
| SUBST l=plist0(ident, empty)  { Psubst l }
| ELIMT p=qident f=loc(sform)   { PelimT(f,p) }
| CASE  f=loc(sform)            { Pcase f }
| LPAREN s=tactics RPAREN       { Pseq s } 
(* PHL tactics *)
| APP n=number p=loc(sform)     { PPhl( Papp(n,p) ) }
| WP  n=number                  { PPhl( Pwp n) }
| WP                            { PPhl( Pwp 0) }
| SKIP                          { PPhl(Pskip) }
| WHILE inv=loc(sform) vrnt=loc(sform) bnd=loc(sform)
                                { PPhl(Pwhile(inv,vrnt,bnd)) }
| ADMIT                         { Padmit }
| CUT n=ident COLON p=loc(sform){ Pcut (n,p) }
;

tactics:
| t=loc(tactic)                        { [t] }
| t=loc(tactic) SEMICOLON ts=tactics2  { t::ts }
;

tactics0:
| ts=tactics { Pseq ts } 
;

%inline tactics2: ts=plist1(tactic2, SEMICOLON) { ts };
tsubgoal: LBRACKET ts=plist0(loc(tactics0), PIPE) RBRACKET { Psubgoal ts };

tactic2: 
| ts=loc(tsubgoal) { ts }
| t=loc(tactic)    { t } 
;

(* -------------------------------------------------------------------- *)
(* Theory cloning                                                       *)

theory_clone:
| CLONE x=uqident cw=clone_with?
   { { pthc_base = x;
       pthc_name = None;
       pthc_ext  = EcUtils.odfl [] cw; } }

| CLONE x=uqident AS y=uident cw=clone_with?
   { { pthc_base = x;
       pthc_name = Some y;
       pthc_ext  = EcUtils.odfl [] cw; } }
;

clone_with:
| WITH x=plist1(clone_override, COMMA) { x }
;

clone_override:
| TYPE ps=poly_typarams x=ident EQ t=loc(type_exp)
   { (x, PTHO_Type (ps, t)) }

| CNST x=ident EQ e=loc(exp)
   { (x, PTHO_Op ([], e)) }
;

(* -------------------------------------------------------------------- *)
(* Printing                                                             *)
print:
| TYPE   qs=qident { Pr_ty qs }
| OP     qs=qident { Pr_op qs }
| THEORY qs=qident { Pr_th qs }
| PRED   qs=qident { Pr_pr qs } 
| AXIOM  qs=qident { Pr_ax qs }
;

prover_iconfig:
| /* empty */   { (None   , None   ) }
| i=NUM         { (Some i , None   ) }
| i1=NUM i2=NUM { (Some i1, Some i2) }
;

prover_info:
| ic=prover_iconfig pl=plist1(loc(STRING), empty)? 
    { let (m, t) = ic in
        { pprov_max   = m;
          pprov_time  = t;
          pprov_names = pl; } }
;

gprover_info: 
| PROVER x=prover_info { x }
| TIMEOUT t=NUM        
    { { pprov_max = None; pprov_time = Some t; pprov_names = None } }
;

checkproof:
| CHECKPROOF ON  { true }
| CHECKPROOF OFF { false }
;

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

global_:
| theory_open      { GthOpen    $1 }
| theory_close     { GthClose   $1 }
| theory_require   { GthRequire $1 }
| theory_import    { GthImport  $1 }
| theory_export    { GthExport  $1 }
| theory_clone     { GthClone   $1 }
| theory_w3        { GthW3      $1 }
| mod_def          { Gmodule    $1 }
| sig_def          { Ginterface $1 }
| type_decl_or_def { Gtype      $1 }
| operator         { Goperator  $1 }
| predicate        { Gpredicate $1 }
| axiom            { Gaxiom     $1 }
| claim            { Gclaim     $1 }
| tactics          { Gtactics   $1 }
| gprover_info     { Gprover_info $1 }
| checkproof       { Gcheckproof $1 }
| x=loc(SAVE)      { Gsave x.pl_loc }
| PRINT p=print    { Gprint     p  }
;

stop:
| EOF { }
| DROP DOT { }
;

global:
| g=global_ FINAL { g }
;

prog:
| g=global { P_Prog ([g], false) }
| stop     { P_Prog ([ ], true ) }

| UNDO d=number FINAL
   { P_Undo d }

| error
   { error (EcLocation.make $startpos $endpos) "Parsing error" }
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

%inline list2(X):
| x=X xs=X+ { x :: xs }
;

%inline empty:
| /**/ { () }
;

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X {
    { pl_desc = x;
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }
;

%inline paren(X):
| LPAREN x=X RPAREN { x }
;
