%{
  open EcUtils
  open EcLocation
  open EcParsetree

  let parse_error loc msg = raise (ParseError (loc, msg))

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

  let opdef_of_opbody ty b =
    match b with
    | None                  -> PO_abstr ty
    | Some (args, `Expr e ) -> PO_concr (args, ty, e)
    | Some (args, `Case bs) -> PO_case  (args, ty, bs)

  let mk_peid_symb loc s ti = 
    mk_loc loc (PEident (pqsymb_of_symb loc s, ti))

  let mk_pfid_symb loc s ti = 
    mk_loc loc (PFident (pqsymb_of_symb loc s, ti))

  let peapp_symb loc s ti es = 
    PEapp (mk_peid_symb loc s ti, es)

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
      
  let pelist loc ti (es : pexpr list) : pexpr = 
    List.fold_right (fun e1 e2 -> pe_cons loc ti e1 e2) es (pe_nil loc ti)

  let pf_nil loc ti = 
    mk_pfid_symb loc EcCoreLib.s_nil ti

  let pf_cons loc ti e1 e2 = 
    mk_loc loc (pfapp_symb loc EcCoreLib.s_cons ti [e1; e2])
      
  let pflist loc ti (es : pformula    list) : pformula    = 
    List.fold_right (fun e1 e2 -> pf_cons loc ti e1 e2) es (pf_nil loc ti)

  let mk_axiom ?(local = false) ?(nosmt = false) (x, ty, vd, f) k = 
    { pa_name    = x;
      pa_tyvars  = ty;
      pa_vars    = vd;
      pa_formula = f; 
      pa_kind    = k;
      pa_nosmt   = nosmt;
      pa_local   = local; }

  let str_and b = if b then "&&" else "/\\"
  let str_or  b = if b then "||" else "\\/"

  let mk_simplify l = 
    if l = [] then
      { pbeta  = true; pzeta  = true;
        piota  = true; plogic = true;
        pdelta = None; pmodpath = true }
    else
      let doarg acc = function
        | `Delta l -> 
            if   l = [] || acc.pdelta = None
            then { acc with pdelta = None }
            else { acc with pdelta = Some (oget acc.pdelta @ l) }

        | `Zeta    -> { acc with pzeta    = true }
        | `Iota    -> { acc with piota    = true }
        | `Beta    -> { acc with pbeta    = true }
        | `Logic   -> { acc with plogic   = true }
        | `ModPath -> { acc with pmodpath = true}
      in
        List.fold_left doarg
          { pbeta  = false; pzeta  = false;
            piota  = false; plogic = false;
            pdelta = Some []; pmodpath = false } l

  let simplify_red = [`Zeta; `Iota; `Beta; `Logic; `ModPath]

  let mk_fpattern kind args =
    { fp_kind = kind;
      fp_args = args; }

  let mk_core_tactic t = { pt_core = t; pt_intros = []; }

  let mk_topmod ~local def =
    { ptm_def = def; ptm_local = local; }
%}

%token <EcSymbols.symbol> LIDENT
%token <EcSymbols.symbol> UIDENT
%token <EcSymbols.symbol> TIDENT
%token <EcSymbols.symbol> MIDENT
%token <EcSymbols.symbol> PUNIOP
%token <EcSymbols.symbol> PBINOP

%token <int> UINT
%token <string> STRING

(* Tokens *)
%token ANDA AND (* asym : &&, sym : /\ *)
%token ORA  OR  (* asym : ||, sym : \/ *)

%token <EcParsetree.codepos> CPOS

%token ADD
%token ADMIT
%token ALIAS
%token APPLY
%token ARROW
%token AS
%token ASSERT
%token ASSUMPTION
%token AT
%token AUTO
%token AXIOM
%token BACKS
%token BETA 
%token BY
%token BYEQUIV
%token BYPHOARE
%token BYPR
%token CALL
%token CASE
%token CEQ
%token CFOLD
%token CHANGE
%token CLAIM
%token CLASS
%token CLEAR
%token CLONE
%token COLON
%token COMMA
%token COMPUTE
%token CONGR
%token CONSEQ
%token CONST
%token CUT
%token DCOLON
%token DEBUG
%token DECLARE
%token DELTA
%token DLBRACKET
%token DO
%token DONE
%token DOT
%token DOTDOT
%token DOTTICK
%token DROP
%token EAGER
%token ELIM
%token ELIMT
%token ELSE
%token END
%token EOF
%token EQ
%token EQUIV
%token EXFALSO
%token EXIST
%token EXPORT
%token EXTRACTION
%token FEL
%token FIELD
%token FINAL
%token FIRST
%token FISSION
%token FORALL
%token FROM_INT
%token FUN
%token FUSION
%token FWDS
%token GENERALIZE 
%token GLOB
%token HOARE
%token IDTAC
%token IF
%token IFF
%token IMPL
%token IMPORT
%token IMPOSSIBLE
%token IN
%token INLINE
%token INSTANCE
%token INTROS
%token IOTA
%token KILL
%token LAST
%token LBRACE
%token LBRACKET
%token LEFT
%token LEFTARROW
%token LEMMA
%token LET
%token LOCAL
%token LOGIC
%token LONGARROW
%token LOSSLESS
%token LPAREN
%token LPBRACE
%token MINUS
%token MODPATH
%token MODULE
%token NE
%token NOLOCALS
%token NOSMT
%token NOT
%token OF
%token OP
%token PCENT
%token PHOARE
%token PIPE
%token POSE
%token PR
%token PRAGMA
%token PRBOUNDED
%token PRED
%token PRINT
%token PROC
%token PROGRESS
%token PROOF
%token PROVER
%token QED
%token QUESTION
%token RBOOL
%token RBRACE
%token RBRACKET
%token RCONDF
%token RCONDT
%token REALIZE
%token REFLEX
%token REQUIRE
%token RES
%token RETURN
%token REWRITE
%token RIGHT
%token RING
%token RND
%token RPAREN
%token RPBRACE
%token SAME
%token SAMPLE
%token SECTION
%token SEMICOLON
%token SEQ
%token SIM
%token SIMPLIFY
%token SKIP
%token SLASH
%token SLASHEQ
%token SLASHSLASH
%token SLASHSLASHEQ
%token SMT
%token SP
%token SPLIT
%token SPLITWHILE
%token STAR
%token STRICT
%token SUBST
%token SWAP
%token SYMMETRY
%token THEN
%token THEORY
%token TICKPIPE
%token TILD
%token TIMEOUT
%token TOP
%token TRANSITIVITY
%token TRIVIAL
%token TRY
%token TYPE
%token UNDERSCORE
%token UNDO
%token UNROLL
%token USING
%token VAR
%token WHILE
%token WHY3
%token WITH
%token WP
%token ZETA 

%token <string> OP1 OP2 OP3 OP4
%token LTCOLON GT LT GE LE

%nonassoc prec_below_comma
%nonassoc COMMA ELSE

%nonassoc IN
%nonassoc prec_below_IMPL
%right    IMPL
%nonassoc IFF
%right    ORA  OR
%right    ANDA AND
%nonassoc NOT

%nonassoc EQ NE

%nonassoc prec_below_order

%left GT LT GE LE
%left OP1
%right QUESTION
%left OP2 MINUS ADD
%right ARROW
%left OP3 STAR SLASH
%left OP4 DCOLON

%nonassoc LBRACE

%right SEMICOLON

%nonassoc prec_tactic

%type <EcParsetree.global EcLocation.located> global
%type <EcParsetree.prog   EcLocation.located> prog

%start prog global
%%

(* -------------------------------------------------------------------- *)
%inline lident: x=loc(LIDENT) { x };
%inline uident: x=loc(UIDENT) { x };
%inline tident: x=loc(TIDENT) { x };
%inline mident: x=loc(MIDENT) { x };

%inline _ident:
| x=LIDENT { x }
| x=UIDENT { x }
;

%inline ident:
| x=loc(_ident) { x }
;

%inline uint: n=UINT { n };

(* -------------------------------------------------------------------- *)
%inline namespace:
| nm=rlist1(UIDENT, DOT)
    { nm }

| TOP
    { [EcCoreLib.id_top] }

| TOP DOT nm=rlist1(UIDENT, DOT)
    { EcCoreLib.id_top :: nm }
;

_genqident(X):
| x=X { ([], x) }
| xs=namespace DOT x=X { (xs, x) }
;

genqident(X):
| x=loc(_genqident(X)) { x }
;


(* -------------------------------------------------------------------- *)
%inline  qident: x=genqident(_ident) { x };
%inline uqident: x=genqident(UIDENT) { x };
%inline lqident: x=genqident(LIDENT) { x };

(* -------------------------------------------------------------------- *)
%inline _oident:
| x=LIDENT { x }
| x=UIDENT { x }
| x=PUNIOP { x }
| x=paren(PUNIOP) { x }
| x=PBINOP { x }

| paren(DCOLON) { EcCoreLib.s_cons }

| x=loc(STRING) {
    if not (EcCoreLib.is_mixfix_op (unloc x)) then
      parse_error x.pl_loc (Some "invalid mixfix operator");
    unloc x
  }
;

%inline oident:
| x=loc(_oident) { x }
;

qoident:
| x=oident
    { pqsymb_of_psymb x }

| xs=namespace DOT x=oident {
    { pl_desc = (xs, unloc x);
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }
;

(* -------------------------------------------------------------------- *)
mod_ident1:
| x=uident
    { (x, None) }

| x=uident LPAREN args=plist1(loc(mod_qident), COMMA) RPAREN
    { (x, Some args) }
;

%inline mod_qident:
| x=rlist1(mod_ident1, DOT) { x }
;

fident:
| nm=mod_qident DOT x=lident { (nm, x) }
| x=lident { ([], x) }
;

(* -------------------------------------------------------------------- *)
%inline ordering_op:
| GT { ">"  }
| LT { "<"  }
| GE { ">=" }
| LE { "<=" }
;

%inline uniop:
| x=OP1 { Printf.sprintf "[%s]" x }
| ADD   { "[+]" }
| MINUS { "[-]" }

(* -------------------------------------------------------------------- *)
%inline or_:
| ORA { true  }
| OR  { false }

%inline and_:
| ANDA { true  }
| AND  { false }

(* -------------------------------------------------------------------- *)
pside_:
| x=LIDENT     { (0, Printf.sprintf "&%s" x) }
| x=UINT       { (0, Printf.sprintf "&%d" x) }
| ADD x=pside_ { (1 + fst x, snd x) }
;

pside:
| x=brace(pside_) { x }
;

(* -------------------------------------------------------------------- *)
(* Patterns                                                             *)

lpattern_u:
| x=ident
    { LPSymbol x }

| LPAREN p=plist2(ident, COMMA) RPAREN
    { LPTuple p }

| LPBRACE fs=rlist1(lp_field, SEMICOLON) SEMICOLON? RPBRACE
    { LPRecord fs }
;

lp_field:
| f=qident EQ x=ident { (f, x) }
;

%inline lpattern:
| x=loc(lpattern_u) { x }
;

(* -------------------------------------------------------------------- *)
(* Expressions: program expression, real expression                     *)

tyvar_byname1:
| x=tident EQ ty=loc(type_exp) { (x, ty) }
;

tyvar_annot:
| lt = plist1(loc(type_exp), COMMA) { TVIunamed lt }
| lt = plist1(tyvar_byname1, COMMA) { TVInamed lt }
;

%inline tvars_app:
| LTCOLON k=loc(tyvar_annot) GT { k }
;

(* -------------------------------------------------------------------- *)
%inline sexpr: x=loc(sexpr_u) { x };
%inline  expr: x=loc( expr_u) { x };

sexpr_u:
| e=sexpr PCENT p=uqident
   { PEscope (p, e) }

| e=sexpr PCENT p=lident
   { if unloc p <> "top" then
       parse_error p.pl_loc (Some "invalid scope name");
     PEscope (pqsymb_of_symb p.pl_loc "<top>", e) }

| n=uint
   { PEint n }

| x=qoident ti=tvars_app?
   { PEident (x, ti) }

| se=sexpr op=loc(FROM_INT)
   { let id =
       PEident (mk_loc op.pl_loc EcCoreLib.s_real_of_int, None)
     in
       PEapp (mk_loc op.pl_loc id, [se]) }

| se=sexpr DLBRACKET ti=tvars_app? e=expr RBRACKET
   { peget (EcLocation.make $startpos $endpos) ti se e }

| se=sexpr DLBRACKET ti=tvars_app? e1=expr LEFTARROW e2=expr RBRACKET  
   { peset (EcLocation.make $startpos $endpos) ti se e1 e2 }

| TICKPIPE ti=tvars_app? e=expr PIPE 
   { peapp_symb e.pl_loc EcCoreLib.s_abs ti [e] }

| LBRACKET ti=tvars_app? es=loc(plist0(expr, SEMICOLON)) RBRACKET  
   { unloc (pelist es.pl_loc ti es.pl_desc) } 

| LBRACKET ti=tvars_app? e1=expr op=loc(DOTDOT) e2=expr RBRACKET
   { let id =
       PEident (mk_loc op.pl_loc EcCoreLib.s_dinter, ti)
     in
       PEapp(mk_loc op.pl_loc id, [e1; e2]) }

| LPAREN es=plist0(expr, COMMA) RPAREN
   { PEtuple es }

| r=loc(RBOOL)
   { PEident (mk_loc r.pl_loc EcCoreLib.s_dbool, None) }

| LPBRACE fields=rlist1(expr_field, SEMICOLON) SEMICOLON? RPBRACE
   { PErecord fields }

| e=sexpr DOTTICK x=qident
   { PEproj (e, x) }
| e=sexpr DOTTICK n=loc(uint) 
   { if n.pl_desc = 0 then 
       parse_error n.pl_loc (Some "tuple projection start at 1");
     PEproji(e,n.pl_desc - 1) }
;

expr_u:
| e=sexpr_u { e }

| e=sexpr args=sexpr+
    { PEapp (e, args) }

| op=loc(NOT) ti=tvars_app? e=expr
    { peapp_symb op.pl_loc "[!]" ti [e] }

| op=loc(uniop) ti=tvars_app? e=expr
    { peapp_symb op.pl_loc op.pl_desc ti [e] } 

| e=expr_chained_orderings %prec prec_below_order
   { fst e }

| e1=expr op=loc(OP1) ti=tvars_app? e2=expr 
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=expr op=loc(EQ) ti=tvars_app? e2=expr
    { peapp_symb op.pl_loc "=" ti [e1; e2] }

| e1=expr op=loc(NE) ti=tvars_app? e2=expr
    { peapp_symb op.pl_loc "[!]" None 
      [ mk_loc op.pl_loc (peapp_symb op.pl_loc "=" ti [e1; e2])] }

| e1=expr op=loc(ADD) ti=tvars_app? e2=expr 
    { peapp_symb op.pl_loc "+" ti [e1; e2] }

| e1=expr op=loc(MINUS) ti=tvars_app? e2=expr 
    { peapp_symb op.pl_loc "-" ti [e1; e2] }

| e1=expr op=loc(OP2) ti=tvars_app? e2=expr 
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=expr op=loc(OP3) ti=tvars_app? e2=expr 
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=expr op=loc(OP4) ti=tvars_app? e2=expr 
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=expr op=loc(DCOLON) ti=tvars_app? e2=expr 
    { peapp_symb op.pl_loc EcCoreLib.s_cons ti [e1; e2] }

| e1=expr op=loc(IMPL) ti=tvars_app? e2=expr
    { peapp_symb op.pl_loc "=>" ti [e1; e2] }

| e1=expr op=loc(IFF) ti=tvars_app? e2=expr 
    { peapp_symb op.pl_loc "<=>" ti [e1; e2] }

| e1=expr op=loc(or_) ti=tvars_app? e2=expr  
    { peapp_symb op.pl_loc (str_or op.pl_desc) ti [e1; e2] }

| e1=expr op=loc(and_) ti=tvars_app? e2=expr 
    { peapp_symb op.pl_loc (str_and op.pl_desc) ti [e1; e2] }

| e1=expr op=loc(STAR) ti=tvars_app?  e2=expr  
    { peapp_symb op.pl_loc "*" ti [e1; e2] }

| e1=expr op=loc(SLASH) ti=tvars_app?  e2=expr  
    { peapp_symb op.pl_loc "/" ti [e1; e2] }

| c=expr QUESTION e1=expr COLON e2=expr %prec OP2
   { PEif (c, e1, e2) }

| IF c=expr THEN e1=expr ELSE e2=expr
   { PEif (c, e1, e2) }

| LET p=lpattern EQ e1=expr IN e2=expr
   { PElet (p, e1, e2) }

| r=loc(RBOOL) TILD e=sexpr
    { let id  = PEident(mk_loc r.pl_loc EcCoreLib.s_dbitstring, None) in
      let loc = EcLocation.make $startpos $endpos in
        PEapp (mk_loc loc id, [e]) }

| FUN pd=ptybindings COMMA e=expr { PElambda (pd, e) } 
;

expr_field:
| x=qident EQ e=expr
    { { rf_name = x ; rf_tvi = None; rf_value = e; } }
;

expr_ordering:
| e1=expr op=loc(ordering_op) ti=tvars_app? e2=expr
    { (op, ti, e1, e2) }
;

expr_chained_orderings:
| e=expr_ordering
    { let (op, ti, e1, e2) = e in
        (peapp_symb op.pl_loc (unloc op) ti [e1; e2], e2) }

| e1=loc(expr_chained_orderings) op=loc(ordering_op) ti=tvars_app? e2=expr
    { let (lce1, (e1, le)) = (e1.pl_loc, unloc e1) in
      let loc = EcLocation.make $startpos $endpos in
        (peapp_symb loc (str_and true) None
           [EcLocation.mk_loc lce1 e1;
            EcLocation.mk_loc loc
              (peapp_symb op.pl_loc (unloc op) ti [le; e2])],
         e2) }
;

%inline pty_varty:
| x=ident+
   { let loc = EcLocation.make $startpos $endpos in
       (x, mk_loc loc PTunivar) }

| x=ident+ COLON ty=loc(type_exp)
   { (x, ty) }
;

ptybinding1:
| LPAREN bds=plist1(pty_varty, COMMA) RPAREN { bds }
| x=ident { [[x], mk_loc x.pl_loc PTunivar] }
;

ptybindings:
| x=ptybinding1+ { List.flatten x } 
;

(* -------------------------------------------------------------------- *)
(* Formulas                                                             *)

%inline sform_r(P): x=loc(sform_u(P)) { x }
%inline  form_r(P): x=loc( form_u(P)) { x }

%inline sform: x=sform_r(none) { x }
%inline  form: x=form_r (none) { x }

%inline sform_h: x=loc(sform_u(hole)) { x }
%inline  form_h: x=loc( form_u(hole)) { x }

%inline hole: UNDERSCORE { PFhole; }
%inline none: IMPOSSIBLE { assert false; }

qident_or_res_or_glob:
| x=qident   { GVvar x }
| x=loc(RES) { GVvar (mk_loc x.pl_loc ([], "res")) }
| GLOB mp=loc(mod_qident) { GVglob mp }

sform_u(P):
| x=P 
   { x }

| f=sform_r(P) PCENT p=qident
   { PFscope (p, f) }

| n=uint
   { PFint n }

| x=loc(RES)
   { PFident (mk_loc x.pl_loc ([], "res"), None) }

| x=qoident ti=tvars_app?
   { PFident (x, ti) }

| se=sform_r(P) op=loc(FROM_INT)
   { let id = PFident(mk_loc op.pl_loc EcCoreLib.s_real_of_int, None) in
     PFapp (mk_loc op.pl_loc id, [se]) }

| se=sform_r(P) DLBRACKET ti=tvars_app? e=form_r(P) RBRACKET
   { pfget (EcLocation.make $startpos $endpos) ti se e }

| se=sform_r(P) DLBRACKET ti=tvars_app? e1=form_r(P) LEFTARROW e2=form_r(P) RBRACKET
   { pfset (EcLocation.make $startpos $endpos) ti se e1 e2 }

| x=sform_r(P) s=loc(pside)
   { PFside (x, s) }

| TICKPIPE ti=tvars_app? e =form_r(P) PIPE 
   { pfapp_symb e.pl_loc EcCoreLib.s_abs ti [e] }

| LPAREN fs=plist0(form_r(P), COMMA) RPAREN
   { PFtuple fs }

| LPBRACE fields=rlist1(form_field, SEMICOLON) SEMICOLON? RPBRACE
   { PFrecord fields }

| LBRACKET ti=tvars_app? es=loc(plist0(form_r(P), SEMICOLON)) RBRACKET
   { (pflist es.pl_loc ti es.pl_desc).pl_desc }

| f=sform_r(P) DOTTICK x=qident
    { PFproj (f, x) }

| f=sform_r(P) DOTTICK n=loc(uint) 
   { if n.pl_desc = 0 then 
       parse_error n.pl_loc (Some "tuple projection start at 1");
     PFproji(f,n.pl_desc - 1) }

| HOARE LBRACKET hb=hoare_body(P) RBRACKET { hb }

| EQUIV LBRACKET eb=equiv_body(P) RBRACKET { eb }

| EAGER LBRACKET eb=eager_body(P) RBRACKET { eb }

| HOARE LBRACKET
    s=loc(fun_def_body)
    COLON pre=form_r(P) LONGARROW post=form_r(P)
  RBRACKET
	{ PFhoareS (pre, s, post) }

| PR LBRACKET
    mp=loc(fident) args=paren(plist0(form_r(P), COMMA)) AT pn=mident
    COLON event=form_r(P)
  RBRACKET
    { PFprob (mp, args, pn, event) }

| r=loc(RBOOL)
    { PFident (mk_loc r.pl_loc EcCoreLib.s_dbool, None) }

| LBRACKET ti=tvars_app? e1=form_r(P) op=loc(DOTDOT) e2=form_r(P) RBRACKET
    { let id = PFident(mk_loc op.pl_loc EcCoreLib.s_dinter, ti) in
      PFapp(mk_loc op.pl_loc id, [e1; e2]) } 
;
                          
form_u(P):
| GLOB mp=loc(mod_qident) { PFglob mp }

| e=sform_u(P) { e }

| e=sform_r(P) args=sform_r(P)+ { PFapp (e, args) } 

| op=loc(NOT) ti=tvars_app? e=form_r(P) 
    { pfapp_symb  op.pl_loc "[!]" ti [e] }

| op=loc(uniop) ti=tvars_app? e=form_r(P)
   { pfapp_symb op.pl_loc op.pl_desc ti [e] } 

| e1=form_r(P) op=loc(OP1) ti=tvars_app? e2=form_r(P)
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] } 

| f=form_chained_orderings(P) %prec prec_below_order
    { fst f }

| e1=form_r(P) op=loc(EQ) ti=tvars_app? e2=form_r(P)
    { pfapp_symb op.pl_loc "=" ti [e1; e2] }

| e1=form_r(P) op=loc(NE) ti=tvars_app? e2=form_r(P)
    { pfapp_symb op.pl_loc "[!]" None 
      [ mk_loc op.pl_loc (pfapp_symb op.pl_loc "=" ti [e1; e2])] }

| e1=form_r(P) op=loc(MINUS) ti=tvars_app? e2=form_r(P)
    { pfapp_symb op.pl_loc "-" ti [e1; e2] }

| e1=form_r(P) op=loc(ADD) ti=tvars_app? e2=form_r(P) 
    { pfapp_symb op.pl_loc "+" ti [e1; e2] }

| e1=form_r(P) op=loc(OP2) ti=tvars_app? e2=form_r(P)  
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=form_r(P) op=loc(OP3) ti=tvars_app? e2=form_r(P)  
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=form_r(P) op=loc(OP4) ti=tvars_app? e2=form_r(P)  
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| e1=form_r(P) op=loc(DCOLON) ti=tvars_app? e2=form_r(P)
    { pfapp_symb op.pl_loc EcCoreLib.s_cons ti [e1; e2] }

| e1=form_r(P) op=loc(IMPL) ti=tvars_app? e2=form_r(P)  
    { pfapp_symb op.pl_loc "=>" ti [e1; e2] }

| e1=form_r(P) op=loc(IFF) ti=tvars_app? e2=form_r(P)  
    { pfapp_symb op.pl_loc "<=>" ti [e1; e2] }

| e1=form_r(P) op=loc(or_) ti=tvars_app? e2=form_r(P)  
    { pfapp_symb op.pl_loc (str_or op.pl_desc) ti [e1; e2] }

| e1=form_r(P) op=loc(and_) ti=tvars_app? e2=form_r(P)  
    { pfapp_symb op.pl_loc (str_and op.pl_desc) ti [e1; e2] }

| e1=form_r(P) op=loc(STAR) ti=tvars_app? e2=form_r(P)  
    { pfapp_symb op.pl_loc "*" ti [e1; e2] }

| e1=form_r(P) op=loc(SLASH) ti=tvars_app? e2=form_r(P)  
    { pfapp_symb op.pl_loc "/" ti [e1; e2] }

| c=form_r(P) QUESTION e1=form_r(P) COLON e2=form_r(P) %prec OP2
    { PFif (c, e1, e2) }

| EQ LBRACE xs=plist1(qident_or_res_or_glob, COMMA) RBRACE
    { PFeqveq xs }

| IF c=form_r(P) THEN e1=form_r(P) ELSE e2=form_r(P)
    { PFif (c, e1, e2) }

| LET p=lpattern EQ e1=form_r(P) IN e2=form_r(P)
    { PFlet (p, e1, e2) }

| FORALL pd=pgtybindings COMMA e=form_r(P) { PFforall (pd, e) }
| EXIST  pd=pgtybindings COMMA e=form_r(P) { PFexists (pd, e) }
| FUN    pd=ptybindings  COMMA e=form_r(P) { PFlambda (pd, e) }

| r=loc(RBOOL) TILD e=sform_r(P)
    { let id  = PFident (mk_loc r.pl_loc EcCoreLib.s_dbitstring, None) in
      let loc = EcLocation.make $startpos $endpos in
        PFapp (mk_loc loc id, [e]) }

| PHOARE pb=phoare_body(P) { pb }

| PHOARE 
    LBRACKET s=loc(fun_def_body) COLON
      pre=form_r(P) LONGARROW post=form_r(P)
    RBRACKET
      cmp=hoare_bd_cmp bd=sform_r(P)
	{ PFBDhoareS (pre, s, post, cmp, bd) }

| LOSSLESS mp=loc(fident)
    { PFlsless mp }
;

form_field:
| x=qident EQ f=form
    { { rf_name = x; rf_tvi = None; rf_value = f; } }
;

form_ordering(P):
| f1=form_r(P) op=loc(ordering_op) ti=tvars_app? f2=form_r(P)
    { (op, ti, f1, f2) }
;

form_chained_orderings(P):
| f=form_ordering(P)
    { let (op, ti, f1, f2) = f in
        (pfapp_symb op.pl_loc (unloc op) ti [f1; f2], f2) }

| f1=loc(form_chained_orderings(P)) op=loc(ordering_op) ti=tvars_app? f2=form_r(P)
    { let (lcf1, (f1, le)) = (f1.pl_loc, unloc f1) in
      let loc = EcLocation.make $startpos $endpos in
        (pfapp_symb loc (str_and true) None
           [EcLocation.mk_loc lcf1 f1;
            EcLocation.mk_loc loc
              (pfapp_symb op.pl_loc (unloc op) ti [le; f2])],
         f2) }
;

hoare_bd_cmp :
| LE {PFHle}
| EQ {PFHeq}
| GE {PFHge}

hoare_body(P):
  mp=loc(fident) COLON pre=form_r(P) LONGARROW post=form_r(P)
    { PFhoareF (pre, mp, post) }
;

phoare_body(P):
  LBRACKET mp=loc(fident) COLON
    pre=form_r(P) LONGARROW post=form_r(P)
  RBRACKET
    cmp=hoare_bd_cmp bd=sform_r(P)
  { PFBDhoareF (pre, mp, post, cmp, bd) }
;

equiv_body(P):
  mp1=loc(fident) TILD mp2=loc(fident)
  COLON pre=form_r(P) LONGARROW post=form_r(P)
    { PFequivF (pre, (mp1, mp2), post) }
;

eager_body(P):
| s1=stmt COMMA  mp1=loc(fident) TILD mp2=loc(fident) COMMA s2=stmt
    COLON pre=form_r(P) LONGARROW post=form_r(P)
    { PFeagerF (pre, (s1, mp1, mp2,s2), post) }
;

pgtybinding1:
| x=ptybinding1 { List.map (fun (xs,ty) -> xs, PGTY_Type ty) x }

| LPAREN x=uident LTCOLON mi=mod_type_restr RPAREN
    { [[x], PGTY_ModTy mi] }

| pn=mident
    { [[pn], PGTY_Mem] }
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
| GLOB m=loc(mod_qident)      { PTglob m       }
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
| LPAREN aout=plist0(typed_vars, COMMA) RPAREN 
    { Fparams_exp (List.flatten aout )}

| LPAREN UNDERSCORE COLON ty=loc(type_exp) RPAREN
    { Fparams_imp ty } 
;

(* -------------------------------------------------------------------- *)
(* Statements                                                           *)

lvalue_u:
| x=qident
   { PLvSymbol x }

| LPAREN p=plist2(qident, COMMA) RPAREN
   { PLvTuple p }

| x=qident DLBRACKET ti=tvars_app? e=expr RBRACKET
   { PLvMap(x, ti, e) }
;

%inline lvalue:
| x=loc(lvalue_u) { x }
;

base_instr:
| x=lvalue EQ SAMPLE e=expr
    { PSrnd (x, e) }

| x=lvalue EQ e=expr
    { let islow = function 'a'..'z' -> true | _ -> false in
      let islow = fun s -> s <> "" && islow s.[0] in

        match unloc e with
        | PEapp ( { pl_desc = PEident (({ pl_desc = (_, fx) } as f), None) },
                 [{ pl_desc = PEtuple es; pl_loc = les; }])
            when islow fx ->
          begin
            PScall (Some x, f, mk_loc les es)
          end
        | _ -> PSasgn (x, e) }

| f=qident LPAREN es=loc(plist0(expr, COMMA)) RPAREN
    { PScall (None, f, es) }

| ASSERT LPAREN c=expr RPAREN 
    { PSassert c }
;

instr:
| bi=base_instr SEMICOLON
   { bi }

| IF LPAREN c=expr RPAREN b1=block ELSE b2=block
   { PSif (c, b1, b2) }

| IF LPAREN c=expr RPAREN b=block
   { PSif (c, b , []) }

| WHILE LPAREN c=expr RPAREN b=block
   { PSwhile (c, b) }
;

block:
| i=loc(base_instr) SEMICOLON
    { [i] }

| stmt=brace(stmt)
   { stmt }
;

stmt: aout=loc(instr)* { aout }

(* -------------------------------------------------------------------- *)
(* Module definition                                                    *)

var_decl:
| VAR xs=plist1(lident, COMMA) COLON ty=loc(type_exp)
   { (xs, ty) }
;

loc_decl_names:
| x=plist1(lident, COMMA) { (`Single, x) }

| LPAREN x=plist2(lident, COMMA) RPAREN { (`Tuple, x) }
;

loc_decl_r:
| VAR x=loc(loc_decl_names)
    { { pfl_names = x; pfl_type = None; pfl_init = None; } }

| VAR x=loc(loc_decl_names) COLON ty=loc(type_exp)
    { { pfl_names = x; pfl_type = Some ty; pfl_init = None; } }

| VAR x=loc(loc_decl_names) COLON ty=loc(type_exp) EQ e=expr
    { { pfl_names = x; pfl_type = Some ty; pfl_init = Some e; } }

| VAR x=loc(loc_decl_names) EQ e=expr
    { { pfl_names = x; pfl_type = None; pfl_init = Some e; } }
;

loc_decl:
| x=loc_decl_r SEMICOLON { x }
;

ret_stmt:
| RETURN e=expr SEMICOLON
    { Some e }

| empty
    { None }
;

fun_def_body:
| LBRACE decl=loc_decl* s=stmt rs=ret_stmt RBRACE
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
        pfd_uses     = (true, None); }
    }
; 


mod_item:
| v=var_decl
    { Pst_var v }

| m=mod_def
    { let (x, m) = m in Pst_mod (x, m) }

| PROC decl=loc(fun_decl) EQ body=fun_def_body { 
    let { pl_loc = loc; pl_desc = decl; } = decl in
        match decl.pfd_tyargs with
        | Fparams_imp _ ->
            let msg = "implicite declaration of parameters not allowed" in
              parse_error loc (Some msg)
        | _ -> Pst_fun (decl, body)
  }

| PROC x=lident EQ f=loc(fident)
    { Pst_alias (x, f) }
;

(* -------------------------------------------------------------------- *)
(* Modules                                                              *)

mod_body:
| m=mod_qident
    { `Alias m }

| LBRACE stt=loc(mod_item)* RBRACE
    { `Struct stt }
;

mod_def:
| MODULE x=uident p=mod_params? t=mod_aty? EQ body=loc(mod_body)
    { let p = EcUtils.odfl [] p in
        match body.pl_desc with
        | `Alias m ->
            (* if p <> [] then
               parse_error (EcLocation.make $startpos $endpos)
                 (Some "cannot parameterize module alias"); *)
             if t <> None then
               parse_error (EcLocation.make $startpos $endpos)
                 (Some "cannot bind module type to module alias"); 
             (x, mk_loc body.pl_loc (Pm_ident(p, m)))

        | `Struct st ->
             (x, mk_loc body.pl_loc (mk_mod ?modtypes:t p st)) }
;

top_mod_def:
| x=mod_def
    { mk_topmod ~local:false x }

| LOCAL x=mod_def
    { mk_topmod ~local:true  x }
;

top_mod_decl:
| DECLARE MODULE x=uident COLON t=mod_type_restr
    { { ptmd_name = x; ptmd_modty = t; } }
;

mod_params:
| LPAREN a=plist1(sig_param, COMMA) RPAREN  { a }
;

mod_aty:
| COLON t=plist1(loc(mod_aty1), COMMA) { t }
;

mod_aty1:
| x=qident { (x, []) }
| x=qident xs=paren(ident+) { (x, xs) }
;

(* -------------------------------------------------------------------- *)
(* Modules interfaces                                                   *)

%inline mod_type:
| x = qident { x }
;

%inline mod_type_restr:
| x = qident
    { (x, []) }

| x = qident LBRACE restr=plist1(loc(mod_qident), COMMA) RBRACE
    { (x, restr) }
;

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
| LBRACE ty=signature_item* RBRACE
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
| PROC i=boption(STAR) x=lident pd=param_decl COLON ty=loc(type_exp) qs=brace(qident*)?
    { `FunctionDecl
          { pfd_name     = x;
            pfd_tyargs   = pd;
            pfd_tyresult = ty;
            pfd_uses     = (not i, qs); } }
;

(* -------------------------------------------------------------------- *)
(* EcTypes declarations / definitions                                   *)

typaram:
| x=tident { (x, []) }
| x=tident LTCOLON tc=plist1(lqident, tcand) { (x, tc) }
;

typarams:
| empty { []  }
| x=tident { [(x, [])] }
| xs=paren(plist1(typaram, COMMA)) { xs }
;

%inline tyd_name:
| tya=typarams x=ident { (tya, x) }
;

tcand:
| x=loc(OP4) { if unloc x <> "&" then parse_error x.pl_loc None }
;

dt_ctor_def:
| x=ident { (x, []) }
| x=ident OF ty=plist1(loc(simpl_type_exp), tcand) { (x, ty) }
;

%inline datatype_def:
| LBRACKET PIPE? ctors=plist1(dt_ctor_def, PIPE) RBRACKET { ctors }
;

rec_field_def:
| x=ident COLON ty=loc(type_exp) { (x, ty); }
;

%inline record_def:
| LBRACE fields=rlist1(rec_field_def, SEMICOLON) SEMICOLON? RBRACE
    { fields }
;

typedecl:
| TYPE td=rlist1(tyd_name, COMMA)
    { List.map (mk_tydecl^~ PTYD_Abstract) td }

| TYPE td=tyd_name EQ te=loc(type_exp)
    { [mk_tydecl td (PTYD_Alias te)] }

| TYPE td=tyd_name EQ te=record_def
    { [mk_tydecl td (PTYD_Record te)] }

| TYPE td=tyd_name EQ te=datatype_def
    { [mk_tydecl td (PTYD_Datatype te)] }
;


(* -------------------------------------------------------------------- *)
(* Type classes                                                         *)
typeclass:
| TYPE CLASS x=lident inth=tc_inth? EQ LBRACE body=tc_body RBRACE {
    { ptc_name = x;
      ptc_inth = inth;
      ptc_ops  = fst body;
      ptc_axs  = snd body; }
  }
;

tc_inth:
| LTCOLON x=lqident { x }
;

tc_body: ops=tc_op* axs=tc_ax* { (ops, axs) };

tc_op: OP x=lident COLON ty=loc(type_exp) { (x, ty) };

tc_ax: AXIOM ax=form { ax };

(* -------------------------------------------------------------------- *)
(* Type classes (instances)                                             *)
tycinstance:
| INSTANCE x=qident WITH ty=qident ops=tyci_op* axs=tyci_ax* {
    { pti_name = x;
      pti_type = ty;
      pti_ops  = ops;
      pti_axs  = axs; }
  }
;

tyci_op:
| OP x=ident EQ tg=qoident { (x, tg) }
;

tyci_ax:
| PROOF x=ident BY tg=tactic_core { (x, tg) }
;

(* -------------------------------------------------------------------- *)
(* Operator definitions                                                 *)

op_tydom:
| LPAREN RPAREN
    { [  ] }

| ty=loc(simpl_type_exp)
   { [ty] }

| tys=paren(plist2(loc(type_exp), COMMA))
   { tys  }
;

tyvars_decl:
| LBRACKET tyvars=typaram* RBRACKET { tyvars }
;

%inline op_or_const:
| OP    { `Op }
| CONST { `Const }
;

operator:
| k=op_or_const x=oident tyvars=tyvars_decl? COLON sty=loc(type_exp) {
    { po_kind   = k;
      po_name   = x;
      po_tyvars = tyvars;
      po_def    = opdef_of_opbody sty None; }
  }

| k=op_or_const x=oident tyvars=tyvars_decl? COLON sty=loc(type_exp) EQ b=opbody {
    { po_kind   = k;
      po_name   = x;
      po_tyvars = tyvars;
      po_def    = opdef_of_opbody sty (Some ([], b)); }
  }

| k=op_or_const x=oident tyvars=tyvars_decl? eq=loc(EQ) b=opbody {
    { po_kind   = k;
      po_name   = x;
      po_tyvars = tyvars;
      po_def    = opdef_of_opbody (mk_loc eq.pl_loc PTunivar) (Some ([], b)); }
  }

| k=op_or_const x=oident tyvars=tyvars_decl? p=ptybindings eq=loc(EQ) b=opbody {
    { po_kind   = k;
      po_name   = x;
      po_tyvars = tyvars;
      po_def    = opdef_of_opbody (mk_loc eq.pl_loc PTunivar) (Some (p, b)); }
  }

| k=op_or_const x=oident tyvars=tyvars_decl? p=ptybindings COLON codom=loc(type_exp) EQ b=opbody {
    { po_kind   = k;
      po_name   = x;
      po_tyvars = tyvars;
      po_def    = opdef_of_opbody codom (Some (p, b)); }
  }
;

opbody:
| e=expr     { `Expr e  }
| bs=opcase+ { `Case bs }
;

opcase:
| WITH ptn=plist1(opptn, COMMA) IMPL e=expr
   { { pop_patterns = ptn; pop_body = e; } }
;

opptn:
| x=ident EQ c=qoident tvi=tvars_app? ps=ident*
    { { pop_name = x; pop_tvi = tvi; pop_pattern = (c, ps); } }
;

predicate:
| PRED x = oident
   { { pp_name   = x;
       pp_tyvars = None;
       pp_def    = PPabstr []; } }

| PRED x = oident tyvars=tyvars_decl? COLON sty = op_tydom
   { { pp_name   = x;
       pp_tyvars = tyvars;
       pp_def    = PPabstr sty; } }

| PRED x = oident tyvars=tyvars_decl? p=ptybindings EQ f=form
   { { pp_name   = x;
       pp_tyvars = tyvars;
       pp_def    = PPconcr(p,f); } } 
;

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

%inline ident_exp:
| x=ident COMMA e=expr { (x, e) }
;

real_hint:
| USING x=ident { Husing x }
| ADMIT         { Hadmit }
| COMPUTE       { Hcompute }
| SPLIT         { Hsplit }
| SAME          { Hsame }
| AUTO          { Hauto }
| empty         { Hnone }

| COMPUTE n=uint e1=expr COMMA e2=expr
   { Hfailure (n, e1, e2, []) }

| COMPUTE n=uint e1=expr COMMA e2=expr COLON l=plist1(ident_exp, COLON)
   { Hfailure (n, e1, e2, l) }
;

claim:
| CLAIM x=ident COLON e=expr h=real_hint { (x, (e, h)) }
;

lemma_decl :
| x=ident tyvars=tyvars_decl? pd=pgtybindings? COLON f=form { x,tyvars,pd,f }
;

nosmt:
| NOSMT { true  }
| empty { false }
;

%inline local:
| LOCAL { true  }
| empty { false }
;

axiom_tc:
| /* empty */       { PILemma }
| BY bracket(empty) { PLemma None }
| BY t=tactic       { PLemma (Some t) }
;

axiom:
| l=local AXIOM o=nosmt d=lemma_decl 
    { mk_axiom ~local:l ~nosmt:o d PAxiom }

| l=local LEMMA o=nosmt d=lemma_decl ao=axiom_tc
    { mk_axiom ~local:l ~nosmt:o d ao }

| l=local  EQUIV x=ident pd=pgtybindings? COLON p=loc( equiv_body(none)) ao=axiom_tc
| l=local  HOARE x=ident pd=pgtybindings? COLON p=loc( hoare_body(none)) ao=axiom_tc
| l=local PHOARE x=ident pd=pgtybindings? COLON p=loc(phoare_body(none)) ao=axiom_tc
    { mk_axiom ~local:l (x, None, pd, p) ao }
;

(* -------------------------------------------------------------------- *)
(* Theory interactive manipulation                                      *)

theory_open  : THEORY  x=uident  { x }
theory_close : END     x=uident  { x }

section_open  : SECTION     { () }
section_close : END SECTION { () }

import_flag:
| IMPORT { `Import }
| EXPORT { `Export }
;

theory_require : 
| REQUIRE ip=import_flag? x=uident { (x, ip) }
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
(* pattern selection (tactics)                                          *)
idpattern:
| x=ident { [x] }
| LBRACKET xs=ident+ RBRACKET { xs }
;

ipattern:
| UNDERSCORE
    { PtAny }

| UNDERSCORE CEQ f=idpattern LPAREN UNDERSCORE RPAREN
    { PtAsgn f }

| IF UNDERSCORE LBRACE p=spattern RBRACE
    { PtIf (p, `NoElse) }

| IF UNDERSCORE LBRACE p=spattern RBRACE UNDERSCORE
    { PtIf (p, `MaybeElse) }

| IF UNDERSCORE LBRACE p1=spattern RBRACE ELSE LBRACE p2=spattern RBRACE
    { PtIf (p1, `Else p2) }

| WHILE UNDERSCORE LBRACE p=spattern RBRACE
    { PtWhile p }
;

spattern:
| UNDERSCORE { () }
;

tselect:
| p=ipattern { p }
;

(* -------------------------------------------------------------------- *)
(* tactic                                                               *)

intro_pattern_1_name:
| s=LIDENT   { s }
| s=UIDENT   { s }
| s=MIDENT   { s }
;

intro_pattern_1:
| UNDERSCORE
    { `NoName }

| QUESTION
   { `FindName }

| s=intro_pattern_1_name
    {`NoRename s}

| s=intro_pattern_1_name NOT
    {`WithRename s}
;

intro_pattern:
| x=loc(intro_pattern_1)
   { IPCore x }

| LBRACKET RBRACKET
   { IPCase [] }

| LBRACKET ip=intro_pattern+ RBRACKET
   { IPCase [ip] }

| LBRACKET ip=plist2(intro_pattern*, PIPE) RBRACKET
   { IPCase ip }

| o=rwocc? ARROW
   { IPRw (o |> omap EcMaps.Sint.of_list, `LtoR) }

| o=rwocc? LEFTARROW
   { IPRw (o |> omap EcMaps.Sint.of_list, `RtoL) }

| LBRACE xs=ident+ RBRACE
   { IPClear xs }

| SLASHSLASH
   { IPDone false }

| SLASHSLASHEQ
   { IPDone true }

| SLASHEQ
   { IPSimplify }
;

fpattern_head(F):
| p=qident tvi=tvars_app?
   { FPNamed (p, tvi) }

| LPAREN UNDERSCORE COLON f=F RPAREN
   { FPCut f }
;

fpattern_arg:
| UNDERSCORE
    { EA_none }

| LPAREN LTCOLON m=loc(mod_qident) RPAREN
    { EA_mod m }

| f=sform
    { EA_form f }

| s=mident
    { EA_mem s }
;

fpattern(F):
| hd=fpattern_head(F)
   { mk_fpattern hd [] }

| LPAREN hd=fpattern_head(F) args=loc(fpattern_arg)* RPAREN
   { mk_fpattern hd args }
;

fpattern_list(F):
| f=fpattern(F)
    { [f] }

| LPAREN fs=rlist2(fpattern(F), COMMA) RPAREN
    { fs }
;

pterm:
| p=qident tvi=tvars_app? args=loc(fpattern_arg)*
    { { pt_name = p; pt_tys = tvi; pt_args = args; } }
;

%inline rwside:
| MINUS { `RtoL }
| empty { `LtoR }
;

%inline rwrgint:
| i=loc(int) {
    if i.pl_desc = 0 then
      parse_error i.pl_loc (Some "focus-index cannot be 0");
    i.pl_desc
  }
;

%inline rwrg:
| i=rwrgint              { ((Some i, Some i), `Include) }
| TILD i=rwrgint         { ((Some i, Some i), `Exclude) }
| rg=rgrw_cp             { (rg, `Include) }
| TILD rg=paren(rgrw_cp) { (rg, `Exclude) }
;

%inline rgrw_cp:
| i1=rwrgint DOTDOT i2=rwrgint { (Some i1, Some i2) }
| i1=rwrgint DOTDOT            { (Some i1, None   ) }
|        DOTDOT i2=rwrgint     { (None   , Some i2) }
;

rwrepeat:
| NOT             { (`All  , None  ) }
| QUESTION        { (`Maybe, None  ) }
| n=uint NOT      { (`All  , Some n) }
| n=uint QUESTION { (`Maybe, Some n) }
;

rwocc:
| LBRACE x=uint+ RBRACE { x }
;

rwarg1:
| SLASHSLASH
    { RWDone false }

| SLASHSLASHEQ
    { RWDone true }

| SLASHEQ
   { RWSimpl }

| s=rwside r=rwrepeat? o=rwocc? fp=fpattern_list(form)
   { RWRw (s, r, o |> omap EcMaps.Sint.of_list, fp) }

| s=rwside r=rwrepeat? o=rwocc? SLASH x=sform_h %prec prec_tactic
   { let loc = EcLocation.make $startpos $endpos in
       if r <> None then
         parse_error loc (Some "delta-repeat not supported");
       RWDelta (s, o |> omap EcMaps.Sint.of_list, x); }

| PR s=bracket(ident)
   { RWPr s }
;

rwarg:
| r=rwarg1 { (None, r) }
| rg=loc(rwrg) COLON r=rwarg1 { (Some rg, r) }
;

genpattern:
| o=rwocc? l=sform_h %prec prec_tactic { (o |> omap EcMaps.Sint.of_list, l) }
;

simplify_arg: 
| DELTA l=qoident* { `Delta l }
| ZETA             { `Zeta }
| IOTA             { `Iota }
| BETA             { `Beta }
| LOGIC            { `Logic }
| MODPATH          { `ModPath }
;

simplify:
| l=simplify_arg+     { l }
| SIMPLIFY            { simplify_red }
| SIMPLIFY l=qoident+ { `Delta l  :: simplify_red  }
| SIMPLIFY DELTA      { `Delta [] :: simplify_red }
;

conseq:
| empty                         { None, None }
| f1=form                       { Some f1, None }
| f1=form LONGARROW             { Some f1, None }
| f1=form LONGARROW UNDERSCORE  { Some f1, None }
| LONGARROW f2=form             { None, Some f2 }
| UNDERSCORE LONGARROW f2=form  { None, Some f2 }
| f1=form LONGARROW f2=form     { Some f1, Some f2 }
;

conseq_bd:
| c=conseq                                   { c, None }
| c=conseq   COLON cmp=hoare_bd_cmp? bd=sform { c, Some (cmp, bd) } 
| UNDERSCORE COLON cmp=hoare_bd_cmp? bd=sform { (None, None), Some(cmp, bd) }

call_info: 
 | f1=form LONGARROW f2=form             { CI_spec (f1, f2) }
 | f=form                                { CI_inv  f }
 | bad=form COMMA p=form                 { CI_upto (bad,p,None) }
 | bad=form COMMA p=form COMMA q=form    { CI_upto (bad,p,Some q) }

tac_dir: 
| BACKS { Backs }
| FWDS  { Fwds }
| empty { Backs }
;

codepos:
| i=uint { (i, None) }
| c=CPOS { c }
;

code_position:
| n=uint { Single n }
| n1=uint n2=uint { Double (n1, n2) } 
;

while_tac_info : 
| inv=sform
    { (inv, None, None) }
| inv=sform vrnt=sform 
    { (inv, Some vrnt, None) }
| inv=sform vrnt=sform k=sform eps=sform 
    { (inv, Some vrnt, Some (k,eps)) }

rnd_info:
| empty {PNoRndParams (* None,None *) }
| f=sform {PSingleRndParam f}
| f=sform g=sform {PTwoRndParams (f,g) }
| phi=sform d1=sform d2=sform d3=sform d4=sform p=sform? 
  {PMultRndParams ((phi,d1,d2,d3,d4),p) }


swap_info:
| s=side? p=swap_pos { s,p }
;

swap_pos:
| i1=uint i2=uint i3=uint
    { SKbase (i1, i2, i3) }

| p=int
    { SKmove p }

| i1=uint p=int
    { SKmovei (i1, p) }

| LBRACKET i1=uint DOTDOT i2=uint RBRACKET p=int
    { SKmoveinter (i1, i2, p) }
;

int:
| n=uint { n }
| loc(MINUS) n=uint { -n }
;

side:
| LBRACE n=uint RBRACE {
   match n with
   | 1 -> true
   | 2 -> false
   | _ -> parse_error
              (EcLocation.make $startpos $endpos)
              (Some "variable side must be 1 or 2")
 }
;

occurences:
| p=paren(uint+) {
    if List.mem 0 p then
      parse_error
        (EcLocation.make $startpos $endpos)
        (Some "`0' is not a valid occurence");
    p
  }
;

dbmap1:
| f=dbmap_flag? x=dbmap_target {
    { pht_flag = odfl `Include f;
      pht_kind = (fst x);
      pht_name = (snd x); }
  }
;

dbmap_flag:
| ADD   { `Include }
| MINUS { `Exclude }
;

dbmap_target:
| AT x=uqident { (`Theory, x) }
| x=qident { (`Lemma, x) }
;

dbhint:
| nl=boption(NOLOCALS) m=dbmap1* {
    { pht_nolocals = nl; pht_map = m; }
  }
;

%inline prod_form:
  | f1=sform f2=sform   { Some f1, Some f2 }
  | UNDERSCORE f2=sform { None   , Some f2 }
  | f1=sform UNDERSCORE { Some f1, None    }
;

app_bd_info:
  | empty    { PAppNone }
  | f=sform  { PAppSingle f }
  | f=prod_form g=prod_form s=sform?
             { PAppMult (s,fst f,snd f,fst g, snd g) }
;

logtactic:
| REFLEX
    { Preflexivity }

| ASSUMPTION
    { Passumption (None, None) }

| ASSUMPTION p=qident tvi=tvars_app?
   { Passumption (Some p, tvi) } 

| GENERALIZE l=genpattern+
   { Pgeneralize l } 

| CLEAR l=ident+
   { Pclear l }

| CONGR
   { Pcongr }

| TRIVIAL
   { Ptrivial }

| SMT db=dbhint pi=prover_info
   { Psmt (Some db, pi) }

| INTROS a=intro_pattern*
   { Pintro a }

| SPLIT
    { Psplit }

| FIELD eqs=ident*
    { Pfield eqs }

| RING eqs=ident*
    { Pring eqs }

| EXIST a=iplist1(loc(fpattern_arg), COMMA) %prec prec_below_comma
   { Pexists a }

| LEFT
    { Pleft }

| RIGHT
    { Pright }

| ELIM e=fpattern(form)
   { Pelim e }

| ELIMT f=sform
   { PelimT (f, None) }

| ELIMT p=qident f=sform
   { PelimT (f, Some p) }

| ELIM SLASH p=qident f=sform
   { PelimT (f, Some p) }

| APPLY e=fpattern(form)
   { Papply (e, None) }

| APPLY e=fpattern(form) IN x=ident
   { Papply (e, Some x) }

| l=simplify
   { Psimplify (mk_simplify l) }

| CHANGE f=sform
   { Pchange f }

| REWRITE a=rwarg+
   { Prewrite a }

| SUBST l=sform*
   { Psubst l }

| CUT ip=intro_pattern? COLON p=form %prec prec_below_IMPL
   { Pcut (ip, p, None) }

| CUT ip=intro_pattern? COLON p=form BY t=tactic_core
   { Pcut (ip, p, Some t) }

| CUT ip=intro_pattern? CEQ fp=pterm
   { Pcutdef (ip, fp) }

| POSE o=rwocc? x=lident CEQ p=form_h %prec prec_below_IMPL
   { Ppose (x, o |> omap EcMaps.Sint.of_list, p) }
;

(* NEW : ADDED FOR EAGER *)
eager_info:
| h=ident 
    { LE_done h }
| LPAREN h=ident COLON s1=stmt TILD s2=stmt COLON pr=form LONGARROW po=form RPAREN
    { LE_todo(h,s1,s2,pr,po) }
;

eager_tac:
| SEQ n1=uint n2=uint i=eager_info COLON p=sform
    { Peager_seq (i,(n1,n2),p) }
| IF 
    { Peager_if }
| WHILE i=eager_info 
    { Peager_while i }
| PROC 
    { Peager_fun_def }
| PROC i=eager_info f=sform 
    { Peager_fun_abs(i,f) }
| CALL info=fpattern(call_info) 
    { Peager_call info }
| info=eager_info COLON p=sform 
    { Peager(info,p) }
;
(* END EAGER *)

phltactic:
| PROC
    { Pfun_def }

| PROC f=sform
    { Pfun_abs f }

| PROC bad=sform p=sform q=sform? 
    { Pfun_upto(bad, p, q) }

| PROC STAR 
    { Pfun_to_code }

| SEQ d=tac_dir pos=code_position COLON p=sform f=app_bd_info
   { Papp (d, pos, p, f) }

| WP n=code_position?
   { Pwp n }

| SP s=side?
    { Psp s }

| SKIP
    { Pskip }

| WHILE s=side? info=while_tac_info
    { Pwhile (s,info) }

| CALL s=side? info=fpattern(call_info) 
    { Pcall (s, info) }

| RCONDT s=side? i=uint
    { Prcond (s, true, i) }

| RCONDF s=side? i=uint 
    { Prcond (s, false, i) }

| IF s=side?
    { Pcond s }

| SWAP info=iplist1(loc(swap_info), COMMA) %prec prec_below_comma
    { Pswap info }

| CFOLD s=side? c=codepos NOT n=uint
    { Pcfold (s, c, Some n) }

| CFOLD s=side? c=codepos
    { Pcfold (s, c, None) }

| RND s=side? info=rnd_info
    { Prnd (s, info) }

| INLINE s=side? o=occurences? f=plist1(loc(fident), empty)
    { Pinline (`ByName (s, (f, o))) }

| INLINE s=side? STAR
    { Pinline (`All s) }

| KILL s=side? o=codepos 
    { Pkill (s, o, Some 1) }

| KILL s=side? o=codepos NOT n=uint
    { Pkill (s, o, Some n) }

| KILL s=side? o=codepos NOT STAR
    { Pkill (s, o, None) }

| p=tselect INLINE
    { Pinline (`ByPattern p) }

| ALIAS s=side? o=codepos
    { Palias (s, o, None) }

| ALIAS s=side? o=codepos WITH x=lident
    { Palias (s, o, Some x) }

| ALIAS s=side? o=codepos x=lident EQ e=expr 
    { Pset (false,s, o,x,e) }

| FISSION s=side? o=codepos AT d1=uint COMMA d2=uint
    { Pfission (s, o, (1, (d1, d2))) }

| FISSION s=side? o=codepos NOT i=uint AT d1=uint COMMA d2=uint
    { Pfission (s, o, (i, (d1, d2))) }

| FUSION s=side? o=codepos AT d1=uint COMMA d2=uint
    { Pfusion (s, o, (1, (d1, d2))) }

| FUSION s=side? o=codepos NOT i=uint AT d1=uint COMMA d2=uint
    { Pfusion (s, o, (i, (d1, d2))) }

| UNROLL s=side? o=codepos
    { Punroll (s, o) }

| SPLITWHILE c=expr COLON s=side? o=codepos
    { Psplitwhile (c, s, o) }

| BYPHOARE info=fpattern(conseq)
    { Pbydeno (`PHoare, info) }

| BYEQUIV info=fpattern(conseq)
    { Pbydeno (`Equiv, info) }

| CONSEQ nm=STAR? info1=fpattern(conseq_bd)
    { Pconseq (nm<>None, (Some info1,None,None)) }
| CONSEQ nm=STAR? info1=fpattern(conseq_bd) info2=fpattern(conseq_bd)
                                                               UNDERSCORE?
    { Pconseq(nm<>None, (Some info1,Some info2, None)) }
| CONSEQ nm=STAR? info1=fpattern(conseq_bd) UNDERSCORE 
                                                 info3=fpattern(conseq_bd)
    { Pconseq(nm<>None, (Some info1,None,Some info3)) }
| CONSEQ nm=STAR? 
    info1=fpattern(conseq_bd) info2=fpattern(conseq_bd) 
                                                 info3=fpattern(conseq_bd)
    { Pconseq (nm<>None, (Some info1,Some info2,Some info3)) }

| CONSEQ nm=STAR? UNDERSCORE info2=fpattern(conseq_bd) UNDERSCORE?
    { Pconseq(nm<>None, (None,Some info2, None)) }
| CONSEQ nm=STAR? UNDERSCORE UNDERSCORE info3=fpattern(conseq_bd) 
    { Pconseq(nm<>None, (None,None,Some info3)) }
| ELIM STAR
    { Phr_exists_elim }

| EXIST STAR l=iplist1(sform, COMMA) %prec prec_below_comma
    { Phr_exists_intro l }

| EXFALSO
    { Pexfalso }

| BYPR { PPr ( None ) }
| BYPR f1=sform f2=sform { PPr( Some (f1,f2)) }

| FEL at_pos=uint cntr=sform delta=sform q=sform f_event=sform some_p=fel_pred_specs inv=sform?
   {Pfel (at_pos,(cntr,delta,q,f_event,some_p,inv))}

| SIM info=eqobs_in
    { Psim info }

| TRANSITIVITY tk=trans_kind h1=trans_hyp h2=trans_hyp
    { Ptrans_stmt (tk, fst h1, snd h1, fst h2, snd h2) }

| SYMMETRY 
    { Psymmetry }    

| EAGER t=eager_tac
    { t }

(* basic pr based tacs *)
| HOARE {Phoare}
| PRBOUNDED {Pprbounded}
| PHOARE SPLIT i=bdhoare_split { Pbdhoare_split i }
| PHOARE EQUIV s=side pr=sform po=sform { Pbd_equiv(s,pr,po) } 
;

bdhoare_split:
| b1=sform b2=sform b3=sform? { BDH_split_bop (b1,b2,b3) }
| b1=sform b2=sform COLON f=sform { BDH_split_or_case (b1,b2,f) }
| NOT b1=sform b2=sform      { BDH_split_not (Some b1,b2) }
;

trans_kind:
 | s=side  c=brace(stmt) { TKstmt(Some s, c) }
 | f=loc(fident) { TKfun (f) }
;

trans_hyp:
| LPAREN p=form LONGARROW q=form RPAREN { (p,q) }
;

fel_pred_spec:
| f=loc(fident) COLON p=sform
    { (f, p) } 

fel_pred_specs:
| LBRACKET assoc_ps = plist0(fel_pred_spec, SEMICOLON) RBRACKET
    {assoc_ps}

eqobs_in:
| empty                              { (None   , None   , None) }
| COLON f3=sform                     { (None   , None   , Some f3)   }
| f1=sform COLON f3=sform?           { (Some f1, None   , f3)   } 
| f1=sform f2=sform COLON f3=sform?  { (Some f1, Some f2, f3)   }
;

tactic_core_r:
| IDTAC
   { Pidtac None }

| IDTAC s=STRING
   { Pidtac (Some s) }

| TRY t=tactic_core
   { Ptry t }

| BY t=tactics
   { Pby (Some t) }

| BY bracket(empty) | DONE
   { Pby None }

| DO t=tactic_core
   { Pdo ((`All, None), t) }

| DO n=uint? NOT t=tactic_core
   { Pdo ((`All, n), t) }

| DO n=uint? QUESTION t=tactic_core
   { Pdo ((`Maybe, n), t) }

| LPAREN s=tactics RPAREN
   { Pseq s } 

| ADMIT
   { Padmit }

| CASE f=sform
   { Pcase f }

| PROGRESS t=tactic_core?
   { Pprogress t }

| x=logtactic
   { Plogic x }

| x=phltactic
   { PPhl x }

(* DEBUG *)
| DEBUG
    { Pdebug }
;

%inline tactic_core:
| x=loc(tactic_core_r) { x }
;

tactic_ip:
| t=tactic_core %prec prec_below_IMPL
    { mk_core_tactic t }

| t=tactic_core IMPL ip=intro_pattern+
    { { pt_core = t; pt_intros = ip; } }
;

tactic:
| t=tactic_ip %prec prec_below_IMPL
    { t }

| t1=tactic_ip ORA t2=tactic_ip
    { let loc = EcLocation.make $startpos $endpos in
        mk_core_tactic (mk_loc loc (Por (t1, t2))) }
;

tactic_chain:
| LBRACKET ts=plist1(loc(tactics0), PIPE) RBRACKET
    { Psubtacs (List.map mk_core_tactic ts) }

| FIRST t=loc(tactics) { Pfirst (mk_core_tactic (mk_loc t.pl_loc (Pseq (unloc t))), 1) }
| LAST  t=loc(tactics) { Plast  (mk_core_tactic (mk_loc t.pl_loc (Pseq (unloc t))), 1) }

| FIRST n=uint t=loc(tactics) { Pfirst (mk_core_tactic (mk_loc t.pl_loc (Pseq (unloc t))), n) }
| LAST  n=uint t=loc(tactics) { Plast  (mk_core_tactic (mk_loc t.pl_loc (Pseq (unloc t))), n) }

| FIRST LAST  { Protate (`Left , 1) }
| LAST  FIRST { Protate (`Right, 1) }

| FIRST n=uint LAST  { Protate (`Left , n) }
| LAST  n=uint FIRST { Protate (`Right, n) }
;

subtactic:
| t=loc(tactic_chain)
    { mk_core_tactic (mk_loc t.pl_loc (Psubgoal (unloc t))) }

| t=tactic
    { t }
;

subtactics:
| t=subtactic { [t] }
| ts=subtactics SEMICOLON t=subtactic { t :: ts }
;

tactics:
| t=tactic %prec SEMICOLON { [t] }
| t=tactic SEMICOLON ts=subtactics { t :: (List.rev ts) }
;

tactics0:
| ts=tactics   { Pseq ts } 
| x=loc(empty) { Pseq [mk_core_tactic (mk_loc x.pl_loc (Pidtac None))] }

tactics_or_prf:
| t=tactics    { `Actual t    }
| p=proof      { `Proof  p    }
;

proof:
| PROOF modes=proofmode1* {
    let seen = Hashtbl.create 0 in
      List.fold_left
        (fun pmodes (mode, flag) ->
           if Hashtbl.mem seen mode then
             parse_error mode.pl_loc (Some "duplicated flag");
           Hashtbl.add seen mode ();
           match unloc mode with
           | `Strict -> { pmodes with pm_strict = flag; })
        { pm_strict = true; } modes
  }
;

proofmode1:
| b=boption(MINUS) pm=loc(proofmodename) { (pm, not b) }
;

proofmodename:
| STRICT { `Strict }
;

(* -------------------------------------------------------------------- *)
(* Theory cloning                                                       *)

theory_clone:
| CLONE ip=import_flag? x=uqident cw=clone_with? cp=clone_proof?
   { let oth =
       { pthc_base = x;
         pthc_name = None;
         pthc_ext  = EcUtils.odfl [] cw;
         pthc_prf  = EcUtils.odfl [] cp; }
     in
       (oth, ip) }

| CLONE ip=import_flag? x=uqident AS y=uident cw=clone_with? cp=clone_proof?
   { let oth =
       { pthc_base = x;
         pthc_name = Some y;
         pthc_ext  = EcUtils.odfl [] cw;
         pthc_prf  = EcUtils.odfl [] cp; }
     in
       (oth, ip) }
;

clone_with:
| WITH x=plist1(clone_override, COMMA) { x }
;

clone_lemma_base:
| STAR     { `All }
| x=_ident { `Named x }
; 

clone_lemma_1_core:
| l=genqident(clone_lemma_base) {
    match unloc l with
    | (xs, `Named x) -> `Named (mk_loc l.pl_loc (xs, x))
    | (xs, `All    ) -> begin
      match List.rev xs with
      | []      -> `All None
      | x :: xs -> `All (Some (mk_loc l.pl_loc (List.rev xs, x)))
    end
  }
;

clone_lemma_1:
| cl=clone_lemma_1_core
    { { pthp_mode = cl; pthp_tactic = None; } }

| cl=clone_lemma_1_core BY t=tactic_core
    { { pthp_mode = cl; pthp_tactic = Some t; } }
;

clone_lemma:
| x=clone_lemma_1
    { [x] }

| xs=clone_lemma COMMA x=clone_lemma_1
    { x :: xs }
;

clone_proof:
| PROOF x=clone_lemma { List.rev x }
;

opclmode:
| EQ { `Alias }
| LEFTARROW { `Inline }
;

cltyparams:
| empty { [] }
| x=tident { [x] }
| xs=paren(plist1(tident, COMMA)) { xs }
;

clone_override:
| TYPE ps=cltyparams x=qident EQ t=loc(type_exp)
   { (x, PTHO_Type (ps, t, `Alias)) }

| TYPE ps=cltyparams x=qident LEFTARROW t=loc(type_exp)
   { (x, PTHO_Type (ps, t, `Inline)) }

| OP x=qoident tyvars=bracket(tident*)? COLON sty=loc(type_exp) mode=opclmode e=expr
   { let ov = {
       opov_tyvars = tyvars;
       opov_args   = [];
       opov_retty  = sty;
       opov_body   = e;
     } in
       (x, PTHO_Op (ov, mode)) }

| OP x=qoident tyvars=bracket(tident*)? mode=loc(opclmode) e=expr
   { let ov = {
       opov_tyvars = tyvars;
       opov_args   = [];
       opov_retty  = mk_loc mode.pl_loc PTunivar;
       opov_body   = e;
     } in
       (x, PTHO_Op (ov, unloc mode)) }

| OP x=qoident tyvars=bracket(tident*)? p=ptybindings mode=loc(opclmode) e=expr
   { let ov = {
       opov_tyvars = tyvars;
       opov_args   = p;
       opov_retty  = mk_loc mode.pl_loc PTunivar;
       opov_body   = e;
     } in
       (x, PTHO_Op (ov, unloc mode)) }

| PRED x=qoident tyvars=bracket(tident*)? p=ptybindings EQ f=form
   { let ov = {
       prov_tyvars = tyvars;
       prov_args   = p;
       prov_body   = f;
     } in
       (x, PTHO_Pred ov) }

| PRED x=qoident tyvars=bracket(tident*)? EQ f=form
   { let ov = {
       prov_tyvars = tyvars;
       prov_args   = [];
       prov_body   = f;
     } in
       (x, PTHO_Pred ov) }

| THEORY x=uqident EQ y=uqident
   { (x, PTHO_Theory y) }
;

realize:
| REALIZE x=qident { x }
;

(* -------------------------------------------------------------------- *)
(* Printing                                                             *)
print:
| TYPE   qs=qident      { Pr_ty qs }
| OP     qs=qoident     { Pr_op qs }
| THEORY qs=qident      { Pr_th qs }
| PRED   qs=qoident     { Pr_pr qs } 
| AXIOM  qs=qident      { Pr_ax qs }
| MODULE qs=qident      { Pr_mod qs }
| MODULE TYPE qs=qident { Pr_mty qs }
;

prover_iconfig:
| /* empty */     { (None   , None   ) }
| i=uint          { (Some i , None   ) }
| i1=uint i2=uint { (Some i1, Some i2) }
;

prover_info:
| ic=prover_iconfig pl=plist1(loc(STRING), empty)? 
    { let (m, t) = ic in
        { pprov_max   = m;
          pprov_time  = t;
          pprov_names = pl; } }
;

gprover_info: 
| PROVER x=prover_info
    { x }

| TIMEOUT t=uint        
    { { pprov_max = None; pprov_time = Some t; pprov_names = None } }
;

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

global_:
| theory_open      { GthOpen      $1 }
| theory_close     { GthClose     $1 }
| theory_require   { GthRequire   $1 }
| theory_import    { GthImport    $1 }
| theory_export    { GthExport    $1 }
| theory_clone     { GthClone     $1 }
| theory_w3        { GthW3        $1 }
| section_open     { GsctOpen        }
| section_close    { GsctClose       }
| top_mod_def      { Gmodule      $1 }
| top_mod_decl     { Gdeclare     $1 }
| sig_def          { Ginterface   $1 }
| typedecl         { Gtype        $1 }
| typeclass        { Gtypeclass   $1 }
| tycinstance      { Gtycinstance $1 }
| operator         { Goperator    $1 }
| predicate        { Gpredicate   $1 }
| axiom            { Gaxiom       $1 }
| claim            { Gclaim       $1 }
| tactics_or_prf   { Gtactics     $1 }
| realize          { Grealize     $1 }
| gprover_info     { Gprover_info $1 }

| x=loc(QED)       { Gsave x.pl_loc }
| PRINT p=print    { Gprint     p   }
| PRAGMA x=lident  { Gpragma    x   }

| EXTRACTION i=extract_info { Gextract i }
;

extract_info:
|  s=STRING? qs=plist1(toextract,COMMA) w=withextract { (s,qs,w) }
;

toextract:
| OP q=qoident     {ExOp q}
| TYPE q=qoident   {ExTy q}
| THEORY q=qoident {ExTh q}
;

withextract:
| empty { [] }
| WITH w=plist1(withextract1,COMMA) { w }
;
withextract1:
| p=toextract EQ s=STRING { p,s }
;


stop:
| EOF { }
| DROP DOT { }
;

global:
| g=loc(global_) FINAL { g }
;

prog_r:
| g=global { P_Prog ([g], false) }
| stop     { P_Prog ([ ], true ) }

| UNDO d=uint FINAL
   { P_Undo d }

| error
   { parse_error (EcLocation.make $startpos $endpos) None }
;

prog:
| x=loc(prog_r) { x }
;

(* -------------------------------------------------------------------- *)
%inline plist0(X, S):
| aout=separated_list(S, X) { aout }
;

iplist1_r(X, S):
| x=X { [x] }
| xs=iplist1_r(X, S) S x=X { x :: xs }
;

%inline iplist1(X, S):
| xs=iplist1_r(X, S) { List.rev xs }
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
__rlist1(X, S):                         (* left-recursive *)
| x=X { [x] }
| xs=__rlist1(X, S) S x=X { x :: xs }
;

%inline rlist0(X, S):
| /* empty */     { [] }
| xs=rlist1(X, S) { xs }
;

%inline rlist1(X, S):
| xs=__rlist1(X, S) { List.rev xs }
;

%inline rlist2(X, S):
| xs=__rlist1(X, S) S x=X { List.rev (x :: xs) }
;

(* -------------------------------------------------------------------- *)
%inline paren(X):
| LPAREN x=X RPAREN { x }
;

%inline brace(X):
| LBRACE x=X RBRACE { x }
;

%inline bracket(X):
| LBRACKET x=X RBRACKET { x }
;

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X {
    { pl_desc = x;
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }
;
