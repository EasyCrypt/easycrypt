%%

%public %inline sform_r(P): x=loc(sform_u(P)) { x }
%public %inline  form_r(P): x=loc( form_u(P)) { x }

%public %inline sform: x=sform_r(none) { x }
%public %inline  form: x=form_r (none) { x }

%public %inline sform_h: x=loc(sform_u(hole)) { x }
%public %inline  form_h: x=loc( form_u(hole)) { x }

%public %inline none: IMPOSSIBLE { assert false }
%public %inline hole: UNDERSCORE { PFhole }

sform_u(P):
| x=P
   { x }

| f=sform_r(P) PCENT p=uqident
   { PFscope (p, f) }

| f=sform_r(P) p=loc(prefix(PCENT, _lident))

   { if unloc p = "top" then
       PFscope (pqsymb_of_symb p.pl_loc "<top>", f)
     else
       let p = lmap (fun x -> "%" ^ x) p in
       PFapp (mk_loc (loc p) (PFident (pqsymb_of_psymb p, None)), [f]) }

| SHARP pf=pffilter* x=ident
   { PFref (x, pf) }

| LPAREN f=form_r(P) COLONTILD ty=loc(type_exp) RPAREN
   { PFcast (f, ty) }

| n=uint
   { PFint n }

| d=DECIMAL
   { PFdecimal d }

| x=loc(RES)
   { PFident (mk_loc x.pl_loc ([], "res"), None) }

| x=qoident ti=tvars_app?
   { PFident (x, ti) }

| x=mident
   { PFmem x }

| se=sform_r(P) DLBRACKET ti=tvars_app? e=loc(plist1(form_r(P), COMMA)) RBRACKET
   { let e = List.reduce1 (fun _ -> lmap (fun x -> PFtuple x) e) (unloc e) in
     pfget (EcLocation.make $startpos $endpos) ti se e }

| se=sform_r(P) DLBRACKET
    ti=tvars_app? e1=loc(plist1(form_r(P), COMMA))LARROW e2=form_r(P)
  RBRACKET
   { let e1 = List.reduce1 (fun _ -> lmap (fun x -> PFtuple x) e1) (unloc e1) in
     pfset (EcLocation.make $startpos $endpos) ti se e1 e2 }

| x=sform_r(P) s=loc(pside)
   { PFside (x, s) }

| op=loc(numop) ti=tvars_app?
    { pfapp_symb op.pl_loc op.pl_desc ti [] }

| TICKPIPE ti=tvars_app? e =form_r(P) PIPE
   { pfapp_symb e.pl_loc EcCoreLib.s_abs ti [e] }

| LPAREN fs=plist0(form_r(P), COMMA) RPAREN
   { PFtuple fs }

| LPBRACE fields=rlist1(form_field, SEMICOLON) SEMICOLON? RPBRACE
   { PFrecord (None, fields) }

| LPBRACE b=sform WITH fields=rlist1(form_field, SEMICOLON) SEMICOLON? RPBRACE
   { PFrecord (Some b, fields) }

| LBRACKET ti=tvars_app? es=loc(plist0(form_r(P), SEMICOLON)) RBRACKET
   { (pflist es.pl_loc ti es.pl_desc).pl_desc }

| f=sform_r(P) DOTTICK x=qident
    { PFproj (f, x) }

| f=sform_r(P) DOTTICK n=loc(word)
   { if n.pl_desc = 0 then
       parse_error n.pl_loc (Some "tuple projection start at 1");
     PFproji(f,n.pl_desc - 1) }

| HOARE LBRACKET hb=hoare_body(P) RBRACKET { hb }

| EHOARE LBRACKET hb=ehoare_body(P) RBRACKET { hb }

| EQUIV LBRACKET eb=equiv_body(P) RBRACKET { eb }

| EAGER LBRACKET eb=eager_body(P) RBRACKET { eb }

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

form_u(P):
| GLOB mp=loc(mod_qident) { PFglob mp }

| e=sform_u(P) { e }

| e=sform_r(P) args=sform_r(P)+ { PFapp (e, args) }

| op=loc(uniop) ti=tvars_app? e=form_r(P)
   { pfapp_symb op.pl_loc op.pl_desc ti [e] }

| f=form_chained_orderings(P) %prec prec_below_order
    { fst f }

| e1=form_r(P) op=loc(binop) ti=tvars_app? e2=form_r(P)
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| c=form_r(P) QUESTION e1=form_r(P) COLON e2=form_r(P) %prec LOP2
    { PFif (c, e1, e2) }

| MATCH f=form_r(P) WITH
    PIPE? bs=plist0(p=mcptn(sbinop) IMPL bf=form_r(P) { (p, bf) }, PIPE)
  END
    { PFmatch (f, bs) }

| EQ LBRACE xs=plist1(qident_or_res_or_glob, COMMA) RBRACE
    { PFeqveq (xs, None) }

| EQ LBRACE xs=plist1(qident_or_res_or_glob, COMMA) RBRACE
    LPAREN  m1=mod_qident COMMA m2=mod_qident RPAREN
    { PFeqveq (xs, Some (m1, m2)) }

| EQ LPBRACE xs=plist1(form_r(P), COMMA) RPBRACE
    { PFeqf xs }

| IF c=form_r(P) THEN e1=form_r(P) ELSE e2=form_r(P)
    { PFif (c, e1, e2) }

| LET p=lpattern EQ e1=form_r(P) IN e2=form_r(P)
    { PFlet (p, (e1, None), e2) }

| LET p=lpattern COLON ty=loc(type_exp) EQ e1=form_r(P) IN e2=form_r(P)
    { PFlet (p, (e1, Some ty), e2) }

| FORALL pd=pgtybindings COMMA e=form_r(P) { PFforall (pd, e) }
| EXIST  pd=pgtybindings COMMA e=form_r(P) { PFexists (pd, e) }
| FUN    pd=ptybindings  COMMA e=form_r(P) { PFlambda (pd, e) }
| FUN    pd=ptybindings  IMPL  e=form_r(P) { PFlambda (pd, e) }

| r=loc(RBOOL) TILD e=sform_r(P)
    { let id  = PFident (mk_loc r.pl_loc EcCoreLib.s_dbitstring, None) in
      let loc = EcLocation.make $startpos $endpos in
        PFapp (mk_loc loc id, [e]) }

| PHOARE pb=phoare_body(P) { pb }

| LOSSLESS mp=loc(fident)
    { PFlsless mp }

form_field:
| x=qident EQ f=form
    { { rf_name = x; rf_tvi = None; rf_value = f; } }

form_ordering(P):
| f1=form_r(P) op=loc(ordering_op) ti=tvars_app? f2=form_r(P)
    { (op, ti, f1, f2) }

form_chained_orderings(P):
| f=form_ordering(P)
    { let (op, ti, f1, f2) = f in
        (pfapp_symb op.pl_loc (unloc op) ti [f1; f2], f2) }

| f1=loc(form_chained_orderings(P)) op=loc(ordering_op) ti=tvars_app? f2=form_r(P)
    { let (lcf1, (f1, le)) = (f1.pl_loc, unloc f1) in
      let loc = EcLocation.make $startpos $endpos in
        (pfapp_symb loc "&&" None
           [EcLocation.mk_loc lcf1 f1;
            EcLocation.mk_loc loc
              (pfapp_symb op.pl_loc (unloc op) ti [le; f2])],
         f2) }

%public hoare_bd_cmp :
| LE { EcAst.FHle }
| EQ { EcAst.FHeq }
| GE { EcAst.FHge }

%public hoare_body(P):
  mp=loc(fident) COLON pre=form_r(P) LONGARROW post=form_r(P)
    { PFhoareF (pre, mp, post) }

%public ehoare_body(P):
  mp=loc(fident) COLON pre=form_r(P) LONGARROW
                       post=form_r(P)
    { PFehoareF (pre, mp, post) }

%public phoare_body(P):
  LBRACKET mp=loc(fident) COLON
    pre=form_r(P) LONGARROW post=form_r(P)
  RBRACKET
    cmp=hoare_bd_cmp bd=sform_r(P)
  { PFBDhoareF (pre, mp, post, cmp, bd) }

%public equiv_body(P):
  mp1=loc(fident) TILD mp2=loc(fident)
  COLON pre=form_r(P) LONGARROW post=form_r(P)
    { PFequivF (pre, (mp1, mp2), post) }

%public eager_body(P):
| s1=stmt COMMA  mp1=loc(fident) TILD mp2=loc(fident) COMMA s2=stmt
    COLON pre=form_r(P) LONGARROW post=form_r(P)
    { PFeagerF (pre, (s1, mp1, mp2,s2), post) }
