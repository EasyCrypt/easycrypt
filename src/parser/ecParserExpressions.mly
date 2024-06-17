%%

(* -------------------------------------------------------------------- *)
%public %inline sexpr: x=loc(sexpr_u) { x }
%public %inline  expr: x=loc( expr_u) { x }

sexpr_u:
| e=sexpr PCENT p=uqident
   { PEscope (p, e) }

| e=sexpr p=loc(prefix(PCENT, _lident))
   { if unloc p = "top" then
       PEscope (pqsymb_of_symb p.pl_loc "<top>", e)
     else
       let p = lmap (fun x -> "%" ^ x) p in
       PEapp (mk_loc (loc p) (PEident (pqsymb_of_psymb p, None)), [e]) }

| LPAREN e=expr COLONTILD ty=loc(type_exp) RPAREN
   { PEcast (e, ty) }

| n=uint
   { PEint n }

| d=DECIMAL
   { PEdecimal d }

| x=qoident ti=tvars_app?
   { PEident (x, ti) }

| op=loc(numop) ti=tvars_app?
    { peapp_symb op.pl_loc op.pl_desc ti [] }

| se=sexpr DLBRACKET ti=tvars_app? e=loc(plist1(expr, COMMA)) RBRACKET
   { let e = List.reduce1 (fun _ -> lmap (fun x -> PEtuple x) e) (unloc e) in
     peget (EcLocation.make $startpos $endpos) ti se e }

| se=sexpr DLBRACKET ti=tvars_app? e1=loc(plist1(expr, COMMA)) LARROW e2=expr RBRACKET
   { let e1 = List.reduce1 (fun _ -> lmap (fun x -> PEtuple x) e1) (unloc e1) in
     peset (EcLocation.make $startpos $endpos) ti se e1 e2 }

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
   { PErecord (None, fields) }

| LPBRACE b=sexpr WITH fields=rlist1(expr_field, SEMICOLON) SEMICOLON? RPBRACE
   { PErecord (Some b, fields) }

| e=sexpr DOTTICK x=qident
   { PEproj (e, x) }

| e=sexpr DOTTICK n=loc(word)
   { if n.pl_desc = 0 then
       parse_error n.pl_loc (Some "tuple projection start at 1");
     PEproji(e,n.pl_desc - 1) }

expr_u:
| e=sexpr_u { e }

| e=sexpr args=sexpr+
    { PEapp (e, args) }

| op=loc(uniop) ti=tvars_app? e=expr
    { peapp_symb op.pl_loc op.pl_desc ti [e] }

| e=expr_chained_orderings %prec prec_below_order
    { fst e }

| e1=expr op=loc(binop) ti=tvars_app? e2=expr
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| c=expr QUESTION e1=expr COLON e2=expr %prec LOP2
   { PEif (c, e1, e2) }

| IF c=expr THEN e1=expr ELSE e2=expr
   { PEif (c, e1, e2) }

| MATCH e=expr WITH
    PIPE? bs=plist0(p=mcptn(sbinop) IMPL be=expr { (p, be) }, PIPE)
  END
    { PEmatch (e, bs) }

| LET p=lpattern EQ e1=expr IN e2=expr
   { PElet (p, (e1, None), e2) }

| LET p=lpattern COLON ty=loc(type_exp) EQ e1=expr IN e2=expr
   { PElet (p, (e1, Some ty), e2) }

| r=loc(RBOOL) TILD e=sexpr
    { let id  = PEident(mk_loc r.pl_loc EcCoreLib.s_dbitstring, None) in
      let loc = EcLocation.make $startpos $endpos in
        PEapp (mk_loc loc id, [e]) }

| FUN pd=ptybindings IMPL  e=expr
| FUN pd=ptybindings COMMA e=expr { PElambda (pd, e) }

| FORALL pd=ptybindings COMMA e=expr { PEforall (pd, e) }
| EXIST  pd=ptybindings COMMA e=expr { PEexists (pd, e) }

expr_field:
| x=qident EQ e=expr
    { { rf_name = x ; rf_tvi = None; rf_value = e; } }

expr_ordering:
| e1=expr op=loc(ordering_op) ti=tvars_app? e2=expr
    { (op, ti, e1, e2) }

expr_chained_orderings:
| e=expr_ordering
    { let (op, ti, e1, e2) = e in
        (peapp_symb op.pl_loc (unloc op) ti [e1; e2], e2) }

| e1=loc(expr_chained_orderings) op=loc(ordering_op) ti=tvars_app? e2=expr
    { let (lce1, (e1, le)) = (e1.pl_loc, unloc e1) in
      let loc = EcLocation.make $startpos $endpos in
        (peapp_symb loc "&&" None
           [EcLocation.mk_loc lce1 e1;
            EcLocation.mk_loc loc
              (peapp_symb op.pl_loc (unloc op) ti [le; e2])],
         e2) }
