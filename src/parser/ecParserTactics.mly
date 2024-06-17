%%

ipcore_name:
| s=_lident { s }
| s=_uident { s }
| s=_mident { s }

ipcore:
| PLUS
   { `Revert }

| UNDERSCORE
   { `Clear }

| QUESTION
   { `Anonymous None }

| n=word QUESTION
   { `Anonymous (Some (Some n)) }

| STAR
   { `Anonymous (Some None) }

| s=ipcore_name
   { `Named s }

%inline sharp:
| SHARP { false }
| SHARPPIPE {true}

%inline icasemode:
| /* empty */
   { `One    }

| opt=icasemode_full_opt wb=sharp
   { `Full (opt, wb, None) }

| i=word NOT opt=icasemode_full_opt wb=sharp
    { `Full (opt, wb, Some (`AtMost i)) }

| NOT opt=icasemode_full_opt wb=sharp
    { `Full (opt, wb, Some (`AsMuch)) }

%inline icasemode_full_opt:
| h=iboption(TILD) d=iboption(SLASH) { (h, d) }

ip_repeat:
| i=ioption(word) NOT { i }
| i=word { Some i }

ipsubsttop:
| LTSTARGT   { None }
| LTLTSTARGT { Some `RtoL }
| LTSTARGTGT { Some `LtoR }

crushmode:
| PIPEGT { { cm_simplify = false; cm_solve = false; } }

| SLASHGT { { cm_simplify = true ; cm_solve = false; } }

| PIPEPIPEGT { { cm_simplify = false; cm_solve = true ; } }

| SLASHSLASHGT { { cm_simplify = true ; cm_solve = true ; } }

intro_pattern:
| x=ipcore
   { IPCore x }

| HAT
   { IPDup }

| LBRACKET mode=icasemode RBRACKET
   { IPCase (mode, []) }

| LBRACKET mode=icasemode ip=loc(intro_pattern)+ RBRACKET
   { IPCase (mode, [ip]) }

| LBRACKET mode=icasemode ip=plist2(loc(intro_pattern)*, PIPE) RBRACKET
   { IPCase (mode, ip) }

| i=ioption(ip_repeat) o=rwocc? RARROW
   { IPRw (o, `LtoR, i) }

| i=ioption(ip_repeat) o=rwocc? LARROW
   { IPRw (o, `RtoL, i) }

| i=ioption(ip_repeat) RRARROW
   { IPSubst (`LtoR, i) }

| i=ioption(ip_repeat) LLARROW
   { IPSubst (`RtoL, i) }

| LBRACE xs=loc(ipcore_name)+ RBRACE
   { IPClear xs }

| SLASHSLASH
   { IPDone None }

| SLASHSLASHEQ
   { IPDone (Some `Default) }

| SLASHSLASHTILDEQ
   { IPDone (Some `Variant) }

| SLASHSHARP
   { IPSmt (false, { (SMT.mk_smt_option []) with plem_max = Some (Some 0) }) }

| SLASHSLASHSHARP
   { IPSmt (true, { (SMT.mk_smt_option []) with plem_max = Some (Some 0) }) }

| SLASHEQ
   { IPSimplify `Default }

| SLASHTILDEQ
   { IPSimplify `Variant }

| SLASH f=pterm
   { IPView f }

| AT s=rwside o=rwocc? SLASH x=sform_h
   { IPDelta ((s, o), x) }

| ip=ipsubsttop
   { IPSubstTop (None, ip) }

| n=word NOT ip=ipsubsttop
   { IPSubstTop (Some n, ip) }

| MINUS
   { IPBreak }

| cm=crushmode
   { IPCrush cm }

gpterm_head(F):
| exp=iboption(AT) p=qident tvi=tvars_app?
   { (exp, FPNamed (p, tvi)) }

| LPAREN exp=iboption(AT) UNDERSCORE? COLON f=F RPAREN
   { (exp, FPCut f) }

gpoterm_head(F):
| x=gpterm_head(F?)
    { x }

| UNDERSCORE
    { (false, FPCut None) }

gpterm_arg:
| LPAREN LTCOLON m=loc(mod_qident) RPAREN
    { EA_mod m }

| f=sform_h
    { match unloc f with
      | PFhole -> EA_none
      | _      -> EA_form f }

| LPAREN COLON
    exp=iboption(AT) p=qident tvi=tvars_app? args=loc(gpterm_arg)*
  RPAREN
    { EA_proof (mk_pterm exp (FPNamed (p, tvi)) args) }

gpterm(F):
| hd=gpterm_head(F)
   { mk_pterm (fst hd) (snd hd) [] }

| LPAREN hd=gpterm_head(F) args=loc(gpterm_arg)* RPAREN
   { mk_pterm (fst hd) (snd hd) args }

gpoterm(F):
| hd=gpoterm_head(F)
   { mk_pterm (fst hd) (snd hd) [] }

| LPAREN hd=gpoterm_head(F) args=loc(gpterm_arg)* RPAREN
   { mk_pterm (fst hd) (snd hd) args }

%inline pterm:
| pt=gpoterm(form_h) { pt }


inlinesubpat:
| m=rlist1(uident, DOT) { m, None }
| m=rlist1(uident, DOT) DOT f=lident { m, Some f}
| f=lident { [], Some f}

inlinepat1:
| nm=loc(mod_qident)  {  `InlinePat(nm, ([], None)) }
| f=loc(fident) {
   let f0 = unloc f in
   if fst f0 = [] then `InlinePat(mk_loc (loc f) [], ([], Some (snd f0)))
   else `InlineXpath f
}
| nm=loc(mod_qident) SLASH sub=inlinesubpat { `InlinePat(nm, sub) }
| u=loc(UNDERSCORE) SLASH sub=inlinesubpat { `InlinePat(mk_loc (loc u) [], sub) }
| STAR { `InlineAll }

inlinepat:
| sign=iboption(MINUS) p=inlinepat1 { (if sign then `DIFF else `UNION), p }


(* ------------------------------------------------------------------ *)
pcutdef1:
| p=qident tvi=tvars_app? args=loc(gpterm_arg)*
    { { ptcd_name = p; ptcd_tys = tvi; ptcd_args = args; } }

pcutdef:
| cd=pcutdef1               { cd }
| LPAREN cd=pcutdef1 RPAREN { cd }

(* ------------------------------------------------------------------ *)
%inline rwside:
| MINUS { `RtoL }
| empty { `LtoR }

rwrepeat:
| NOT             { (`All  , None  ) }
| QUESTION        { (`Maybe, None  ) }
| n=word NOT      { (`All  , Some n) }
| n=word QUESTION { (`Maybe, Some n) }

rwocc:
| LBRACE       x=word+ RBRACE { (`Inclusive (EcMaps.Sint.of_list x)) }
| LBRACE MINUS x=word+ RBRACE { (`Exclusive (EcMaps.Sint.of_list x)) }
| LBRACE PLUS          RBRACE { (`All) }

rwpr_arg:
| i=ident        { (i, None) }
| i=ident f=form { (i, Some f) }

rwarg1:
| SLASHSLASH
   { RWDone None }

| SLASHSLASHEQ
   { RWDone (Some `Default) }

| SLASHSLASHTILDEQ
   { RWDone (Some `Variant) }

| SLASHSHARP
   { RWSmt (false, { (SMT.mk_smt_option []) with plem_max = Some (Some 0) }) }

| SLASHSLASHSHARP
   { RWSmt (true, { (SMT.mk_smt_option []) with plem_max = Some (Some 0) }) }

| SLASHEQ
   { RWSimpl `Default }

| SLASHTILDEQ
   { RWSimpl `Variant }

| s=rwside r=rwrepeat? o=rwocc? p=bracket(form_h)? fp=rwpterms
   { RWRw ((s, r, o, p), fp) }

| s=rwside r=rwrepeat? o=rwocc? SLASH x=sform_h %prec prec_tactic
   { RWDelta ((s, r, o, None), x); }

| PR s=bracket(rwpr_arg)
   { RWPr s }

| AMP f=pterm
   { RWApp f }

| SHARP SMT
   { RWSmt (false, SMT.mk_smt_option []) }

| SHARP SMT COLON pi=bracket(smt_info)
   { RWSmt (false, pi) }

| SHARP SMT COLON dbmap=paren(dbmap1*)
   { RWSmt (false, SMT.mk_smt_option [`WANTEDLEMMAS dbmap]) }

| SHARP x=ident {
    let tactics = [("ring", `Ring); ("field", `Field)] in
    match List.Exceptionless.assoc (unloc x) tactics with
    | Some x -> RWTactic x
    | None ->
        let msg = "invalid rw-tactic: " ^ (unloc x) in
        parse_error (loc x) (Some msg)
  }

rwpterms:
| f=pterm
    { [(`LtoR, f)] }

| LPAREN fs=rlist2(rwpterm, COMMA) RPAREN
    { fs }

rwpterm:
| s=rwside f=pterm
    { (s, f) }

rwarg:
| r=loc(rwarg1)
    { (None, r) }

| rg=loc(tcfc) COLON r=loc(rwarg1)
    { (Some rg, r) }

genpattern:
| l=sform_h %prec prec_tactic
    { `Form (None, l) }

| o=rwocc l=sform_h %prec prec_tactic
    { `Form (Some o, l) }

| LPAREN exp=iboption(AT) UNDERSCORE COLON f=form RPAREN
    { `ProofTerm (mk_pterm exp (FPCut (Some f)) []) }

| LPAREN LPAREN
    exp=iboption(AT) UNDERSCORE COLON f=form RPAREN
    args=loc(gpterm_arg)*
  RPAREN
    { `ProofTerm (mk_pterm exp (FPCut (Some f)) args) }

| AT x=ident
    { `LetIn x }

simplify_arg:
| DELTA l=qoident* { `Delta l }
| ZETA             { `Zeta }
| IOTA             { `Iota }
| BETA             { `Beta }
| ETA              { `Eta }
| LOGIC            { `Logic }
| MODPATH          { `ModPath }

simplify:
| l=simplify_arg+     { l }
| SIMPLIFY            { simplify_red }
| SIMPLIFY l=qoident+ { `Delta l  :: simplify_red  }
| SIMPLIFY DELTA      { `Delta [] :: simplify_red }

cbv:
| CBV            { simplify_red }
| CBV l=qoident+ { `Delta l  :: simplify_red  }
| CBV DELTA      { `Delta [] :: simplify_red }

conseq:
| empty                            { None, None }
| UNDERSCORE LONGARROW UNDERSCORE  { None, None }
| f1=form LONGARROW               { Some f1, None }
| f1=form LONGARROW UNDERSCORE    { Some f1, None }
| f2=form                         { None, Some f2 }
| LONGARROW f2=form               { None, Some f2 }
| UNDERSCORE LONGARROW f2=form    { None, Some f2 }
| f1=form LONGARROW f2=form       { Some f1, Some f2 }

conseq_xt:
| c=conseq                                     { c, None }
| c=conseq   COLON cmp=hoare_bd_cmp? bd=sform  { c, Some (CQI_bd (cmp, bd)) }
| UNDERSCORE COLON cmp=hoare_bd_cmp? bd=sform  { (None, None), Some (CQI_bd (cmp, bd)) }


call_info:
| f1=form LONGARROW f2=form          { CI_spec (f1, f2) }
| f=form                             { CI_inv  f }
| bad=form COMMA p=form              { CI_upto (bad,p,None) }
| bad=form COMMA p=form COMMA q=form { CI_upto (bad,p,Some q) }

tac_dir:
| BACKS { Backs }
| FWDS  { Fwds }
| empty { Backs }

icodepos_r:
| IF       { (`If     :> cp_match) }
| WHILE    { (`While  :> cp_match) }
| LARROW   { (`Assign :> cp_match) }
| LESAMPLE { (`Sample :> cp_match) }
| LEAT     { (`Call   :> cp_match) }

%inline icodepos:
 | HAT x=icodepos_r { x }

codepos1_wo_off:
| i=sword
    { (`ByPos i :> cp_base) }

| k=icodepos i=option(brace(sword))
    { (`ByMatch (i, k) :> cp_base) }

codepos1:
| cp=codepos1_wo_off { (0, cp) }

| cp=codepos1_wo_off AMP PLUS  i=word { ( i, cp) }
| cp=codepos1_wo_off AMP MINUS i=word { (-i, cp) }

%inline nm1_codepos:
| i=codepos1 k=ID(DOT { 0 } | QUESTION { 1 } )
    { (i, k) }

codepos:
| nm=rlist0(nm1_codepos, empty) i=codepos1
    { (List.rev nm, i) }

o_codepos1:
| UNDERSCORE { None }
| i=codepos1 { Some i}

s_codepos1:
| n=codepos1
    { Single n }

| n1=codepos1 n2=codepos1
    { Double (n1, n2) }

semrndpos1:
| b=boption(STAR) c=codepos1
    { (b, c) }

semrndpos:
| n=semrndpos1
    { Single n }

| n1=semrndpos1 n2=semrndpos1
    { Double (n1, n2) }

while_tac_info:
| inv=sform
    { { wh_inv = inv; wh_vrnt = None; wh_bds = None; } }

| inv=sform vrnt=sform
    { { wh_inv = inv; wh_vrnt = Some vrnt; wh_bds = None; } }

| inv=sform vrnt=sform k=sform eps=sform
    { { wh_inv = inv; wh_vrnt = Some vrnt; wh_bds = Some (`Bd (k, eps)); } }

async_while_tac_info:
| LBRACKET t1=expr COMMA f1=form RBRACKET
  LBRACKET t2=expr COMMA f2=form RBRACKET p0=sform p1=sform COLON inv=sform
    { { asw_test = ((t1, f1), (t2,f2));
        asw_pred = (p0, p1);
        asw_inv  = inv; } }

rnd_info:
| empty
    { PNoRndParams }

| f=sform
    { PSingleRndParam f }

| f=sform g=sform
    { PTwoRndParams (f, g) }

| phi=sform d1=sform d2=sform d3=sform d4=sform p=sform?
    { PMultRndParams ((phi, d1, d2, d3, d4), p) }

swap_info:
| s=side? p=swap_pos { s,p }

swap_pos:
| i1=word i2=word i3=word
    { SKbase (i1, i2, i3) }

| p=sword
    { SKmove p }

| i1=word p=sword
    { SKmovei (i1, p) }

| LBRACKET i1=word DOTDOT i2=word RBRACKET p=sword
    { SKmoveinter (i1, i2, p) }

side:
| LBRACE n=word RBRACE {
   match n with
   | 1 -> `Left
   | 2 -> `Right
   | _ -> parse_error
              (EcLocation.make $startpos $endpos)
              (Some "variable side must be 1 or 2")
 }

occurences:
| p=paren(word+) {
    if List.mem 0 p then
      parse_error
        (EcLocation.make $startpos $endpos)
        (Some "`0' is not a valid occurence");
    p
  }

dbmap1:
| f=dbmap_flag? x=dbmap_target
    { { pht_flag = odfl `Include f;
        pht_kind = (fst x);
        pht_name = (snd x); } }

%inline dbmap_flag:
| PLUS  { `Include }
| MINUS { `Exclude }

%inline dbmap_target:
| AT x=uqident { (`Theory, x) }
| x=qident     { (`Lemma , x) }

%public dbhint:
| m=dbmap1         { [m] }
| m=paren(dbmap1*) {  m  }

%inline prod_form:
| f1=sform f2=sform   { (Some f1, Some f2) }
| UNDERSCORE f2=sform { (None   , Some f2) }
| f1=sform UNDERSCORE { (Some f1, None   ) }

app_bd_info:
| empty
    { PAppNone }

| f=sform
    { PAppSingle f }

| f=prod_form g=prod_form s=sform?
    { PAppMult (s, fst f, snd f, fst g, snd g) }

revert:
| cl=ioption(brace(loc(ipcore_name)+)) gp=genpattern*
  { { pr_clear = odfl [] cl; pr_genp = gp; } }

%inline have_or_suff:
| HAVE { `Have }
| SUFF { `Suff }

logtactic:
| REFLEX
    { Preflexivity }

| ASSUMPTION
    { Passumption }

| MOVE vw=prefix(SLASH, pterm)* gp=prefix(COLON, revert)?
   { Pmove { pr_rev = odfl prevert0 gp; pr_view = vw; } }

| CLEAR l=loc(ipcore_name)+
   { Pclear l }

| CONGR
   { Pcongr }

| TRIVIAL
   { Ptrivial }

| SMT pi=smt_info
   { Psmt pi }

| SMT LPAREN dbmap=dbmap1* RPAREN
   { Psmt (SMT.mk_smt_option [`WANTEDLEMMAS dbmap]) }

| SPLIT
    { Psplit }

| FIELD eqs=ident*
    { Pfield eqs }

| RING eqs=ident*
    { Pring eqs }

| ALGNORM
   { Palg_norm }

| EXIST a=iplist1(loc(gpterm_arg), empty)
   { Pexists a }

| LEFT
    { Pleft }

| RIGHT
    { Pright }

| ELIM COLON? e=revert
   { Pelim (e, None) }

| ELIM SLASH p=qident COLON? e=revert
   { Pelim (e, Some p) }

| APPLY
   { Papply (`Top `Apply, None) }

| APPLY e=pterm
   { Papply (`Apply ([e], `Apply), None) }

| APPLY COLON e=pterm rv=revert
   { Papply (`Apply ([e], `Apply), Some rv) }

| APPLY es=prefix(SLASH, pterm)+
   { Papply (`Apply (es, `Apply), None) }

| APPLY e=pterm IN x=ident
   { Papply (`ApplyIn (e, x), None) }

| APPLY COLON e=pterm rv=revert IN x=ident
   { Papply (`ApplyIn (e, x), Some rv) }

| EXACT
   { Papply (`Top `Exact, None) }

| EXACT e=pterm
   { Papply (`Apply ([e], `Exact), None) }

| EXACT COLON e=pterm rv=revert
   { Papply (`Apply ([e], `Exact), Some rv) }

| EXACT es=prefix(SLASH, pterm)+
   { Papply (`Apply (es, `Exact), None) }

| l=simplify
   { Psimplify (mk_simplify l) }

| l=cbv
   { Pcbv (mk_simplify l) }

| CHANGE f=sform
   { Pchange f }

| REWRITE a=rwarg+
   { Prewrite (a, None) }

| REWRITE a=rwarg+ IN x=ident
   { Prewrite (a, Some x) }

| RWNORMAL f=sform WITH ps=qident+
   { Prwnormal (f, ps) }

| SUBST l=sform*
   { Psubst l }

| m=have_or_suff ip=loc(intro_pattern)* COLON p=form %prec prec_below_IMPL
   { Pcut (m, ip, p, None) }

| m=have_or_suff ip=loc(intro_pattern)* COLON p=form BY t=loc(tactics)
   { Pcut (m, ip, p, Some t) }

| GEN HAVE x=loc(ipcore_name) ip=prefix(COMMA, loc(intro_pattern)*)?
   COLON ids=loc(ipcore_name)* SLASH f=form %prec prec_below_IMPL
   { Pgenhave (x, ip, ids, f) }

| HAVE ip=loc(intro_pattern)* CEQ fp=pcutdef
   { Pcutdef (ip, fp) }

| POSE o=rwocc? x=ident xs=ptybindings? CEQ p=form_h %prec prec_below_IMPL
   { Ppose (x, odfl [] xs, o, p) }

| POSE x=mident
   { Pmemory x }

| WLOG b=boption(SUFF) COLON ids=loc(ipcore_name)* SLASH f=form
   { Pwlog (ids, b, f) }

eager_info:
| h=ident
    { LE_done h }

| LPAREN h=ident COLON s1=stmt TILD s2=stmt COLON pr=form LONGARROW po=form RPAREN
    { LE_todo (h, s1, s2, pr, po) }

eager_tac:
| SEQ n1=codepos1 n2=codepos1 i=eager_info COLON p=sform
    { Peager_seq (i, (n1, n2), p) }

| IF
    { Peager_if }

| WHILE i=eager_info
    { Peager_while i }

| PROC
    { Peager_fun_def }

| PROC i=eager_info f=sform
    { Peager_fun_abs (i, f) }

| CALL info=gpterm(call_info)
    { Peager_call info }

| info=eager_info COLON p=sform
    { Peager (info, p) }

form_or_double_form:
| f=sform
    { Single f }

| LPAREN UNDERSCORE? COLON f1=form LONGARROW f2=form RPAREN
    { Double (f1, f2) }

%inline if_option:
| s=option(side)
   { `Head (s) }

| s=option(side) i1=o_codepos1 i2=o_codepos1 COLON f=sform
   { `Seq (s, (i1, i2), f) }

| CEQ f=sform
   { `Seq (None, (None, None), f) }

| s=option(side) i=codepos1? COLON LPAREN
    UNDERSCORE COLON f1=form LONGARROW f2=form
  RPAREN
   {
     match s with
     | None ->
       let loc = EcLocation.make $startpos $endpos in
        parse_error loc (Some (
          "must provide a side when only one code-position is given"))
      | Some s -> `SeqOne (s, i, f1, f2)
   }

byequivopt:
| b=boption(MINUS) x=lident {
    match unloc x with
    | "eq"    -> not b
    | _ ->
        parse_error x.pl_loc
          (Some ("invalid option: " ^ (unloc x)))
  }

inlineopt:
| LBRACKET b=boption(MINUS) x=lident RBRACKET {
    match unloc x with
    | "tuple" -> `UseTuple (not b)
    | _ ->
        parse_error x.pl_loc
          (Some ("invalid option: " ^ (unloc x)))

  }

interleavepos:
| LBRACKET c=word COLON n=word RBRACKET
  { c, n }

interleave_info:
| s=side? c1=interleavepos c2=interleavepos c3=interleavepos* k=word
   { (s, c1, c2 :: c3, k) }

%inline outline_kind:
| s=brace(stmt) { OKstmt(s) }
| r=sexpr? LEAT f=loc(fident) { OKproc(f, r) }

phltactic:
| PROC
   { Pfun `Def }

| PROC f=sform
   { Pfun (`Abs f) }

| PROC bad=sform p=sform q=sform?
   { Pfun (`Upto (bad, p, q)) }

| PROC STAR
   { Pfun `Code }

| SEQ s=side? d=tac_dir pos=s_codepos1 COLON p=form_or_double_form f=app_bd_info
   { Papp (s, d, pos, p, f) }

| WP n=s_codepos1?
   { Pwp n }

| SP n=s_codepos1?
    { Psp n }

| SKIP
    { Pskip }

| WHILE s=side? info=while_tac_info
    { Pwhile (s, info) }

| ASYNC WHILE info=async_while_tac_info
    { Pasyncwhile info }

| CALL s=side? info=gpterm(call_info)
    { Pcall (s, info) }

| CALL SLASH fc=sform info=gpterm(call_info)
    { Pcallconcave (fc,info) }

| RCONDT s=side? i=codepos1
    { Prcond (s, true, i) }

| RCONDF s=side? i=codepos1
    { Prcond (s, false, i) }

| MATCH c=oident s=side? i=codepos1
    { Prmatch (s, unloc c, i) }

| IF opt=if_option
    { Pcond opt }

| MATCH s=loc(side?) eq=boption(EQ)
    { match unloc s, eq with
      | None  , false -> Pmatch (`DSided `ConstrSynced)
      | None  , true  -> Pmatch (`DSided `Eq)
      | Some s, false -> Pmatch (`SSided s)
      | Some _, true  ->
          parse_error s.pl_loc (Some "cannot give side and '='") }

| SWAP info=iplist1(loc(swap_info), COMMA) %prec prec_below_comma
    { Pswap info }

| INTERLEAVE info=loc(interleave_info)
    { Pinterleave info }

| CFOLD s=side? c=codepos NOT n=word
    { Pcfold (s, c, Some n) }

| CFOLD s=side? c=codepos
    { Pcfold (s, c, None) }

| RND s=side? info=rnd_info c=prefix(COLON, semrndpos)?
    { Prnd (s, c, info) }

| RNDSEM red=boption(STAR) s=side? c=codepos1
    { Prndsem (red, s, c) }

| INLINE s=side? u=inlineopt? o=occurences?
  { Pinline (`ByName(s, u, ([], o))) }

| INLINE s=side? u=inlineopt? o=occurences? f1=inlinepat1 f=plist0(inlinepat, empty)
  { Pinline (`ByName(s, u, ((`UNION, f1)::f, o))) }

| INLINE s=side? u=inlineopt? p=codepos
    { Pinline (`CodePos (s, u, p)) }

| OUTLINE s=side LBRACKET st=codepos1 e=option(MINUS e=codepos1 {e}) RBRACKET k=outline_kind
    { Poutline {
	  outline_side  = s;
	  outline_start = st;
	  outline_end   = odfl st e;
	  outline_kind  = k }
    }

| KILL s=side? o=codepos
    { Pkill (s, o, Some 1) }

| KILL s=side? o=codepos NOT n=word
    { Pkill (s, o, Some n) }

| KILL s=side? o=codepos NOT STAR
    { Pkill (s, o, None) }

| CASE LARROW s=side? o=codepos
    { Pasgncase (s, o) }

| ALIAS s=side? o=codepos
    { Palias (s, o, None) }

| ALIAS s=side? o=codepos WITH x=lident
    { Palias (s, o, Some x) }

| ALIAS s=side? o=codepos x=lident EQ e=expr
    { Pset (s, o, false, x,e) }

| WEAKMEM s=side? h=loc(ipcore_name) p=param_decl
    { Pweakmem(s, h, p) }

| FISSION s=side? o=codepos AT d1=word COMMA d2=word
    { Pfission (s, o, (1, (d1, d2))) }

| FISSION s=side? o=codepos NOT i=word AT d1=word COMMA d2=word
    { Pfission (s, o, (i, (d1, d2))) }

| FUSION s=side? o=codepos AT d1=word COMMA d2=word
    { Pfusion (s, o, (1, (d1, d2))) }

| FUSION s=side? o=codepos NOT i=word AT d1=word COMMA d2=word
    { Pfusion (s, o, (i, (d1, d2))) }

| UNROLL b=boption(FOR) s=side? o=codepos
    { Punroll (s, o, b) }

| SPLITWHILE s=side? o=codepos COLON c=expr %prec prec_tactic
    { Psplitwhile (c, s, o) }

| BYPHOARE info=gpterm(conseq)?
    { Pbydeno (`PHoare, (mk_rel_pterm info, true, None)) }

| BYEHOARE info=gpterm(conseq)?
    { Pbydeno (`EHoare, (mk_rel_pterm info, true, None)) }

| BYEQUIV eq=bracket(byequivopt)? info=gpterm(conseq)?
    { Pbydeno (`Equiv, (mk_rel_pterm info, odfl true eq, None)) }

| BYEQUIV eq=bracket(byequivopt)? info=gpterm(conseq)? COLON bad1=sform
    { Pbydeno (`Equiv, (mk_rel_pterm info, odfl true eq, Some bad1)) }

| BYUPTO
    { Pbyupto }

| CONSEQ SLASH fc=sform info=gpterm(conseq)
    { Pconcave (info, fc) }

| CONSEQ cq=cqoptions?
    { Pconseq (odfl [] cq, (None, None, None)) }

| CONSEQ cq=cqoptions? info1=gpterm(conseq_xt)
    { Pconseq (odfl [] cq, (Some info1, None, None)) }

| CONSEQ cq=cqoptions? info1=gpterm(conseq_xt) info2=gpterm(conseq_xt) UNDERSCORE?
    { Pconseq (odfl [] cq, (Some info1, Some info2, None)) }

| CONSEQ cq=cqoptions? info1=gpterm(conseq_xt) UNDERSCORE info3=gpterm(conseq_xt)
    { Pconseq (odfl [] cq, (Some info1, None, Some info3)) }

| CONSEQ cq=cqoptions?
    info1=gpterm(conseq_xt)
    info2=gpterm(conseq_xt)
    info3=gpterm(conseq_xt)
      { Pconseq (odfl [] cq, (Some info1,Some info2,Some info3)) }

| CONSEQ cq=cqoptions? UNDERSCORE info2=gpterm(conseq_xt) UNDERSCORE?
    { Pconseq (odfl [] cq, (None,Some info2, None)) }

| CONSEQ cq=cqoptions? UNDERSCORE UNDERSCORE info3=gpterm(conseq_xt)
    { Pconseq (odfl [] cq, (None,None,Some info3)) }

| CONSEQ cm=crushmode { Pconseqauto cm }

| ELIM STAR
    { Phrex_elim }

| b=ID(EXIST STAR { false } | EXLIM { true })
    l=iplist1(sform, COMMA) %prec prec_below_comma

    { Phrex_intro (l, b) }

| ECALL s=side? x=paren(p=qident tvi=tvars_app? fs=sform* { (p, tvi, fs) })
    { Phecall (s, x) }

| EXFALSO
    { Pexfalso }

| BYPR
    { PPr None }

| BYPR f1=sform f2=sform
    { PPr (Some (f1, f2)) }

| FEL at_pos=codepos1 cntr=sform delta=sform q=sform
    f_event=sform some_p=fel_pred_specs inv=sform?
    { let info = {
        pfel_cntr  = cntr;
        pfel_asg   = delta;
        pfel_q     = q;
        pfel_event = f_event;
        pfel_specs = some_p;
        pfel_inv   = inv;
      } in Pfel (at_pos, info) }

| SIM cm=crushmode? info=eqobs_in
    { Psim (cm, info) }

| REPLACE rk=repl_kind h1=repl_hyp h2=repl_hyp
    { Ptrans_stmt (rk, TFform(fst h1, snd h1, fst h2, snd h2)) }

| REPLACE STAR rk=repl_kind
    { Ptrans_stmt (rk, TFeq) }

| TRANSITIVITY tk=trans_kind h1=trans_hyp h2=trans_hyp
    { Ptrans_stmt (tk, TFform(fst h1, snd h1, fst h2, snd h2)) }

| TRANSITIVITY STAR tk=trans_kind
    { Ptrans_stmt (tk, TFeq) }

| REWRITE EQUIV LBRACKET
    s=side cp=codepos1 rws=rwside x=pterm proc=rweqv_proc?
  RBRACKET
    {
      let info = {
          rw_eqv_side  = s;
          rw_eqv_dir   = rws;
          rw_eqv_pos   = cp;
          rw_eqv_lemma = x;
          rw_eqv_proc = proc;
        }
      in
      Prw_equiv info
    }

| SYMMETRY
    { Psymmetry }

| EAGER t=eager_tac
    { t }

| HOARE
    { Phoare }

| PRBOUNDED
    { Pprbounded }

| PHOARE SPLIT i=bdhoare_split
    { Pbdhoare_split i }

| PHOARE EQUIV s=side pr=sform po=sform
    { Pbd_equiv (s, pr, po) }

| AUTO
    { Pauto }

| LOSSLESS
    { Plossless }

| PROC CHANGE side=side? pos=codepos COLON f=sexpr
    { Pprocchange (side, pos, f) }

| PROC REWRITE side=side? pos=codepos f=pterm
    { Pprocrewrite (side, pos, f) }

bdhoare_split:
| b1=sform b2=sform b3=sform?
    { BDH_split_bop (b1,b2,b3) }

| b1=sform b2=sform COLON f=sform
    { BDH_split_or_case (b1,b2,f) }

| NOT b1=sform b2=sform
    { BDH_split_not (Some b1,b2) }

%inline trans_kind:
| s=side c=brace(stmt)
    { TKstmt(s, c) }

| f=loc(fident)
    { TKfun (f) }

%inline trans_hyp:
| LPAREN p=form LONGARROW q=form RPAREN { (p,q) }

%inline rweqv_res:
| COLON AT res=sexpr { res }

%inline rweqv_proc:
| p=paren(args=loc(plist0(expr, COMMA)) res=rweqv_res? {args, res}) {p}

%inline repl_kind:
| s=side p=im_block BY c=brace(stmt)
    { TKparsedStmt (s, p, c) }

%inline repl_hyp:
| h=trans_hyp
    { h }

fel_pred_spec:
| f=loc(fident) COLON p=sform
    { (f, p) }

fel_pred_specs:
| LBRACKET assoc_ps = plist0(fel_pred_spec, SEMICOLON) RBRACKET
    {assoc_ps}

eqobs_in_pos:
| i1=codepos1 i2=codepos1 { (i1, i2) }

eqobs_in_eqglob1:
| LPAREN mp1= uoption(loc(fident)) TILD mp2= uoption(loc(fident)) COLON
  geq=form RPAREN
  {((mp1, mp2),geq) }

| LPAREN UNDERSCORE? COLON geq=form RPAREN { ((None,None), geq) }

eqobs_in_inv:
| SLASH inv=sform { inv }

eqobs_in_eqinv:
| geqs=eqobs_in_eqglob1* inv=eqobs_in_inv? { (geqs,inv) }

eqobs_in_eqpost:
| COLON f=sform   { f }

eqobs_in:
| pos=eqobs_in_pos? i=eqobs_in_eqinv p=eqobs_in_eqpost? {
    { sim_pos  = pos;
      sim_hint = i;
      sim_eqs  = p; }
}

pgoptionkw:
| x=loc(SPLIT) { mk_loc x.pl_loc "split" }
| x=loc(SUBST) { mk_loc x.pl_loc "subst" }
| x=lident     { x }

pgoption:
| b=boption(MINUS) DELTA
    { (not b, `Delta None) }

| b=boption(MINUS) DELTA COLON SPLIT
    { (not b, `Delta (Some `Split)) }

| b=boption(MINUS) DELTA COLON CASE
    { (not b, `Delta (Some `Case)) }

| b=boption(MINUS) x=pgoptionkw {
    match unloc x with
    | "split"    -> (not b, `Split)
    | "solve"    -> (not b, `Solve)
    | "subst"    -> (not b, `Subst)
    | "disjunct" -> (not b, `Disjunctive)
    | _ ->
        parse_error x.pl_loc
          (Some ("invalid option: " ^ (unloc x)))
  }

%inline pgoptions:
| AT? xs=bracket(pgoption+) { xs }

cqoptionkw:
| x=lident { x }

cqoption:
| b=boption(MINUS) x=cqoptionkw {
    match unloc x with
    | "frame" -> (not b, `Frame)
    | _ ->
        parse_error x.pl_loc
          (Some ("invalid option: " ^ (unloc x)))
  }

%inline cqoptions:
| xs=bracket(cqoption+) { xs }

caseoption:
| b=boption(MINUS) x=lident {
    match unloc x with
    | "ambient" -> (not b, `Ambient)
    | _ ->
       parse_error x.pl_loc
         (Some ("invalid option: " ^ (unloc x)))
  }

%inline caseoptions:
| AT xs=bracket(caseoption+) { xs }

%inline do_repeat:
| n=word? NOT      { (`All, n) }
| n=word? QUESTION { (`Maybe, n) }

tactic_core_r:
| IDTAC
   { Pidtac None }

| IDTAC s=STRING
   { Pidtac (Some s) }

| TRY t=tactic_core
   { Ptry t }

| TRY NOT t=tactic_core
   { Pnstrict t }

| BY t=tactics
   { Pby (Some t) }

| BY bracket(empty) | DONE
   { Pby None }

| SOLVE dp=word? base=option(paren(plist1(lident, COMMA)))
   { Psolve (dp, base) }

| DO r=do_repeat? t=tactic_core
   { Pdo (odfl (`All, None) r, t) }

| LPAREN s=tactics RPAREN
   { Pseq s }

| ADMIT
   { Padmit }

| CASE vw=prefix(SLASH, pterm)*
     opts=ioption(caseoptions)
     eq=ioption(postfix(boption(UNDERSCORE), COLON))
     gp=revert

    { Pcase (odfl false eq, odfl [] opts,
             { pr_view = vw; pr_rev = gp; } ) }

| PROGRESS opts=pgoptions? t=tactic_core? {
    Pprogress (odfl [] opts, t)
  }

| x=logtactic
   { Plogic x }

| x=phltactic
   { PPhl x }

%public %inline tactic_core:
| x=loc(tactic_core_r) { x }

%inline tcfc_1:
| i=loc(sword) {
    if i.pl_desc = 0 then
      parse_error i.pl_loc (Some "focus-index must be positive");
    i.pl_desc
  }

%inline tcfc_rg:
| i1=tcfc_1                  { (Some i1, Some i1) }
| i1=tcfc_1 DOTDOT i2=tcfc_1 { (Some i1, Some i2) }
| i1=tcfc_1 DOTDOT           { (Some i1, None   ) }
|           DOTDOT i2=tcfc_1 { (None   , Some i2) }

%inline tcfc_set:
| xs=plist1(tcfc_rg, COMMA) { xs }

%inline tcfc:
| s1=tcfc_set
    { (Some s1, None) }

| s1=tcfc_set? TILD s2=tcfc_set
    { (s1, Some s2) }

tactic_chain_r:
| LBRACKET ts=plist1(loc(tactics0), PIPE) RBRACKET
    { Psubtacs (List.map mk_core_tactic ts) }

| LBRACKET ts=plist1(sep(tcfc, COLON, loc(tactics)), PIPE) RBRACKET
    { let ts = List.map (snd_map mk_tactic_of_tactics) ts in
      Pfsubtacs (ts, None) }

| LBRACKET
    ts=plist1(sep(tcfc, COLON, loc(tactics)), PIPE) ELSE t=loc(tactics)
  RBRACKET
    { let ts = List.map (snd_map mk_tactic_of_tactics) ts in
      Pfsubtacs (ts, Some (mk_tactic_of_tactics t)) }

| FIRST t=loc(tactics) { Pfirst (mk_tactic_of_tactics t, 1) }
| LAST  t=loc(tactics) { Plast  (mk_tactic_of_tactics t, 1) }

| FIRST n=word t=loc(tactics) { Pfirst (mk_tactic_of_tactics t, n) }
| LAST  n=word t=loc(tactics) { Plast  (mk_tactic_of_tactics t, n) }

| FIRST LAST  { Protate (`Left , 1) }
| LAST  FIRST { Protate (`Right, 1) }

| FIRST n=word LAST  { Protate (`Left , n) }
| LAST  n=word FIRST { Protate (`Right, n) }

| EXPECT n=word
    { Pexpect (`None, n) }

| EXPECT n=word t=loc(tactics)
    { Pexpect (`Tactic (mk_tactic_of_tactics t), n) }

| EXPECT n=word t=loc(paren(rlist1(tactic_chain_r, SEMICOLON)))
    { Pexpect (`Chain t, n) }

| fc=tcfc COLON t=tactic
    { Pfocus (t, fc) }

tactic_chain:
| t=loc(tactic_chain_r) %prec prec_below_IMPL
    { mk_core_tactic (mk_loc t.pl_loc (Psubgoal (unloc t))) }

| t=loc(tactic_chain_r) ip=plist1(tactic_genip, empty)
    { let t = mk_loc t.pl_loc (Psubgoal (unloc t)) in
      { pt_core = t; pt_intros = ip; } }

subtactic:
| t=tactic_chain
| t=tactic
    { t }

%inline subtactics:
| x=rlist1(subtactic, SEMICOLON) { x }

%public tactics:
| t=tactic %prec SEMICOLON { [t] }
| t=tactic SEMICOLON ts=subtactics { t :: ts }

tactics0:
| ts=tactics   { Pseq ts }
| x=loc(empty) { Pseq [mk_core_tactic (mk_loc x.pl_loc (Pidtac None))] }

%public toptactic:
| PLUS  t=tactics { t }
| STAR  t=tactics { t }
| MINUS t=tactics { t }
|       t=tactics { t }

%public tactics_or_prf:
| t=toptactic  { `Actual t }
| PROOF        { `Proof    }

tactic_ip:
| t=tactic_core %prec prec_below_IMPL
    { mk_core_tactic t }

| t=tactic_core ip=plist1(tactic_genip, empty)
    { { pt_core = t; pt_intros = ip; } }

%inline tactic_genip:
| IMPL ip=loc(intro_pattern)+
    { `Ip ip }

| LEAT gn=revert
    { `Gen gn }

%public tactic:
| t=tactic_ip %prec prec_below_IMPL
    { t }

| t1=tactic_ip ORA t2=tactic
    { let loc = EcLocation.make $startpos $endpos in
        mk_core_tactic (mk_loc loc (Por (t1, t2))) }
