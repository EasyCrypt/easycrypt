%%
(* -------------------------------------------------------------------- *)
(* Theory cloning                                                       *)

clone_import:
| EXPORT  { `Export  }
| IMPORT  { `Import  }
| INCLUDE { `Include }

clone_opt:
| b=boption(MINUS) ABSTRACT { (not b, `Abstract) }

clone_opts:
| xs=bracket(clone_opt+) { xs }

clone_with:
| WITH x=plist1(clone_override, COMMA) { x }

clone_lemma_tag:
|       x=ident { (`Include, x) }
| MINUS x=ident { (`Exclude, x) }

clone_lemma_base:
| STAR x=bracket(clone_lemma_tag+)?
    { `All (odfl [] x) }

| x=_ident
    { `Named x }

clone_lemma_1_core:
| l=genqident(clone_lemma_base) {
    match unloc l with
    | (xs, `Named x ) -> `Named (mk_loc l.pl_loc (xs, x), `Alias)
    | (xs, `All tags) -> begin
      match List.rev xs with
      | []      -> `All (None, tags)
      | x :: xs -> `All (Some (mk_loc l.pl_loc (List.rev xs, x)), tags)
    end
  }

clone_lemma_1:
| cl=clone_lemma_1_core
    { { pthp_mode = cl; pthp_tactic = None; } }

| cl=clone_lemma_1_core BY t=tactic_core
    { { pthp_mode = cl; pthp_tactic = Some t; } }

clone_lemma:
| x=plist1(clone_lemma_1, COMMA) { x }

clone_proof:
| PROOF x=clone_lemma { x }

clone_rename_kind:
| TYPE        { `Type    }
| OP          { `Op      }
| PRED        { `Pred    }
| LEMMA       { `Lemma   }
| MODULE      { `Module  }
| MODULE TYPE { `ModType }
| THEORY      { `Theory  }

clone_rename_1:
| k=bracket(plist1(clone_rename_kind, COMMA))? r1=loc(STRING) AS r2=loc(STRING)
    { (odfl [] k, (r1, r2)) }

clone_rename:
| RENAME rnm=clone_rename_1+ { rnm }

clone_clear_1:
| ABBREV qs=qoident+
  { List.map (fun x -> (`Abbrev, x)) qs }

clone_clear:
| REMOVE cl=clone_clear_1+ { List.flatten cl }

opclmode:
| EQ       { `Alias         }
| LARROW   { `Inline `Clear }
| LE       { `Inline `Keep  }

cltyparams:
| empty { [] }
| x=tident { [x] }
| xs=paren(plist1(tident, COMMA)) { xs }

clone_override:
| TYPE ps=cltyparams x=qident mode=opclmode t=loc(type_exp)
   { (x, PTHO_Type (`BySyntax (ps, t), mode)) }

| OP st=nosmt x=qoident tyvars=bracket(tident*)?
    p=ptybinding1* sty=ioption(prefix(COLON, loc(type_exp)))
    mode=loc(opclmode) f=form

   { let ov = {
       opov_nosmt  = st;
       opov_tyvars = tyvars;
       opov_args   = List.flatten p;
       opov_retty  = odfl (mk_loc mode.pl_loc PTunivar) sty;
       opov_body   = f;
     } in

     (x, PTHO_Op (`BySyntax ov, unloc mode)) }

| PRED x=qoident tyvars=bracket(tident*)? p=ptybinding1* mode=loc(opclmode) f=form
   { let ov = {
       prov_tyvars = tyvars;
       prov_args   = List.flatten p;
       prov_body   = f;
     } in

      (x, PTHO_Pred (`BySyntax ov, unloc mode)) }

| AXIOM x=qoident mode=loc(opclmode) y=qoident
  { x, PTHO_Axiom (y, unloc mode) }

| LEMMA x=qoident mode=loc(opclmode) y=qoident
  { x, PTHO_Axiom (y, unloc mode) }

| MODULE uqident loc(opclmode) uqident
   { parse_error
       (EcLocation.make $startpos $endpos)
       (Some "Module overriding is no longer supported.")
   }

| MODULE TYPE x=uqident mode=loc(opclmode) y=uqident
   { (x, PTHO_ModTyp (y, unloc mode)) }

| THEORY x=uqident mode=loc(opclmode) y=uqident
   { (x, PTHO_Theory (y, unloc mode)) }

(* -------------------------------------------------------------------- *)
%public realize:
| REALIZE x=qident
    {  { pr_name = x; pr_proof = None; } }

| REALIZE x=qident BY t=tactics
    {  { pr_name = x; pr_proof = Some (Some t); } }

| REALIZE x=qident BY bracket(empty)
    {  { pr_name = x; pr_proof = Some None; } }

(* -------------------------------------------------------------------- *)
%public theory_clone:
| local=is_local CLONE options=clone_opts?
    ip=clone_import? x=uqident y=prefix(AS, uident)? cw=clone_with?
    c=or3(clone_proof, clone_rename, clone_clear)*

   { let (cp, cr, cl) =
       List.fold_left (fun (cp, cr, cl) -> function
        | `Or13 x -> (cp@x, cr, cl)
        | `Or23 y -> (cp, cr@y, cl)
        | `Or33 z -> (cp, cr, cl@z))
       ([], [], []) c in

     { pthc_base   = x;
       pthc_name   = y;
       pthc_ext    = EcUtils.odfl [] cw;
       pthc_prf    = cp;
       pthc_rnm    = cr;
       pthc_clears = cl;
       pthc_opts   = odfl [] options;
       pthc_local  = local;
       pthc_import = ip; } }
