%start prog global is_uniop is_binop is_numop

%%

(* -------------------------------------------------------------------- *)
%public %inline ordering_op:
| GT { ">"  }
| LT { "<"  }
| GE { ">=" }
| LE { "<=" }

%public %inline uniop:
| x=NOP { Printf.sprintf "[%s]" x }
| NOT   { "[!]" }
| PLUS  { "[+]" }
| MINUS { "[-]" }

%public %inline sbinop:
| EQ        { "="   }
| NE        { "<>"  }
| PLUS      { "+"   }
| MINUS     { "-"   }
| STAR      { "*"   }
| SLASH     { "/"   }
| AT        { "@"   }
| OR        { "\\/" }
| ORA       { "||"  }
| AND       { "/\\" }
| ANDA      { "&&"  }
| AMP       { "&"   }
| HAT       { "^"   }
| BACKSLASH { "\\"  }

| x=LOP1 | x=LOP2 | x=LOP3 | x=LOP4
| x=ROP1 | x=ROP2 | x=ROP3 | x=ROP4
| x=NOP
    { x }

%public %inline binop:
| op=sbinop { op    }
| IMPL      { "=>"  }
| IFF       { "<=>" }

%public %inline numop:
| op=NUMOP { op }

(* -------------------------------------------------------------------- *)
is_binop: binop EOF {}
is_uniop: uniop EOF {}
is_numop: numop EOF {}

(* -------------------------------------------------------------------- *)
pside_:
| x=_lident { Printf.sprintf "&%s" x }
| x=word    { Printf.sprintf "&%d" x }

%public pside:
| x=brace(pside_) { x }

(* -------------------------------------------------------------------- *)
(* Patterns                                                             *)

lpattern_u:
| x=ident
    { LPSymbol x }

| LPAREN p=plist2(bdident, COMMA) RPAREN
    { LPTuple p }

| LPBRACE fs=rlist1(lp_field, SEMICOLON) SEMICOLON? RPBRACE
    { LPRecord fs }

lp_field:
| f=qident EQ x=ident { (f, x) }

%public %inline lpattern:
| x=loc(lpattern_u) { x }

(* -------------------------------------------------------------------- *)
(* Expressions: program expression, real expression                     *)

tyvar_byname1:
| x=tident EQ ty=loc(type_exp) { (x, ty) }

tyvar_annot:
| lt = plist1(loc(type_exp), COMMA) { TVIunamed lt }
| lt = plist1(tyvar_byname1, COMMA) { TVInamed lt }

%public %inline tvars_app:
| LTCOLON k=loc(tyvar_annot) GT { k }

(* -------------------------------------------------------------------- *)
bdident_:
| x=ident    { Some x }
| UNDERSCORE { None }

%inline bdident:
| x=loc(bdident_) { x }

pty_varty:
| x=loc(bdident+)
   { (unloc x, mk_loc (loc x) PTunivar) }

| x=bdident+ COLON ty=loc(type_exp)
   { (x, ty) }

%public %inline ptybinding1:
| LPAREN bds=plist1(pty_varty, COMMA) RPAREN
    { bds }

| x=loc(bdident)
   { [[unloc x], mk_loc (loc x) PTunivar] }

%public ptybindings:
| x=ptybinding1+
    { List.flatten x }

| x=bdident+ COLON ty=loc(type_exp)
   { [x, ty] }

ptybindings_decl:
| x=ptybinding1+
    { List.flatten x }

ptybindings_opdecl:
| x=ptybinding1+
    { (List.flatten x, None) }

| x=ptybinding1* SLASH y=ptybinding1*
    { (List.flatten x, Some (List.flatten y)) }

(* -------------------------------------------------------------------- *)
(* Formulas                                                             *)

orcl_time(P):
 | m=uident DOT f=lident COLON c=form_r(P) { (m,f, c) }

%public qident_or_res_or_glob:
| x=qident
    { GVvar x }

| x=loc(RES)
    { GVvar (mk_loc x.pl_loc ([], "res")) }

| GLOB mp=loc(mod_qident)
    { GVglob (mp, []) }

| GLOB mp=loc(mod_qident) BACKSLASH ex=brace(plist1(qident, COMMA))
    { GVglob (mp, ex) }

pfpos:
| i=sword
    { `Index i }

| f=bracket(form_h) off=pfoffset?
    { `Match (f, off) }

pfoffset:
| PLUS  w=word {  w }
| MINUS w=word { -w }

%public pffilter:
| LBRACKET flat=iboption(SLASH)
    rg=plist0(
      i=pfpos? COLON j=pfpos? { `Range (i, j) }
    | i=pfpos { `Single i }, COMMA)
  RBRACKET

  { PFRange (flat, rg) }

| LPBRACE flat=iboption(SLASH) x=ident IN h=form_h RPBRACE

  { PFMatch (flat, x, h) }

| LPBRACE flat=iboption(SLASH)
    f=form FOR xs=plist1(ident, COMMA) IN h=form_h
  RPBRACE

  { PFMatchBuild (flat, xs, f, h) }

| LBRACE
    flat=iboption(SLASH)
    exclude=iboption(TILD)
    rooted=iboption(HAT)
    h=pffilter_pattern
  RBRACE

  { PFKeep (flat, rooted, exclude, h) }

pffilter_pattern:
| f=form_h
    { `Pattern f}

| LBRACE xs=plist0(x=qoident s=loc(pside)? { (x, s) }, COMMA) RBRACE
    { `VarSet xs }


pgtybinding1:
| x=ptybinding1
    { List.map (fun (xs, ty) -> (xs, PGTY_Type ty)) x }

| LPAREN x=uident LTCOLON mi=mod_type_with_restr RPAREN
    { [[mk_loc (loc x) (Some x)], PGTY_ModTy mi] }

| pn=mident
    { [[mk_loc (loc pn) (Some pn)], PGTY_Mem None] }

| LPAREN pn=mident COLON mt=memtype RPAREN
    { [[mk_loc (loc pn) (Some pn)], PGTY_Mem (Some mt)] }

%public pgtybindings:
| x=pgtybinding1+ { List.flatten x }

(* -------------------------------------------------------------------- *)
(* Type expressions                                                     *)

simpl_type_exp:
| UNDERSCORE                  { PTunivar       }
| x=qident                    { PTnamed x      }
| x=tident                    { PTvar x        }
| tya=type_args x=qident      { PTapp (x, tya) }
| GLOB m=loc(mod_qident)      { PTglob m       }
| LPAREN ty=type_exp RPAREN   { ty             }

type_args:
| ty=loc(simpl_type_exp)                          { [ty] }
| LPAREN tys=plist2(loc(type_exp), COMMA) RPAREN  { tys  }

%public type_exp:
| ty=simpl_type_exp                          { ty }
| ty=plist2(loc(simpl_type_exp), STAR)       { PTtuple ty }
| ty1=loc(type_exp) RARROW ty2=loc(type_exp) { PTfun(ty1,ty2) }

(* -------------------------------------------------------------------- *)
(* Parameter declarations                                              *)
var_or_anon:
| x=loc(UNDERSCORE)
    { mk_loc x.pl_loc None }

| x=ident
    { mk_loc x.pl_loc (Some x) }

typed_vars_or_anons:
| xs=var_or_anon+ COLON ty=loc(type_exp)
   { List.map (fun v -> (v, ty)) xs }

| xs=var_or_anon+
    { List.map (fun v -> (v, mk_loc v.pl_loc PTunivar)) xs }

%public param_decl:
| LPAREN aout=plist0(typed_vars_or_anons, COMMA) RPAREN
    { List.flatten aout }

(* -------------------------------------------------------------------- *)
(* Statements                                                           *)

lvalue_u:
| x=loc(fident)
   { match lqident_of_fident x.pl_desc with
     | None   -> parse_error x.pl_loc None
     | Some v -> PLvSymbol (mk_loc x.pl_loc v) }

| LPAREN p=plist2(qident, COMMA) RPAREN
   { PLvTuple p }

| x=loc(fident) DLBRACKET ti=tvars_app? e=expr RBRACKET
   { match lqident_of_fident x.pl_desc with
     | None   -> parse_error x.pl_loc None
     | Some v -> PLvMap (mk_loc x.pl_loc v, ti, e) }

%inline lvalue:
| x=loc(lvalue_u) { x }

base_instr:
| x=lident
    { PSident x }

| x=lvalue LESAMPLE  e=expr
    { PSrnd (x, e) }

| x=lvalue LARROW e=expr
    { PSasgn (x, e) }

| x=lvalue LEAT f=loc(fident) LPAREN es=loc(plist0(expr, COMMA)) RPAREN
    { PScall (Some x, f, es) }

| f=loc(fident) LPAREN es=loc(plist0(expr, COMMA)) RPAREN
    { PScall (None, f, es) }

| ASSERT LPAREN c=expr RPAREN
    { PSassert c }

instr:
| bi=base_instr SEMICOLON
   { bi }

| i=if_expr
   { i }

| WHILE LPAREN c=expr RPAREN b=block
   { PSwhile (c, b) }

| MATCH e=expr WITH PIPE? bs=plist0(match_branch, PIPE) END SEMICOLON
   { PSmatch (e, `Full bs) }

| IF LPAREN e=expr IS c=opptn RPAREN b1=block b2=option(prefix(ELSE, block))
   { PSmatch (e, `If ((c, b1), b2)) }

%inline if_expr:
| IF c=paren(expr) b=block el=if_else_expr
   { PSif ((c, b), fst el, snd el) }

if_else_expr:
|  /* empty */ { ([], []) }
| ELSE b=block { ([],  b) }

| ELIF e=paren(expr) b=block el=if_else_expr
    { ((e, b) :: fst el, snd el) }

match_branch:
| c=opptn IMPL b=block
    { (c, b) }

block:
| i=loc(base_instr) SEMICOLON
    { [i] }

| stmt=brace(stmt)
   { stmt }

%public stmt: aout=loc(instr)* { aout }

(* -------------------------------------------------------------------- *)
(* Module definition                                                    *)

var_decl:
| VAR xs=plist1(lident, COMMA) COLON ty=loc(type_exp)
   { (xs, ty) }

loc_decl_names:
| x=plist1(lident, COMMA) { (`Single, x) }

| LPAREN x=plist2(lident, COMMA) RPAREN { (`Tuple, x) }

loc_decl_r:
| VAR x=loc(loc_decl_names)
    { { pfl_names = x; pfl_type = None; pfl_init = None; } }

| VAR x=loc(loc_decl_names) COLON ty=loc(type_exp)
    { { pfl_names = x; pfl_type = Some ty; pfl_init = None; } }

| VAR x=loc(loc_decl_names) COLON ty=loc(type_exp) LARROW e=expr
    { { pfl_names = x; pfl_type = Some ty; pfl_init = Some e; } }

| VAR x=loc(loc_decl_names) LARROW e=expr
    { { pfl_names = x; pfl_type = None; pfl_init = Some e; } }

loc_decl:
| x=loc_decl_r SEMICOLON { x }

memtype_decl:
| x=loc(loc_decl_names) COLON ty=loc(type_exp)
    { x,ty }

memtype:
| LBRACE m=rlist0(memtype_decl,COMMA) RBRACE {m}

ret_stmt:
| RETURN e=expr SEMICOLON
    { Some e }

| empty
    { None }

fun_def_body:
| LBRACE decl=loc_decl* s=stmt rs=ret_stmt RBRACE
    { { pfb_locals = decl;
        pfb_body   = s   ;
        pfb_return = rs  ; }
    }

fun_decl:
| x=lident pd=param_decl ty=prefix(COLON, loc(type_exp))?
    { let frestr = { pmre_name = x; pmre_orcls = None; } in
      { pfd_name     = x;
        pfd_tyargs   = pd;
        pfd_tyresult = odfl (mk_loc x.pl_loc PTunivar) ty;
        pfd_uses     = frestr; }
    }

minclude_proc:
| PLUS? xs=plist1(lident,COMMA) { `MInclude xs }
| MINUS xs=plist1(lident,COMMA) { `MExclude xs }

mod_item:
| v=var_decl
    { Pst_var v }

| MODULE x=uident c=mod_cast? EQ m=loc(mod_body)
    { Pst_mod (x, odfl [] c, m) }

| PROC decl=loc(fun_decl) EQ body=fun_def_body {
    let { pl_desc = decl; } = decl in
    Pst_fun (decl, body)
  }

| PROC x=lident EQ f=loc(fident)
    { Pst_alias (x, f) }

| INCLUDE v=boption(VAR) m=loc(mod_qident) xs=bracket(minclude_proc)?
    { Pst_include (m, v, xs) }

| IMPORT VAR ms=loc(mod_qident)+
    { Pst_import ms }

(* -------------------------------------------------------------------- *)
(* Modules                                                              *)

mod_body:
| m=mod_qident
    { Pm_ident m }

| LBRACE stt=loc(mod_item)* RBRACE
    { Pm_struct stt }

mod_def_or_decl:
| locality=locality MODULE header=mod_header c=mod_cast? EQ ptm_body=loc(mod_body)
  { let ptm_header = match c with None -> header | Some c ->  Pmh_cast(header,c) in
    { ptm_def      = `Concrete { ptm_header; ptm_body; };
      ptm_locality = locality; } }

| locality=locality MODULE ptm_name=uident LTCOLON ptm_modty=mod_type_with_restr
    { { ptm_def      = `Abstract { ptm_name; ptm_modty; };
        ptm_locality = locality; } }

mod_header:
| x=uident                  { Pmh_ident x }
| mh=loc(mod_header_params) { Pmh_params mh }
| LPAREN mh=mod_header c=mod_cast RPAREN { Pmh_cast(mh,c) }

mod_cast:
| COLON c=plist1(uqident,COMMA) { c }

mod_header_params:
| mh=mod_header p=mod_params { mh,p }

mod_params:
| LPAREN a=plist1(sig_param, COMMA) RPAREN  { a }

(* -------------------------------------------------------------------- *)
(* Memory restrictions *)

mem_restr_el:
  | PLUS  el=f_or_mod_ident { PMPlus el }
  | MINUS el=f_or_mod_ident { PMMinus el }
  |       el=f_or_mod_ident { PMDefault el }

mem_restr:
  | ol=rlist0(mem_restr_el,COMMA) { ol }

(* -------------------------------------------------------------------- *)
(* qident optionally taken in a (implicit) module parameters. *)
qident_inparam:
| SHARP q=qident { { inp_in_params = true;
		     inp_qident    = q; } }
| q=qident { { inp_in_params = false;
	       inp_qident    = q; } }

(* -------------------------------------------------------------------- *)
(* Oracle restrictions *)
oracle_restr:
  | LBRACE ol=rlist0(qident_inparam,COMMA) RBRACE { ol }

(* -------------------------------------------------------------------- *)
(* Module restrictions *)

mod_restr_el:
  | f=lident COLON orcls=option(oracle_restr)
    { { pmre_name = f; pmre_orcls = orcls; } }

mod_restr:
  | LBRACE mr=mem_restr RBRACE
    { { pmr_mem = mr; pmr_procs = [] } }
  | LBRACKET l=rlist1(mod_restr_el,COMMA) RBRACKET
    { { pmr_mem = []; pmr_procs = l } }
  | LBRACE mr=mem_restr RBRACE LBRACKET l=rlist1(mod_restr_el,COMMA) RBRACKET
    { { pmr_mem = mr;	pmr_procs = l } }
  | LBRACKET l=rlist1(mod_restr_el,COMMA) RBRACKET LBRACE mr=mem_restr RBRACE
    { { pmr_mem = mr;	pmr_procs = l } }

(* -------------------------------------------------------------------- *)
(* Modules interfaces                                                   *)

%inline mod_type:
| x = qident { x }

%inline mod_type_with_restr:
| x = qident
    { { pmty_pq = x; pmty_mem = None; } }

| x = qident mr=mod_restr
    { { pmty_pq = x; pmty_mem = Some mr; } }

sig_def:
| pi_locality=loc(locality) MODULE TYPE pi_name=uident args=sig_params* mr=mod_restr? EQ i=sig_body
    { let pi_sig =
        Pmty_struct { pmsig_params = List.flatten args;
                      pmsig_body   = i;
			                pmsig_restr  = mr; } in
      { pi_name; pi_sig; pi_locality = locality_as_local pi_locality; } }

sig_body:
| body=sig_struct_body { body }

sig_struct_body:
| LBRACE ty=signature_item* RBRACE
    { ty }

sig_params:
| LPAREN params=plist1(sig_param, COMMA) RPAREN
    { params }

sig_param:
| x=uident COLON i=mod_type { (x, i) }

signature_item:
| INCLUDE i=mod_type xs=bracket(minclude_proc)? qs=brace(qident*)?
    { let qs = qs |> omap (List.map (fun x ->
        { inp_in_params = false; inp_qident = x;  }))
      in `Include (i, xs, qs) }

| PROC x=lident pd=param_decl COLON ty=loc(type_exp) orcls=option(oracle_restr)
    { `FunctionDecl
         { pfd_name     = x;
           pfd_tyargs   = pd;
           pfd_tyresult = ty;
           pfd_uses     = { pmre_name = x; pmre_orcls = orcls; } } }

(* -------------------------------------------------------------------- *)
%inline locality:
| (* empty *) { `Global }
| LOCAL       { `Local }
| DECLARE     { `Declare }

| LOCAL DECLARE
| DECLARE LOCAL
    { parse_error
        (EcLocation.make $startpos $endpos)
        (Some "cannot mix declare & local") }

%public %inline is_local:
| lc=loc(locality) { locality_as_local lc }

(* -------------------------------------------------------------------- *)
(* EcTypes declarations / definitions                                   *)

typaram:
| x=tident { (x, []) }
| x=tident LTCOLON tc=plist1(lqident, AMP) { (x, tc) }

typarams:
| empty { []  }
| x=tident { [(x, [])] }
| xs=paren(plist1(typaram, COMMA)) { xs }

%inline tyd_name:
| tya=typarams x=ident { (tya, x) }

dt_ctor_def:
| x=oident { (x, []) }
| x=oident OF ty=plist1(loc(simpl_type_exp), AMP) { (x, ty) }

%inline datatype_def:
| LBRACKET PIPE? ctors=plist1(dt_ctor_def, PIPE) RBRACKET { ctors }

rec_field_def:
| x=ident COLON ty=loc(type_exp) { (x, ty); }

%inline record_def:
| LBRACE fields=rlist1(rec_field_def, SEMICOLON) SEMICOLON? RBRACE
    { fields }

typedecl:
| locality=locality TYPE td=rlist1(tyd_name, COMMA)
    { List.map (fun x -> mk_tydecl ~locality x (PTYD_Abstract [])) td }

| locality=locality TYPE td=tyd_name LTCOLON tcs=rlist1(qident, COMMA)
    { [mk_tydecl ~locality td (PTYD_Abstract tcs)] }

| locality=locality TYPE td=tyd_name EQ te=loc(type_exp)
    { [mk_tydecl ~locality td (PTYD_Alias te)] }

| locality=locality TYPE td=tyd_name EQ te=record_def
    { [mk_tydecl ~locality td (PTYD_Record te)] }

| locality=locality TYPE td=tyd_name EQ te=datatype_def
    { [mk_tydecl ~locality td (PTYD_Datatype te)] }

(* -------------------------------------------------------------------- *)
(* Type classes                                                         *)
typeclass:
| loca=is_local TYPE CLASS x=lident inth=tc_inth? EQ LBRACE body=tc_body RBRACE {
    { ptc_name = x;
      ptc_inth = inth;
      ptc_ops  = fst body;
      ptc_axs  = snd body;
      ptc_loca = loca;
    }
  }

tc_inth:
| LTCOLON x=lqident { x }

tc_body:
| ops=tc_op* axs=tc_ax* { (ops, axs) }

tc_op:
| OP x=oident COLON ty=loc(type_exp) { (x, ty) }

tc_ax:
| AXIOM x=ident COLON ax=form { (x, ax) }

(* -------------------------------------------------------------------- *)
(* Type classes (instances)                                             *)
tycinstance:
| loca=is_local INSTANCE x=qident
    WITH typ=tyvars_decl? ty=loc(type_exp) ops=tyci_op* axs=tyci_ax*
  {
    { pti_name = x;
      pti_type = (odfl [] typ, ty);
      pti_ops  = ops;
      pti_axs  = axs;
      pti_args = None;
      pti_loca = loca;
    }
  }

| loca=is_local INSTANCE x=qident c=uoption(UINT) p=uoption(UINT)
    WITH typ=tyvars_decl? ty=loc(type_exp) ops=tyci_op* axs=tyci_ax*
  {
    { pti_name = x;
      pti_type = (odfl [] typ, ty);
      pti_ops  = ops;
      pti_axs  = axs;
      pti_args = Some (`Ring (c, p));
      pti_loca = loca;
    }
  }

tyci_op:
| OP x=oident EQ tg=qoident
    { (x, ([], tg)) }

| OP x=oident EQ tg=qoident LTCOLON tvi=plist0(loc(type_exp), COMMA) GT
    { (x, (tvi, tg)) }

tyci_ax:
| PROOF x=ident BY tg=tactic_core
    { (x, tg) }

(* -------------------------------------------------------------------- *)
(* Operator definitions                                                 *)

pred_tydom:
| ty=loc(type_exp)
   { [ty] }

| tys=plist2(loc(simpl_type_exp), AMP)
   { tys }

| tys=paren(plist2(loc(type_exp), COMMA))
   { tys  }

tyvars_decl:
| LBRACKET tyvars=rlist0(typaram, COMMA) RBRACKET
    { tyvars }

| LBRACKET tyvars=rlist2(tident , empty) RBRACKET
    { List.map (fun x -> (x, [])) tyvars }

op_or_const:
| OP    { `Op    }
| CONST { `Const }

operator:
| locality=locality k=op_or_const st=nosmt tags=bracket(ident*)?
    x=plist1(oident, COMMA) tyvars=tyvars_decl? args=ptybindings_opdecl?
    sty=prefix(COLON, loc(type_exp))? b=seq(prefix(EQ, loc(opbody)), opax?)?

  { let gloc = EcLocation.make $startpos $endpos in
    let sty  = sty |> ofdfl (fun () ->
      mk_loc (b |> omap (loc |- fst) |> odfl gloc) PTunivar) in

    { po_kind     = k;
      po_name     = List.hd x;
      po_aliases  = List.tl x;
      po_tags     = odfl [] tags;
      po_tyvars   = tyvars;
      po_args     = odfl ([], None) args;
      po_def      = opdef_of_opbody sty (omap (unloc |- fst) b);
      po_ax       = obind snd b;
      po_nosmt    = st;
      po_locality = locality; } }

| locality=locality k=op_or_const st=nosmt tags=bracket(ident*)?
    x=plist1(oident, COMMA) tyvars=tyvars_decl? args=ptybindings_opdecl?
    COLON LBRACE sty=loc(type_exp) PIPE reft=form RBRACE AS rname=ident

  { { po_kind     = k;
      po_name     = List.hd x;
      po_aliases  = List.tl x;
      po_tags     = odfl [] tags;
      po_tyvars   = tyvars;
      po_args     = odfl ([], None) args;
      po_def      = opdef_of_opbody sty (Some (`Reft (rname, reft)));
      po_ax       = None;
      po_nosmt    = st;
      po_locality = locality; } }

opbody:
| f=form   { `Form f  }
| bs=opbr+ { `Case bs }

opax:
| AXIOMATIZED BY x=ident { x }

opbr:
| WITH ptn=plist1(opcase, COMMA) IMPL e=expr
   { { pop_patterns = ptn; pop_body = e; } }

%inline opcase:
| x=ident EQ p=opptn
    { { pop_name = x; pop_pattern = p; } }

%inline opptn:
| p=mcptn(sbinop)
    { p }

| p=paren(mcptn(binop))
    { p }

%public mcptn(BOP):
| c=qoident tvi=tvars_app? ps=bdident*
    { PPApp ((c, tvi), ps) }

| LBRACKET tvi=tvars_app? RBRACKET {
    let loc = EcLocation.make $startpos $endpos in
    PPApp ((pqsymb_of_symb loc EcCoreLib.s_nil, tvi), [])
  }

| op=loc(uniop) tvi=tvars_app?
    { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), []) }

| op=loc(uniop) tvi=tvars_app? x=bdident
    { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), [x]) }

| x1=bdident op=loc(BOP) tvi=tvars_app? x2=bdident
    { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), [x1; x2]) }

| x1=bdident op=loc(ordering_op) tvi=tvars_app? x2=bdident
    { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), [x1; x2]) }

(* -------------------------------------------------------------------- *)
(* Proc operators                                                       *)
procop:
| locality=locality PROC OP x=ident EQ f=loc(fident)
    { { ppo_name = x; ppo_target = f; ppo_locality = locality; } }

(* -------------------------------------------------------------------- *)
(* Predicate definitions                                                *)
predicate:
| locality=locality PRED x=oident
   { { pp_name     = x;
       pp_tyvars   = None;
       pp_def      = PPabstr [];
       pp_locality = locality; } }

| locality=locality PRED x=oident tyvars=tyvars_decl? COLON sty=pred_tydom
   { { pp_name     = x;
       pp_tyvars   = tyvars;
       pp_def      = PPabstr sty;
       pp_locality = locality; } }

| locality=locality PRED x=oident tyvars=tyvars_decl? p=ptybindings? EQ f=form
   { { pp_name     = x;
       pp_tyvars   = tyvars;
       pp_def      = PPconcr (odfl [] p, f);
       pp_locality = locality; } }

| locality=locality INDUCTIVE x=oident tyvars=tyvars_decl? p=ptybindings?
    EQ b=indpred_def

   { { pp_name     = x;
       pp_tyvars   = tyvars;
       pp_def      = PPind (odfl [] p, b);
       pp_locality = locality; } }

indpred_def:
| PIPE? ctors=plist0(ip_ctor_def, PIPE)
| ctors=bracket(plist0(ip_ctor_def, PIPE)) { ctors }

ip_ctor_def:
| x=oident bd=pgtybindings? fs=prefix(OF, plist1(sform, AMP))?
  { { pic_name = x; pic_bds = odfl [] bd; pic_spec = odfl [] fs; } }

(* -------------------------------------------------------------------- *)
(* Notations                                                            *)
nt_binding1:
| x=ident
    { (x, mk_loc (loc x) PTunivar) }

| x=ident COLON ty=loc(type_exp)
    { (x, ty) }

nt_argty:
| ty=loc(type_exp)
    { ([], ty) }

| xs=plist0(ident, COMMA) LONGARROW ty=loc(type_exp)
    { (xs, ty) }

nt_arg1:
| x=ident
    { (x, ([], None)) }

| LPAREN x=ident COLON ty=nt_argty RPAREN
    { (x, snd_map some ty) }

nt_bindings:
| DASHLT bd=plist0(nt_binding1, COMMA) GT
    { bd }

notation:
| locality=loc(locality) NOTATION x=loc(NOP) tv=tyvars_decl? bd=nt_bindings?
    args=nt_arg1* codom=prefix(COLON, loc(type_exp))? EQ body=expr
  { { nt_name  = x;
      nt_tv    = tv;
      nt_bd    = odfl [] bd;
      nt_args  = args;
      nt_codom = ofdfl (fun () -> mk_loc (loc body) PTunivar) codom;
      nt_body  = body;
      nt_local = locality_as_local locality; } }

abrvopt:
| b=boption(MINUS) x=ident {
    match unloc x with
    | "printing" -> (not b, `Printing)
    | _ ->
        parse_error x.pl_loc
          (Some ("invalid option: " ^ (unloc x)))
  }

abrvopts:
| opts=bracket(abrvopt+) { opts }

abbreviation:
| locality=loc(locality) ABBREV opts=abrvopts? x=oident tyvars=tyvars_decl?
    args=ptybindings_decl? sty=prefix(COLON, loc(type_exp))? EQ b=expr

  { let sty  = sty |> ofdfl (fun () -> mk_loc (loc b) PTunivar) in

    { ab_name  = x;
      ab_tv    = tyvars;
      ab_args  = odfl [] args;
      ab_def   = (sty, b);
      ab_opts  = odfl [] opts;
      ab_local = locality_as_local locality; } }

(* -------------------------------------------------------------------- *)
mempred_binding:
  | TICKBRACE u=uident+ RBRACE { PT_MemPred u }

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

lemma_decl:
| x=ident
  tyvars=tyvars_decl?
  predvars=mempred_binding?
  pd=pgtybindings?
  COLON f=form
    { (x, tyvars, predvars, pd, f) }

%public nosmt:
| NOSMT { true  }
| empty { false }

axiom_tc:
| /* empty */       { PLemma None }
| BY bracket(empty) { PLemma (Some None) }
| BY t=tactics      { PLemma (Some (Some t)) }

axiom:
| l=locality AXIOM ids=bracket(ident+)? o=nosmt d=lemma_decl
    { mk_axiom ~locality:l ~nosmt:o d (PAxiom (odfl [] ids)) }

| l=locality LEMMA o=nosmt d=lemma_decl ao=axiom_tc
    { mk_axiom ~locality:l ~nosmt:o d ao }

| l=locality  EQUIV x=ident pd=pgtybindings? COLON p=loc( equiv_body(none)) ao=axiom_tc
| l=locality  HOARE x=ident pd=pgtybindings? COLON p=loc( hoare_body(none)) ao=axiom_tc
| l=locality EHOARE x=ident pd=pgtybindings? COLON p=loc( ehoare_body(none)) ao=axiom_tc
| l=locality PHOARE x=ident pd=pgtybindings? COLON p=loc(phoare_body(none)) ao=axiom_tc
    { mk_axiom ~locality:l (x, None, None, pd, p) ao }

proofend:
| QED      { `Qed   }
| ADMITTED { `Admit }
| ABORT    { `Abort }

(* -------------------------------------------------------------------- *)
(* Theory interactive manipulation                                      *)

theory_clear_item1:
| l=genqident(STAR) {
    match List.rev (fst (unloc l)) with
    | [] -> None
    | x :: xs -> Some (mk_loc (loc l) (List.rev xs, x))
  }

theory_clear_items:
| xs=theory_clear_item1* { xs }

theory_open:
| loca=is_local b=boption(ABSTRACT) THEORY x=uident
    { (loca, b, x) }

theory_close:
| END xs=bracket(theory_clear_items)? x=uident
    { (odfl [] xs, x) }

theory_clear:
| CLEAR xs=bracket(theory_clear_items)
    { xs }

section_open  : SECTION     x=option(uident) { x }
section_close : END SECTION x=option(uident) { x }

import_flag:
| IMPORT { `Import }
| EXPORT { `Export }

theory_require:
| nm=prefix(FROM, uident)? REQUIRE ip=import_flag? x=theory_require_1+
    { (nm, x, ip) }

theory_require_1:
| x=uident
    { (x, None) }

| LBRACKET x=uident AS y=uident RBRACKET
    { (x, Some y) }

theory_import: IMPORT xs=uqident* { xs }
theory_export: EXPORT xs=uqident* { xs }

module_import:
| IMPORT VAR xs=loc(mod_qident)+ { xs }

(* -------------------------------------------------------------------- *)
(* Instruction matching                                                 *)

%inline im_block_start:
| LBRACE  { Without_anchor }
| LPBRACE { With_anchor    }

%inline im_block_end:
| RBRACE  { Without_anchor }
| RPBRACE { With_anchor    }

%public im_block:
| a1=im_block_start s=im_stmt a2=im_block_end
   { ((a1, a2), s) }

im_stmt_atomic:
| UNDERSCORE
   { IM_Any }

| LARROW
| UNDERSCORE LARROW UNDERSCORE
   { IM_Assign }

| LESAMPLE
| UNDERSCORE LESAMPLE UNDERSCORE
   { IM_Sample }

| LEAT
| UNDERSCORE LEAT UNDERSCORE
   { IM_Call }

| IF
   { IM_If (None, None) }

| WHILE
   { IM_While None }

| n=lident
   { IM_Named (n, None) }

im_stmt_base_r(S):
| x=im_stmt_atomic S
   { x }

| IF x1=im_block
   { IM_If (Some x1, None) }

| IF x1=im_block ELSE x2=im_block
   { IM_If (Some x1, Some x2) }

| WHILE x=im_block
   { IM_While (Some x) }

| x=paren(im_stmt) S
   { IM_Parens x }

| s=im_repeat_mark x=im_stmt_base_r(S)
   { IM_Repeat (s, x) }

im_stmt_base(S):
| x=im_stmt_base_r(S)
   { x }

| xs=plist2(im_stmt_base_r(empty), PIPE) S
   { IM_Choice xs }

im_stmt_seq_r:
| x=im_stmt_base(empty)
   { [x] }

| x=im_stmt_base(SEMICOLON) xs=im_stmt_seq_r
   { x :: xs }

%inline im_stmt_seq_named:
| x=im_stmt_seq_r AS n=lident
   { IM_Named (n, Some (IM_Seq x)) }

im_stmt_seq:
| x=im_stmt_seq_named
   { [x] }

| xs=im_stmt_seq_r
   { xs }

| x=im_stmt_seq_named SEMICOLON xs=im_stmt_seq
    { x :: xs }

%inline im_stmt:
| xs=im_stmt_seq?
   { IM_Seq (odfl [] xs) }

im_base_repeat_mark:
| x=im_range NOT
   { IM_R_Repeat x }

| x=im_range_question QUESTION
   { IM_R_May x }

im_repeat_mark:
| b=boption(TILD) x=im_base_repeat_mark
   { (not b, x) }

im_range:
| empty
   { (None, None) }

| i=word
   { (Some i, Some i) }

| LBRACKET n=word DOTDOT m=word RBRACKET
   { (Some n, Some m) }

| LBRACKET n=word DOTDOT RBRACKET
   { (Some n, None) }

| LBRACKET DOTDOT m=word RBRACKET
   { (None, Some m) }

im_range_question:
| empty
  { None }

| i=word
  { Some i }


(* -------------------------------------------------------------------- *)
tcd_toptactic:
| t=toptactic {
    let l1 = $startpos(t) in
    let l2 = $endpos(t) in

    if l1.L.pos_fname <> l2.L.pos_fname then
      parse_error
        (EcLocation.make $startpos $endpos)
        (Some "<dump> command cannot span multiple files");
    ((l1.L.pos_fname, (l1.L.pos_cnum, l2.L.pos_cnum)), t)
  }

tactic_dump:
| DUMP aout=STRING wd=word? t=paren(tcd_toptactic)
  {  let infos = {
      tcd_source = fst t;
      tcd_width  = wd;
      tcd_output = aout;
    } in (infos, snd t) }

(* -------------------------------------------------------------------- *)
(* Printing                                                             *)
print:
|             qs=qoident         { Pr_any  qs            }
| STAR        qs=qoident         { Pr_any  qs            }
| TYPE        qs=qident          { Pr_ty   qs            }
| OP          qs=qoident         { Pr_op   qs            }
| THEORY      qs=qident          { Pr_th   qs            }
| PRED        qs=qoident         { Pr_pr   qs            }
| AXIOM       qs=qident          { Pr_ax   qs            }
| LEMMA       qs=qident          { Pr_ax   qs            }
| MODULE      qs=qident          { Pr_mod  qs            }
| MODULE TYPE qs=qident          { Pr_mty  qs            }
| GLOB        qs=loc(mod_qident) { Pr_glob qs            }
| GOAL        n=sword            { Pr_goal n             }
| REWRITE     qs=qident          { Pr_db   (`Rewrite qs) }
| SOLVE       qs=ident           { Pr_db   (`Solve   qs) }


%public smt_info:
| li=smt_info1* { SMT.mk_smt_option li}

smt_info1:
| t=word
    { `MAXLEMMAS (Some t) }

| TIMEOUT EQ t=word
    { `TIMEOUT t }

| p=prover_kind
    { `PROVER p }

| PROVER EQ p=prover_kind
    { `PROVER p }

| DUMP IN EQ file=loc(STRING)
    { `DUMPIN file }

| x=lident po=prefix(EQ, smt_option)?
    { SMT.mk_pi_option x po }

prover_kind1:
| l=loc(STRING)       { `Only   , l }
| PLUS  l=loc(STRING) { `Include, l }
| MINUS l=loc(STRING) { `Exclude, l }

prover_kind:
| LBRACKET lp=prover_kind1* RBRACKET { lp }

%inline smt_option:
| n=word        { `INT n    }
| d=dbhint      { `DBHINT d }
| p=prover_kind { `PROVER p }

gprover_info:
| PROVER x=smt_info { x }

| TIMEOUT t=word
    { { empty_pprover with pprov_timeout = Some t; } }

| TIMEOUT STAR t=word
    { { empty_pprover with pprov_cpufactor = Some t; } }

addrw:
| local=is_local HINT REWRITE p=lqident COLON l=lqident*
    { (local, p, l) }

hint:
| local=is_local HINT EXACT base=lident? COLON l=qident*
    { { ht_local = local; ht_prio  = 0;
        ht_base  = base ; ht_names = l; } }

| local=is_local HINT SOLVE i=word base=lident? COLON l=qident*
    { { ht_local = local; ht_prio  = i;
        ht_base  = base ; ht_names = l; } }

(* -------------------------------------------------------------------- *)
(* User reduction                                                       *)
reduction:
| HINT SIMPLIFY opt=bracket(user_red_option*)? xs=plist1(user_red_info, COMMA)
    { (odfl [] opt, xs) }

user_red_info:
| x=qident i=prefix(AT, word)?
    { ([x], i) }

| xs=paren(plist1(qident, COMMA)) i=prefix(AT, word)?
    { (xs, i) }

user_red_option:
| x=lident {
    match unloc x with
    | "reduce" -> `Delta
    | "eqtrue" -> `EqTrue
    | _ ->
        parse_error x.pl_loc
          (Some ("invalid option: " ^ (unloc x)))
  }

(* -------------------------------------------------------------------- *)
(* Search pattern                                                       *)
%inline search: x=sform_h { x }

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

global_action:
| theory_open      { GthOpen      $1 }
| theory_close     { GthClose     $1 }
| theory_require   { GthRequire   $1 }
| theory_import    { GthImport    $1 }
| theory_export    { GthExport    $1 }
| theory_clone     { GthClone     $1 }
| theory_clear     { GthClear     $1 }
| module_import    { GModImport   $1 }
| section_open     { GsctOpen     $1 }
| section_close    { GsctClose    $1 }
| mod_def_or_decl  { Gmodule      $1 }
| sig_def          { Ginterface   $1 }
| typedecl         { Gtype        $1 }
| typeclass        { Gtypeclass   $1 }
| tycinstance      { Gtycinstance $1 }
| operator         { Goperator    $1 }
| procop           { Gprocop      $1 }
| predicate        { Gpredicate   $1 }
| notation         { Gnotation    $1 }
| abbreviation     { Gabbrev      $1 }
| reduction        { Greduction   $1 }
| axiom            { Gaxiom       $1 }
| tactics_or_prf   { Gtactics     $1 }
| tactic_dump      { Gtcdump      $1 }
| x=loc(realize)   { Grealize     x  }
| gprover_info     { Gprover_info $1 }
| addrw            { Gaddrw       $1 }
| hint             { Ghint        $1 }
| x=loc(proofend)  { Gsave        x  }
| PRINT p=print    { Gprint       p  }
| SEARCH x=search+ { Gsearch      x  }
| LOCATE x=qident  { Glocate      x  }
| WHY3 x=STRING    { GdumpWhy3    x  }

| PRAGMA       x=pragma { Gpragma x }
| PRAGMA PLUS  x=pragma { Goption (x, `Bool true ) }
| PRAGMA MINUS x=pragma { Goption (x, `Bool false) }

| PRAGMA x=pragma EQ i=sword { Goption (x, `Int i) }

pragma_r:
| x=plist1(_lident, COLON)
    { String.concat ":" x }

| u=_uident COLON x=plist1(_lident, COLON)
    { String.concat ":" (u :: x) }

pragma:
| x=loc(pragma_r) { x }

stop:
| EOF { }
| DROP DOT { }

global:
| db=debug_global? fail=boption(FAIL) g=global_action ep=FINAL
  { let lc = EcLocation.make $startpos ep in
    { gl_action = EcLocation.mk_loc lc g;
      gl_fail   = fail;
      gl_debug  = db; } }

debug_global:
| TIME  { `Timed }
| DEBUG { `Break }

prog_r:
| g=global { P_Prog ([g], false) }
| stop     { P_Prog ([ ], true ) }

| UNDO d=word FINAL
   { P_Undo d }

| EXIT FINAL
   { P_Exit }

| error
   { parse_error (EcLocation.make $startpos $endpos) None }

prog:
| x=loc(prog_r) { x }
