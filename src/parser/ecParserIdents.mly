%%

(* -------------------------------------------------------------------- *)
%public _lident:
| x=LIDENT   { x }
| ABORT      { "abort"      }
| ADMITTED   { "admitted"   }
| ASYNC      { "async"      }
| DEBUG      { "debug"      }
| DUMP       { "dump"       }
| EXPECT     { "expect"     }
| FIRST      { "first"      }
| GEN        { "gen"        }
| INTERLEAVE { "interleave" }
| LAST       { "last"       }
| LEFT       { "left"       }
| RIGHT      { "right"      }
| SOLVE      { "solve"      }
| WLOG       { "wlog"       }
| EXLIM      { "exlim"      }
| ECALL      { "ecall"      }
| FROM       { "from"       }
| EXIT       { "exit"       }

| x=RING  { match x with `Eq -> "ringeq"  | `Raw -> "ring"  }
| x=FIELD { match x with `Eq -> "fieldeq" | `Raw -> "field" }

%public %inline _uident:
| x=UIDENT { x }

%public %inline _tident:
| x=TIDENT { x }

%public %inline _mident:
| x=MIDENT { x }

%public %inline lident: x=loc(_lident) { x }
%public %inline uident: x=loc(_uident) { x }
%public %inline tident: x=loc(_tident) { x }
%public %inline mident: x=loc(_mident) { x }

%public %inline _ident:
| x=_lident { x }
| x=_uident { x }

%public %inline ident:
| x=loc(_ident) { x }

%public %inline uint: n=UINT { n }

%public %inline word:
| n=loc(UINT) {
    try  BI.to_int (unloc n)
    with BI.Overflow ->
      parse_error (loc n) (Some "literal is too large")
  }

%public %inline sword:
|       n=word {  n }
| MINUS n=word { -n }

(* -------------------------------------------------------------------- *)
%inline namespace:
| nm=rlist1(UIDENT, DOT)
    { nm }

| TOP nm=rlist0(prefix(DOT, UIDENT), empty)
    { EcCoreLib.i_top :: nm }

| SELF nm=rlist0(prefix(DOT, UIDENT), empty)
    { EcCoreLib.i_self :: nm }

_genqident(X):
| x=X { ([], x) }
| xs=namespace DOT x=X { (xs, x) }

%public genqident(X):
| x=loc(_genqident(X)) { x }


(* -------------------------------------------------------------------- *)
%public %inline  qident: x=genqident(_ident ) { x }
%public %inline uqident: x=genqident(_uident) { x }
%public %inline lqident: x=genqident(_lident) { x }

(* -------------------------------------------------------------------- *)
%inline _boident:
| x=_lident { x }
| x=_uident { x }
| x=PUNIOP  { x }
| x=PBINOP  { x }
| x=PNUMOP  { x }
| x=PPSTOP  { x }

| x=loc(STRING)   {
    if not (EcCoreLib.is_mixfix_op (unloc x)) then
      parse_error x.pl_loc (Some "invalid mixfix operator");
    unloc x
  }

%inline _oident:
| x=_boident      { x }
| x=paren(PUNIOP) { x }

%public %inline boident: x=loc(_boident) { x }
%public %inline  oident: x=loc( _oident) { x }

%public qoident:
| x=boident
    { pqsymb_of_psymb x }

| xs=namespace DOT x=oident
| xs=namespace DOT x=loc(NOP) {
    { pl_desc = (xs, unloc x);
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }

(* -------------------------------------------------------------------- *)
mod_ident1:
| x=uident
    { (x, None) }

| x=uident LPAREN args=plist1(loc(mod_qident), COMMA) RPAREN
    { (x, Some args) }


%public %inline mod_qident:
| x=rlist1(mod_ident1, DOT)
    { x }

| _l=TOP DOT x=rlist1(mod_ident1, DOT)
    { (mk_loc (EcLocation.make $startpos(_l) $endpos(_l))
         EcCoreLib.i_top, None) :: x }

| _l=SELF DOT x=rlist1(mod_ident1, DOT)
    { (mk_loc (EcLocation.make $startpos(_l) $endpos(_l))
         EcCoreLib.i_self, None) :: x }

%public %inline fident:
| nm=mod_qident DOT x=lident { (nm, x) }
| x=lident { ([], x) }

%public f_or_mod_ident:
| nm=mod_qident DOT x=lident
    { let fv = mk_loc (EcLocation.make $startpos(nm) $endpos(x)) (nm, x) in
      FM_FunOrVar fv }
| x=lident
    { let fv = mk_loc (EcLocation.make $startpos(x) $endpos(x)) ([], x) in
      FM_FunOrVar fv}
| m=loc(mod_qident) { FM_Mod m }

