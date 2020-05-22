(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

%{
  open EcUtils
  open EcLocation
  open EcParsetree

  module L  = Lexing
  module BI = EcBigInt

  let parse_error loc msg = raise (ParseError (loc, msg))

  let pqsymb_of_psymb (x : psymbol) : pqsymbol =
    mk_loc x.pl_loc ([], x.pl_desc)

  let pqsymb_of_symb loc x : pqsymbol =
    mk_loc loc ([], x)

  let mk_tydecl (tyvars, name) body = {
    pty_name   = name;
    pty_tyvars = tyvars;
    pty_body   = body;
  }

  let opdef_of_opbody ty b =
    match b with
    | None            -> PO_abstr ty
    | Some (`Expr e ) -> PO_concr (ty, e)
    | Some (`Case bs) -> PO_case  (ty, bs)
    | Some (`Reft rt) -> PO_reft  (ty, rt)

  let lqident_of_fident (nm, name) =
    let module E = struct exception Invalid end in

    let nm =
      let for1 (x, args) =
        if args <> None then raise E.Invalid else unloc x
      in
        List.map for1 nm
    in
      try Some (nm, unloc name) with E.Invalid -> None

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

  let mk_simplify l =
    if l = [] then
      { pbeta  = true; pzeta  = true;
        piota  = true; peta   = true;
        plogic = true; pdelta = None;
        pmodpath = true; puser = true; }
    else
      let doarg acc = function
        | `Delta l ->
            if   l = [] || acc.pdelta = None
            then { acc with pdelta = None }
            else { acc with pdelta = Some (oget acc.pdelta @ l) }

        | `Zeta    -> { acc with pzeta    = true }
        | `Iota    -> { acc with piota    = true }
        | `Beta    -> { acc with pbeta    = true }
        | `Eta     -> { acc with peta     = true }
        | `Logic   -> { acc with plogic   = true }
        | `ModPath -> { acc with pmodpath = true }
        | `User    -> { acc with puser    = true }
      in
        List.fold_left doarg
          { pbeta  = false; pzeta  = false;
            piota  = false; peta   = false;
            plogic = false; pdelta = Some [];
            pmodpath = false; puser = false; } l

  let simplify_red = [`Zeta; `Iota; `Beta; `Eta; `Logic; `ModPath; `User]

  let mk_pterm explicit head args =
    { fp_mode = if explicit then `Explicit else `Implicit;
      fp_head = head;
      fp_args = args; }

  let mk_core_tactic t = { pt_core = t; pt_intros = []; }

  let mk_tactic_of_tactics ts =
    mk_core_tactic (mk_loc ts.pl_loc (Pseq (unloc ts)))

  let mk_topmod ~local (header, body) =
    {
      ptm_header = header;
      ptm_body   = body;
      ptm_local  = local;
    }

  let mk_rel_pterm info =
    odfl ({ fp_mode = `Implicit;
            fp_head = FPCut (None, None);
            fp_args = []; }) info

  (* ------------------------------------------------------------------ *)
  type prover =
    [ `Exclude | `Include | `Only] * psymbol

  type pi = [
    | `DBHINT of pdbhint
    | `INT    of int
    | `PROVER of prover list
  ]

  type smt = [
    | `ALL
    | `ITERATE
    | `QUORUM         of int
    | `MAXLEMMAS      of int option
    | `MAXPROVERS     of int
    | `PROVER         of prover list
    | `TIMEOUT        of int
    | `UNWANTEDLEMMAS of EcParsetree.pdbhint
    | `WANTEDLEMMAS   of EcParsetree.pdbhint
    | `VERBOSE        of int option
    | `VERSION        of [ `Full | `Lazy ]
    | `SELECTED
  ]

  module SMT : sig
    val mk_pi_option  : psymbol -> pi option -> smt
    val mk_smt_option : smt list -> pprover_infos
  end = struct
    let option_matching tomatch =
      let match_option = String.option_matching tomatch in
      fun s ->
        match match_option s.pl_desc with
        | [m] -> mk_loc s.pl_loc m
        | []  -> parse_error s.pl_loc (Some ("unknown option: " ^ (unloc s)))
        | ls  ->
          let msg =
            Printf.sprintf
              "option `%s` is ambiguous. matching ones are: `%s`"
              (unloc s) (String.concat ", " ls)
          in parse_error s.pl_loc (Some msg)

    let option_matching =
       option_matching
         [ "all"           ;
           "quorum"        ;
           "timeout"       ;
           "maxprovers"    ;
           "maxlemmas"     ;
           "wantedlemmas"  ;
           "unwantedlemmas";
           "prover"        ;
           "verbose"       ;
           "lazy"          ;
           "full"          ;
           "iterate"       ;
           "selected"      ]

    let as_int = function
      | None          -> `None
      | Some (`INT n) -> `Some n
      | Some _        -> `Error

    let as_dbhint = function
      | None             -> `None
      | Some (`DBHINT d) -> `Some d
      | Some _           -> `Error

    let as_prover = function
      | None             -> `None
      | Some (`PROVER p) -> `Some p
      | Some _           -> `Error

    let get_error ~optional s name =
      let msg =
        Printf.sprintf
          "`%s`: %s`%s` option expected" (unloc s)
          (if optional then "optional " else "")
          name
      in parse_error s.pl_loc (Some msg)

    let get_as (name, getter) s o =
      match getter o with
      | `Some v -> v
      | `None
      | `Error  -> get_error ~optional:false s name

    let get_opt_as (name, getter) s o =
      match getter o with
      | `Some v -> Some v
      | `None   -> None
      | `Error  -> get_error ~optional:true s name

    let get_as_none s o =
      if EcUtils.is_some o then
          let msg = Printf.sprintf "`%s`: no option expected" (unloc s) in
          parse_error s.pl_loc (Some msg)

    let mk_pi_option (s : psymbol) (o : pi option) : smt =
      let s = option_matching s in

      match unloc s with
      | "timeout"        -> `TIMEOUT        (get_as     ("int"   , as_int) s o)
      | "quorum"         -> `QUORUM         (get_as     ("int"   , as_int) s o)
      | "maxprovers"     -> `MAXPROVERS     (get_as     ("int"   , as_int) s o)
      | "maxlemmas"      -> `MAXLEMMAS      (get_opt_as ("int"   , as_int) s o)
      | "wantedlemmas"   -> `WANTEDLEMMAS   (get_as     ("dbhint", as_dbhint) s o)
      | "unwantedlemmas" -> `UNWANTEDLEMMAS (get_as     ("dbhint", as_dbhint) s o)
      | "prover"         -> `PROVER         (get_as     ("prover", as_prover) s o)
      | "verbose"        -> `VERBOSE        (get_opt_as ("int"   , as_int) s o)
      | "lazy"           -> `VERSION        (get_as_none s o; `Lazy)
      | "full"           -> `VERSION        (get_as_none s o; `Full)
      | "all"            -> get_as_none s o; (`ALL)
      | "iterate"        -> get_as_none s o; (`ITERATE)
      | "selected"       -> get_as_none s o; (`SELECTED)
      | _                ->  assert false

    let mk_smt_option (os : smt list) =
      let mprovers = ref None in
      let timeout  = ref None in
      let pnames   = ref None in
      let quorum   = ref None in
      let all      = ref None in
      let mlemmas  = ref None in
      let wanted   = ref None in
      let unwanted = ref None in
      let verbose  = ref None in
      let version  = ref None in
      let iterate  = ref None in
      let selected = ref None in

      let is_universal p = unloc p = "" || unloc p = "!" in

      let ok_use_only pp p =
        if pp.pp_add_rm <> [] then
          let msg = "use-only elements must come at beginning" in
          parse_error (loc p) (Some msg)
        else if pp.pp_use_only <> [] && is_universal p then
          let msg = "cannot add universal to non-empty use-only" in
          parse_error (loc p) (Some msg)
        else
          match pp.pp_use_only with
          | [q] ->
              if is_universal q then
                let msg = "use-only part is already universal" in
                parse_error (loc p) (Some msg)
          | _ -> () in

      let add_prover (k, p) =
        let r  = odfl empty_pprover_list !pnames in
        let pr =
          match k with
          | `Only ->
	            ok_use_only r p; { r with pp_use_only = p :: r.pp_use_only }
          | `Include -> { r with pp_add_rm = (`Include, p) :: r.pp_add_rm }
          | `Exclude -> { r with pp_add_rm = (`Exclude, p) :: r.pp_add_rm }

        in pnames := Some pr in

      let do1 o  =
        match o with
        | `ALL              -> all      := Some true
        | `QUORUM         n -> quorum   := Some n
        | `TIMEOUT        n -> timeout  := Some n
        | `MAXPROVERS     n -> mprovers := Some n
        | `MAXLEMMAS      n -> mlemmas  := Some n
        | `WANTEDLEMMAS   d -> wanted   := Some d
        | `UNWANTEDLEMMAS d -> unwanted := Some d
        | `VERBOSE        v -> verbose  := Some v
        | `VERSION        v -> version  := Some v
        | `ITERATE          -> iterate  := Some true
        | `PROVER         p -> List.iter add_prover p
        | `SELECTED         -> selected := Some true
      in

      List.iter do1 os;

      oiter
        (fun r -> pnames := Some { r with pp_add_rm = List.rev r.pp_add_rm })
        !pnames;

      { pprov_max       = !mprovers;
        pprov_timeout   = !timeout;
        pprov_cpufactor =  None;
        pprov_names     = !pnames;
        pprov_quorum    = !quorum;
        pprov_verbose   = !verbose;
        pprov_version   = !version;
        plem_all        = !all;
        plem_max        = !mlemmas;
        plem_iterate    = !iterate;
        plem_wanted     = !wanted;
        plem_unwanted   = !unwanted;
        plem_selected   = !selected;
      }
  end
%}

%token <EcSymbols.symbol> LIDENT
%token <EcSymbols.symbol> UIDENT
%token <EcSymbols.symbol> TIDENT
%token <EcSymbols.symbol> MIDENT
%token <EcSymbols.symbol> PUNIOP
%token <EcSymbols.symbol> PBINOP
%token <EcSymbols.symbol> PNUMOP

%token <EcBigInt.zint> UINT
%token <EcBigInt.zint * (int * EcBigInt.zint)> DECIMAL
%token <string> STRING

(* Tokens *)
%token ANDA AND (* asym : &&, sym : /\ *)
%token ORA  OR  (* asym : ||, sym : \/ *)

%token<[`Raw|`Eq]> RING
%token<[`Raw|`Eq]> FIELD


%token ABORT
%token ABBREV
%token ABSTRACT
%token ADMIT
%token ADMITTED
%token ALGNORM
%token ALIAS
%token AMP
%token APPLY
%token AS
%token ASSERT
%token ASSUMPTION
%token ASYNC
%token AT
%token AUTO
%token AXIOM
%token AXIOMATIZED
%token BACKS
%token BETA
%token BY
%token BYEQUIV
%token BYPHOARE
%token BYPR
%token CALL
%token CASE
%token CBV
%token CEQ
%token CFOLD
%token CHANGE
%token CLASS
%token CLEAR
%token CLONE
%token COLON
%token COLONTILD
%token COMMA
%token CONGR
%token CONSEQ
%token CONST
%token CUT
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
%token DUMP
%token EAGER
%token ECALL
%token ELIF
%token ELIM
%token ELSE
%token END
%token EOF
%token EQ
%token EQUIV
%token ETA
%token EXACT
%token EXFALSO
%token EXIST
%token EXLIM
%token EXPECT
%token EXPORT
%token FEL
%token FINAL
%token FIRST
%token FISSION
%token FOR
%token FORALL
%token FROM
%token FUN
%token FUSION
%token FWDS
%token GLOB
%token GOAL
%token HAT
%token HAVE
%token HINT
%token HOARE
%token IDTAC
%token IF
%token IFF
%token IMPL
%token IMPORT
%token IMPOSSIBLE
%token IN
%token INCLUDE
%token INDUCTIVE
%token INLINE
%token INTERLEAVE
%token INSTANCE
%token IOTA
%token KILL
%token LARROW
%token LAST
%token LBRACE
%token LBRACKET
%token LEAT
%token LEFT
%token LEMMA
%token LESAMPLE
%token LET
%token LLARROW
%token LOCAL
%token LOGIC
%token LONGARROW
%token LOSSLESS
%token LPAREN
%token LPBRACE
%token MINUS
%token MODPATH
%token MODULE
%token MOVE
%token NE
%token NOSMT
%token NOT
%token NOTATION
%token OF
%token OP
%token PCENT
%token PHOARE
%token PIPE
%token PIPEGT
%token PIPEPIPEGT
%token PLUS
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
%token RARROW
%token RBOOL
%token RBRACE
%token RBRACKET
%token RCONDF
%token RCONDT
%token REALIZE
%token REFLEX
%token REMOVE
%token RENAME
%token REPLACE
%token REQUIRE
%token RES
%token RETURN
%token REWRITE
%token RIGHT
%token RND
%token RPAREN
%token RPBRACE
%token RRARROW
%token RWNORMAL
%token SEARCH
%token SECTION
%token SELF
%token SEMICOLON
%token SEQ
%token SHARP
%token SHARPPIPE
%token SIM
%token SIMPLIFY
%token SKIP
%token SLASH
%token SLASHEQ
%token SLASHGT
%token SLASHSHARP
%token SLASHSLASHGT
%token SLASHTILDEQ
%token SLASHSLASH
%token SLASHSLASHEQ
%token SLASHSLASHTILDEQ
%token SLASHSLASHSHARP
%token SMT
%token SOLVE
%token SP
%token SPLIT
%token SPLITWHILE
%token STAR
%token STRICT
%token SUBST
%token SUFF
%token SWAP
%token SYMMETRY
%token THEN
%token THEORY
%token TICKPIPE
%token TILD
%token TIME
%token TIMEOUT
%token TOP
%token TRANSITIVITY
%token TRIVIAL
%token TRY
%token TYPE
%token UNDERSCORE
%token UNDO
%token UNROLL
%token VAR
%token WHILE
%token WHY3
%token WITH
%token WLOG
%token WP
%token ZETA
%token <string> NOP LOP1 ROP1 LOP2 ROP2 LOP3 ROP3 LOP4 ROP4 NUMOP
%token LTCOLON DASHLT GT LT GE LE LTSTARGT LTLTSTARGT LTSTARGTGT

%nonassoc prec_below_comma
%nonassoc COMMA ELSE

%nonassoc IN
%nonassoc prec_below_IMPL
%right    IMPL LEAT
%nonassoc IFF
%right    ORA  OR
%right    ANDA AND
%nonassoc NOT

%nonassoc EQ NE

%nonassoc prec_below_order

%left  NOP
%left  GT LT GE LE
%left  LOP1
%right ROP1
%right QUESTION
%left  LOP2 MINUS PLUS
%right ROP2
%right RARROW
%left  LOP3 STAR SLASH
%right ROP3
%left  LOP4 AT AMP HAT
%right ROP4

%nonassoc LBRACE

%right SEMICOLON

%nonassoc prec_tactic

%type <EcParsetree.global> global
%type <EcParsetree.prog  > prog

%type <unit> is_uniop
%type <unit> is_binop
%type <unit> is_numop

%start prog global is_uniop is_binop is_numop
%%

(* -------------------------------------------------------------------- *)
_lident:
| x=LIDENT   { x }
| ABORT      { "abort"      }
| ADMITTED   { "admitted"   }
| ASYNC      { "async"      }
| DUMP       { "dump"       }
| EXPECT     { "expect"     }
| FIRST      { "first"      }
| INTERLEAVE { "interleave" }
| LAST       { "last"       }
| LEFT       { "left"       }
| RIGHT      { "right"      }
| SOLVE      { "solve"      }
| STRICT     { "strict"     }
| WLOG       { "wlog"       }
| EXLIM      { "exlim"      }
| ECALL      { "ecall"      }
| FROM       { "from"       }

| x=RING  { match x with `Eq -> "ringeq"  | `Raw -> "ring"  }
| x=FIELD { match x with `Eq -> "fieldeq" | `Raw -> "field" }

%inline _uident:
| x=UIDENT { x }

%inline _tident:
| x=TIDENT { x }

%inline _mident:
| x=MIDENT { x }

%inline lident: x=loc(_lident) { x }
%inline uident: x=loc(_uident) { x }
%inline tident: x=loc(_tident) { x }
%inline mident: x=loc(_mident) { x }

%inline _ident:
| x=_lident { x }
| x=_uident { x }

%inline ident:
| x=loc(_ident) { x }

%inline uint: n=UINT { n }

%inline word:
| n=loc(UINT) {
    try  BI.to_int (unloc n)
    with BI.Overflow ->
      parse_error (loc n) (Some "literal is too large")
  }

%inline sword:
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

genqident(X):
| x=loc(_genqident(X)) { x }


(* -------------------------------------------------------------------- *)
%inline  qident: x=genqident(_ident ) { x }
%inline uqident: x=genqident(_uident) { x }
%inline lqident: x=genqident(_lident) { x }

(* -------------------------------------------------------------------- *)
%inline _boident:
| x=_lident { x }
| x=_uident { x }
| x=PUNIOP  { x }
| x=PBINOP  { x }
| x=PNUMOP  { x }

| x=loc(STRING)   {
    if not (EcCoreLib.is_mixfix_op (unloc x)) then
      parse_error x.pl_loc (Some "invalid mixfix operator");
    unloc x
  }

%inline _oident:
| x=_boident      { x }
| x=paren(PUNIOP) { x }


%inline boident: x=loc(_boident) { x }
%inline  oident: x=loc( _oident) { x }

qoident:
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


%inline mod_qident:
| x=rlist1(mod_ident1, DOT)
    { x }

| _l=TOP DOT x=rlist1(mod_ident1, DOT)
    { (mk_loc (EcLocation.make $startpos(_l) $endpos(_l))
         EcCoreLib.i_top, None) :: x }

| _l=SELF DOT x=rlist1(mod_ident1, DOT)
    { (mk_loc (EcLocation.make $startpos(_l) $endpos(_l))
         EcCoreLib.i_self, None) :: x }

fident:
| nm=mod_qident DOT x=lident { (nm, x) }
| x=lident { ([], x) }

(* -------------------------------------------------------------------- *)
%inline ordering_op:
| GT { ">"  }
| LT { "<"  }
| GE { ">=" }
| LE { "<=" }

%inline uniop:
| x=NOP { Printf.sprintf "[%s]" x }
| NOT   { "[!]" }
| PLUS  { "[+]" }
| MINUS { "[-]" }

%inline sbinop:
| EQ    { "="   }
| PLUS  { "+"   }
| MINUS { "-"   }
| STAR  { "*"   }
| SLASH { "/"   }
| AT    { "@"   }
| OR    { "\\/" }
| ORA   { "||"  }
| AND   { "/\\" }
| ANDA  { "&&"  }
| AMP   { "&"   }
| HAT   { "^"   }

| x=LOP1 | x=LOP2 | x=LOP3 | x=LOP4
| x=ROP1 | x=ROP2 | x=ROP3 | x=ROP4
| x=NOP
    { x }

%inline binop:
| op=sbinop { op    }
| IMPL      { "=>"  }
| IFF       { "<=>" }

%inline numop:
| op=NUMOP { op }

(* -------------------------------------------------------------------- *)
is_binop: binop EOF {}
is_uniop: uniop EOF {}
is_numop: numop EOF {}

(* -------------------------------------------------------------------- *)
pside_:
| x=_lident { Printf.sprintf "&%s" x }
| x=word    { Printf.sprintf "&%d" x }

pside:
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

%inline lpattern:
| x=loc(lpattern_u) { x }

(* -------------------------------------------------------------------- *)
(* Expressions: program expression, real expression                     *)

tyvar_byname1:
| x=tident EQ ty=loc(type_exp) { (x, ty) }

tyvar_annot:
| lt = plist1(loc(type_exp), COMMA) { TVIunamed lt }
| lt = plist1(tyvar_byname1, COMMA) { TVInamed lt }

%inline tvars_app:
| LTCOLON k=loc(tyvar_annot) GT { k }

(* -------------------------------------------------------------------- *)
%inline sexpr: x=loc(sexpr_u) { x }
%inline  expr: x=loc( expr_u) { x }

sexpr_u:
| e=sexpr PCENT p=uqident
   { PEscope (p, e) }

| e=sexpr p=loc(prefix(PCENT, lident))
   { let { pl_loc = lc; pl_desc = p; } = p in
     if unloc p = "r" then
       let id =
         PEident (mk_loc lc EcCoreLib.s_real_of_int, None)
       in PEapp (mk_loc lc id, [e])
     else begin
       if unloc p <> "top" then
         parse_error p.pl_loc (Some "invalid scope name");
       PEscope (pqsymb_of_symb p.pl_loc "<top>", e)
     end }

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

| e1=expr op=loc(NE) ti=tvars_app? e2=expr
    { peapp_symb op.pl_loc "[!]" None
      [ mk_loc op.pl_loc (peapp_symb op.pl_loc "=" ti [e1; e2])] }

| e1=expr op=loc(binop) ti=tvars_app? e2=expr
    { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| c=expr QUESTION e1=expr COLON e2=expr %prec LOP2
   { PEif (c, e1, e2) }

| IF c=expr THEN e1=expr ELSE e2=expr
   { PEif (c, e1, e2) }

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

%inline ptybinding1:
| LPAREN bds=plist1(pty_varty, COMMA) RPAREN
    { bds }

| x=loc(bdident)
   { [[unloc x], mk_loc (loc x) PTunivar] }

ptybindings:
| x=ptybinding1+
    { List.flatten x }

| x=bdident+ COLON ty=loc(type_exp)
   { [x, ty] }

ptybindings_decl:
| x=ptybinding1+
    { List.flatten x }

(* -------------------------------------------------------------------- *)
(* Formulas                                                             *)

%inline sform_r(P): x=loc(sform_u(P)) { x }
%inline  form_r(P): x=loc( form_u(P)) { x }

%inline sform: x=sform_r(none) { x }
%inline  form: x=form_r (none) { x }

%inline sform_h: x=loc(sform_u(hole)) { x }
%inline  form_h: x=loc( form_u(hole)) { x }

%inline hole: UNDERSCORE { PFhole }
%inline none: IMPOSSIBLE { assert false }

qident_or_res_or_glob:
| x=qident   { GVvar x }
| x=loc(RES) { GVvar (mk_loc x.pl_loc ([], "res")) }
| GLOB mp=loc(mod_qident) { GVglob mp }

pfpos:
| i=sword
    { `Index i }

| f=bracket(form_h) off=pfoffset?
    { `Match (f, off) }

pfoffset:
| PLUS  w=word {  w }
| MINUS w=word { -w }

pffilter:
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

sform_u(P):
| x=P
   { x }

| f=sform_r(P) PCENT p=uqident
   { PFscope (p, f) }

| f=sform_r(P) p=loc(prefix(PCENT, lident))
   { let { pl_loc = lc; pl_desc = p; } = p in
     if unloc p = "r" then
       let id =
         PFident (mk_loc lc EcCoreLib.s_real_of_int, None)
       in PFapp (mk_loc lc id, [f])
     else begin
       if unloc p <> "top" then
         parse_error p.pl_loc (Some "invalid scope name");
       PFscope (pqsymb_of_symb p.pl_loc "<top>", f)
     end }

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

| e1=form_r(P) op=loc(NE) ti=tvars_app? e2=form_r(P)
    { pfapp_symb op.pl_loc "[!]" None
      [ mk_loc op.pl_loc (pfapp_symb op.pl_loc "=" ti [e1; e2])] }

| e1=form_r(P) op=loc(binop) ti=tvars_app? e2=form_r(P)
    { pfapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

| c=form_r(P) QUESTION e1=form_r(P) COLON e2=form_r(P) %prec LOP2
    { PFif (c, e1, e2) }

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

hoare_bd_cmp :
| LE { EcFol.FHle }
| EQ { EcFol.FHeq }
| GE { EcFol.FHge }

hoare_body(P):
  mp=loc(fident) COLON pre=form_r(P) LONGARROW post=form_r(P)
    { PFhoareF (pre, mp, post) }

phoare_body(P):
  LBRACKET mp=loc(fident) COLON
    pre=form_r(P) LONGARROW post=form_r(P)
  RBRACKET
    cmp=hoare_bd_cmp bd=sform_r(P)
  { PFBDhoareF (pre, mp, post, cmp, bd) }

equiv_body(P):
  mp1=loc(fident) TILD mp2=loc(fident)
  COLON pre=form_r(P) LONGARROW post=form_r(P)
    { PFequivF (pre, (mp1, mp2), post) }

eager_body(P):
| s1=stmt COMMA  mp1=loc(fident) TILD mp2=loc(fident) COMMA s2=stmt
    COLON pre=form_r(P) LONGARROW post=form_r(P)
    { PFeagerF (pre, (s1, mp1, mp2,s2), post) }

pgtybinding1:
| x=ptybinding1
    { List.map (fun (xs, ty) -> (xs, PGTY_Type ty)) x }

| LPAREN x=uident LTCOLON mi=mod_type_restr RPAREN
    { [[mk_loc (loc x) (Some x)], PGTY_ModTy mi] }

| pn=mident
    { [[mk_loc (loc pn) (Some pn)], PGTY_Mem] }

pgtybindings:
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

type_exp:
| ty=simpl_type_exp                          { ty }
| ty=plist2(loc(simpl_type_exp), STAR)       { PTtuple ty }
| ty1=loc(type_exp) RARROW ty2=loc(type_exp) { PTfun(ty1,ty2) }

(* -------------------------------------------------------------------- *)
(* Parameter declarations                                              *)

typed_vars:
| xs=ident+ COLON ty=loc(type_exp)
   { List.map (fun v -> (v, ty)) xs }

| xs=ident+
    { List.map (fun v -> (v, mk_loc v.pl_loc PTunivar)) xs }

param_decl:
| LPAREN aout=plist0(typed_vars, COMMA) RPAREN
    { Fparams_exp (List.flatten aout )}

| LPAREN UNDERSCORE COLON ty=loc(type_exp) RPAREN
    { Fparams_imp ty }

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

if_expr:
| IF c=paren(expr) b=block el=if_else_expr
   { PSif ((c, b), fst el, snd el) }

if_else_expr:
|  /* empty */ { ([], []) }
| ELSE b=block { ([],  b) }

| ELIF e=paren(expr) b=block el=if_else_expr
    { ((e, b) :: fst el, snd el) }

block:
| i=loc(base_instr) SEMICOLON
    { [i] }

| stmt=brace(stmt)
   { stmt }

stmt: aout=loc(instr)* { aout }

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
    { { pfd_name     = x;
        pfd_tyargs   = pd;
        pfd_tyresult = odfl (mk_loc x.pl_loc PTunivar) ty;
        pfd_uses     = (true, None); }
    }

include_proc:
| PLUS? xs=plist1(lident,COMMA) { `Include_proc xs }
| MINUS xs=plist1(lident,COMMA) { `Exclude_proc xs }
mod_item:
| v=var_decl
    { Pst_var v }

| MODULE x=uident c=mod_cast? EQ m=loc(mod_body)
    { Pst_mod (x, odfl [] c, m) }

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

| INCLUDE m=loc(mod_qident) xs=bracket(include_proc)?
    { Pst_maliases (m,xs) }


(* -------------------------------------------------------------------- *)
(* Modules                                                              *)

mod_body:
| m=mod_qident
    { Pm_ident m }

| LBRACE stt=loc(mod_item)* RBRACE
    { Pm_struct stt }

mod_def:
| MODULE header=mod_header c=mod_cast? EQ body=loc(mod_body)
  { let header = match c with None -> header | Some c ->  Pmh_cast(header,c) in
    header, body }

mod_header:
| x=uident                  { Pmh_ident x }
| mh=loc(mod_header_params) { Pmh_params mh }
| LPAREN mh=mod_header c=mod_cast RPAREN { Pmh_cast(mh,c) }

mod_cast:
| COLON c=plist1(uqident,COMMA) { c }

mod_header_params:
| mh=mod_header p=mod_params { mh,p }

top_mod_def:
| LOCAL x=mod_def { mk_topmod ~local:true  x }
| /*-*/ x=mod_def { mk_topmod ~local:false x }

top_mod_decl:
| DECLARE MODULE x=uident COLON t=mod_type_restr
    { { ptmd_name = x; ptmd_modty = t; } }

mod_params:
| LPAREN a=plist1(sig_param, COMMA) RPAREN  { a }

(* -------------------------------------------------------------------- *)
(* Modules interfaces                                                   *)

%inline mod_type:
| x = qident { x }

%inline mod_type_restr:
| x = qident
    { (x, []) }

| x = qident LBRACE restr=plist1(loc(mod_qident), COMMA) RBRACE
    { (x, restr) }

sig_def:
| MODULE TYPE x=uident args=sig_params* EQ i=sig_body
    { (x, Pmty_struct { pmsig_params = List.flatten args;
                        pmsig_body   = i; }) }

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
| INCLUDE i=mod_type xs=bracket(include_proc)? qs=brace(qident*)?
   { `Include (i, xs, qs) }
| PROC i=boption(STAR) x=lident pd=param_decl COLON ty=loc(type_exp) qs=brace(qident*)?
    { `FunctionDecl
          { pfd_name     = x;
            pfd_tyargs   = pd;
            pfd_tyresult = ty;
            pfd_uses     = (not i, qs); } }

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
| TYPE td=rlist1(tyd_name, COMMA)
    { List.map (mk_tydecl^~ (PTYD_Abstract [])) td }

| TYPE td=tyd_name LTCOLON tcs=rlist1(qident, COMMA)
    { [mk_tydecl td (PTYD_Abstract tcs)] }

| TYPE td=tyd_name EQ te=loc(type_exp)
    { [mk_tydecl td (PTYD_Alias te)] }

| TYPE td=tyd_name EQ te=record_def
    { [mk_tydecl td (PTYD_Record te)] }

| TYPE td=tyd_name EQ te=datatype_def
    { [mk_tydecl td (PTYD_Datatype te)] }

(* -------------------------------------------------------------------- *)
(* Type classes                                                         *)
typeclass:
| TYPE CLASS x=lident inth=tc_inth? EQ LBRACE body=tc_body RBRACE {
    { ptc_name = x;
      ptc_inth = inth;
      ptc_ops  = fst body;
      ptc_axs  = snd body; }
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
| INSTANCE x=qident
    WITH typ=tyvars_decl? ty=loc(type_exp) ops=tyci_op* axs=tyci_ax*
  {
    { pti_name = x;
      pti_type = (odfl [] typ, ty);
      pti_ops  = ops;
      pti_axs  = axs;
      pti_args = None; }
  }

| INSTANCE x=qident c=uoption(UINT) p=uoption(UINT)
    WITH typ=tyvars_decl? ty=loc(type_exp) ops=tyci_op* axs=tyci_ax*
  {
    { pti_name = x;
      pti_type = (odfl [] typ, ty);
      pti_ops  = ops;
      pti_axs  = axs;
      pti_args = Some (`Ring (c, p)); }
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
| k=op_or_const st=nosmt tags=bracket(ident*)? x=plist1(oident, COMMA)
    tyvars=tyvars_decl? args=ptybindings_decl?
    sty=prefix(COLON, loc(type_exp))? b=seq(prefix(EQ, loc(opbody)), opax?)?

  { let gloc = EcLocation.make $startpos $endpos in
    let sty  = sty |> ofdfl (fun () ->
      mk_loc (b |> omap (loc |- fst) |> odfl gloc) PTunivar) in

    { po_kind    = k;
      po_name    = List.hd x;
      po_aliases = List.tl x;
      po_tags    = odfl [] tags;
      po_tyvars  = tyvars;
      po_args    = odfl [] args;
      po_def     = opdef_of_opbody sty (omap (unloc |- fst) b);
      po_ax      = obind snd b;
      po_nosmt   = st; } }

| k=op_or_const st=nosmt tags=bracket(ident*)? x=plist1(oident, COMMA)
    tyvars=tyvars_decl? args=ptybindings_decl?
    COLON LBRACE sty=loc(type_exp) PIPE reft=form RBRACE AS rname=ident

  { { po_kind    = k;
      po_name    = List.hd x;
      po_aliases = List.tl x;
      po_tags    = odfl [] tags;
      po_tyvars  = tyvars;
      po_args    = odfl [] args;
      po_def     = opdef_of_opbody sty (Some (`Reft (rname, reft)));
      po_ax      = None;
      po_nosmt   = st; } }

opbody:
| e=expr   { `Expr e  }
| bs=opbr+ { `Case bs }

opax:
| AXIOMATIZED BY x=ident { x }

opbr:
| WITH ptn=plist1(opcase, COMMA) IMPL e=expr
   { { pop_patterns = ptn; pop_body = e; } }

%inline opcase:
| x=ident EQ p=opptn(sbinop)
    { { pop_name = x; pop_pattern = p; } }

| x=ident EQ p=paren(opptn(binop))
    { { pop_name = x; pop_pattern = p; } }

opptn(BOP):
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

| x1=bdident op=loc(NE) tvi=tvars_app? x2=bdident
    { PPApp ((pqsymb_of_symb op.pl_loc "[!]", tvi), [x1; x2]) }

| x1=bdident op=loc(BOP) tvi=tvars_app? x2=bdident
    { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), [x1; x2]) }

| x1=bdident op=loc(ordering_op) tvi=tvars_app? x2=bdident
    { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), [x1; x2]) }

(* -------------------------------------------------------------------- *)
(* Predicate definitions                                                *)
predicate:
| PRED x=oident
   { { pp_name   = x;
       pp_tyvars = None;
       pp_def    = PPabstr []; } }

| PRED x=oident tyvars=tyvars_decl? COLON sty=pred_tydom
   { { pp_name   = x;
       pp_tyvars = tyvars;
       pp_def    = PPabstr sty; } }

| PRED x=oident tyvars=tyvars_decl? p=ptybindings? EQ f=form
   { { pp_name   = x;
       pp_tyvars = tyvars;
       pp_def    = PPconcr (odfl [] p, f); } }

| INDUCTIVE x=oident tyvars=tyvars_decl? p=ptybindings?
    EQ b=indpred_def

   { { pp_name   = x;
       pp_tyvars = tyvars;
       pp_def    = PPind (odfl [] p, b) } }

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
| NOTATION x=loc(NOP) tv=tyvars_decl? bd=nt_bindings?
    args=nt_arg1* codom=prefix(COLON, loc(type_exp))? EQ body=expr
  { { nt_name  = x;
      nt_tv    = tv;
      nt_bd    = odfl [] bd;
      nt_args  = args;
      nt_codom = ofdfl (fun () -> mk_loc (loc body) PTunivar) codom;
      nt_body  = body; } }

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
| ABBREV opts=abrvopts? x=oident tyvars=tyvars_decl? args=ptybindings_decl?
    sty=prefix(COLON, loc(type_exp))? EQ b=expr

  { let sty  = sty |> ofdfl (fun () -> mk_loc (loc b) PTunivar) in

    { ab_name = x;
      ab_tv   = tyvars;
      ab_args = odfl [] args;
      ab_def  = (sty, b);
      ab_opts = odfl [] opts; } }

(* -------------------------------------------------------------------- *)
top_decl:
| x=top_mod_decl { PDCL_Module x }

(* -------------------------------------------------------------------- *)
(* Global entries                                                       *)

lemma_decl :
| x=ident tyvars=tyvars_decl? pd=pgtybindings? COLON f=form { x,tyvars,pd,f }

nosmt:
| NOSMT { true  }
| empty { false }

%inline local:
| LOCAL { true  }
| empty { false }

axiom_tc:
| /* empty */       { PILemma }
| BY bracket(empty) { PLemma None }
| BY t=tactics      { PLemma (Some t) }

axiom:
| l=local AXIOM ids=bracket(ident+)? o=nosmt d=lemma_decl
    { mk_axiom ~local:l ~nosmt:o d (PAxiom (odfl [] ids)) }

| l=local LEMMA o=nosmt d=lemma_decl ao=axiom_tc
    { mk_axiom ~local:l ~nosmt:o d ao }

| l=local  EQUIV x=ident pd=pgtybindings? COLON p=loc( equiv_body(none)) ao=axiom_tc
| l=local  HOARE x=ident pd=pgtybindings? COLON p=loc( hoare_body(none)) ao=axiom_tc
| l=local PHOARE x=ident pd=pgtybindings? COLON p=loc(phoare_body(none)) ao=axiom_tc
    { mk_axiom ~local:l (x, None, pd, p) ao }

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
| b=boption(ABSTRACT) THEORY x=uident
    { (b, x) }

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

(* -------------------------------------------------------------------- *)
(* Instruction matching                                                 *)

%inline im_block_start:
| LBRACE  { Without_anchor }
| LPBRACE { With_anchor    }

%inline im_block_end:
| RBRACE  { Without_anchor }
| RPBRACE { With_anchor    }

im_block:
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
(* tactic                                                               *)

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
| pt=gpoterm(form) { pt }

pcutdef1:
| p=qident tvi=tvars_app? args=loc(gpterm_arg)*
    { { ptcd_name = p; ptcd_tys = tvi; ptcd_args = args; } }

pcutdef:
| cd=pcutdef1               { cd }
| LPAREN cd=pcutdef1 RPAREN { cd }

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

| s=rwside r=rwrepeat? o=rwocc? fp=rwpterms
   { RWRw ((s, r, o), fp) }

| s=rwside r=rwrepeat? o=rwocc? SLASH x=sform_h %prec prec_tactic
   { RWDelta ((s, r, o), x); }

| PR s=bracket(rwpr_arg)
   { RWPr s }

| SMT
   { RWSmt (false, SMT.mk_smt_option []) }

| LBRACKET SMT pi=smt_info RBRACKET
   { RWSmt (false, pi) }

| LBRACKET SMT LPAREN dbmap=dbmap1* RPAREN RBRACKET
   { RWSmt (false, SMT.mk_smt_option [`WANTEDLEMMAS dbmap]) }

| AMP f=pterm
   { RWApp f }

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
| empty                           { None, None }
| UNDERSCORE LONGARROW UNDERSCORE { None, None }
| f1=form LONGARROW               { Some f1, None }
| f1=form LONGARROW UNDERSCORE    { Some f1, None }
| f2=form                         { None, Some f2 }
| LONGARROW f2=form               { None, Some f2 }
| UNDERSCORE LONGARROW f2=form    { None, Some f2 }
| f1=form LONGARROW f2=form       { Some f1, Some f2 }


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

while_tac_info:
| inv=sform
    { { wh_inv = inv; wh_vrnt = None; wh_bds = None; } }

| inv=sform vrnt=sform
    { { wh_inv = inv; wh_vrnt = Some vrnt; wh_bds = None; } }

| inv=sform vrnt=sform k=sform eps=sform
    { { wh_inv = inv; wh_vrnt = Some vrnt; wh_bds = Some (k, eps); } }

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

dbhint:
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
| HAVE | CUT { `Have }
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

| ior_(CUT, HAVE) ip=loc(intro_pattern)* CEQ fp=pcutdef
   { Pcutdef (ip, fp) }

| POSE o=rwocc? x=ident xs=ptybindings? CEQ p=form_h %prec prec_below_IMPL
   { Ppose (x, odfl [] xs, o, p) }

| WLOG COLON ids=loc(ipcore_name)* SLASH f=form
   { Pwlog (ids, f) }

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

| LPAREN UNDERSCORE COLON f1=form LONGARROW f2=form RPAREN
    { Double (f1, f2) }

%inline if_option:
| s=option(side)
   { `Head s }

| s=option(side) i1=o_codepos1 i2=o_codepos1 COLON f=sform
   { `Seq (s, (i1, i2), f) }

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

| RCONDT s=side? i=codepos1
    { Prcond (s, true, i) }

| RCONDF s=side? i=codepos1
    { Prcond (s, false, i) }

| IF opt=if_option
    { Pcond opt }

| SWAP info=iplist1(loc(swap_info), COMMA) %prec prec_below_comma
    { Pswap info }

| INTERLEAVE info=loc(interleave_info)
    { Pinterleave info }

| CFOLD s=side? c=codepos NOT n=word
    { Pcfold (s, c, Some n) }

| CFOLD s=side? c=codepos
    { Pcfold (s, c, None) }

| RND s=side? info=rnd_info
    { Prnd (s, info) }

| INLINE s=side? u=inlineopt? o=occurences? f=plist1(loc(fident), empty)
    { Pinline (`ByName (s, u, (f, o))) }

| INLINE s=side? u=inlineopt? p=codepos
    { Pinline (`CodePos (s, u, p)) }

| INLINE s=side? u=inlineopt? STAR
    { Pinline (`All (s, u)) }

| KILL s=side? o=codepos
    { Pkill (s, o, Some 1) }

| KILL s=side? o=codepos NOT n=word
    { Pkill (s, o, Some n) }

| KILL s=side? o=codepos NOT STAR
    { Pkill (s, o, None) }

| ALIAS s=side? o=codepos
    { Palias (s, o, None) }

| ALIAS s=side? o=codepos WITH x=lident
    { Palias (s, o, Some x) }

| ALIAS s=side? o=codepos x=lident EQ e=expr
    { Pset (s, o, false, x,e) }

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

| BYEQUIV eq=bracket(byequivopt)? info=gpterm(conseq)?
    { Pbydeno (`Equiv, (mk_rel_pterm info, odfl true eq, None)) }

| BYEQUIV eq=bracket(byequivopt)? info=gpterm(conseq)? COLON bad1=sform
    { Pbydeno (`Equiv, (mk_rel_pterm info, odfl true eq, Some bad1)) }

| CONSEQ cq=cqoptions?
    { Pconseq (odfl [] cq, (None, None, None)) }

| CONSEQ cq=cqoptions? info1=gpterm(conseq_bd)
    { Pconseq (odfl [] cq, (Some info1, None, None)) }

| CONSEQ cq=cqoptions? info1=gpterm(conseq_bd) info2=gpterm(conseq_bd) UNDERSCORE?
    { Pconseq (odfl [] cq, (Some info1, Some info2, None)) }

| CONSEQ cq=cqoptions? info1=gpterm(conseq_bd) UNDERSCORE info3=gpterm(conseq_bd)
    { Pconseq (odfl [] cq, (Some info1, None, Some info3)) }

| CONSEQ cq=cqoptions?
    info1=gpterm(conseq_bd)
    info2=gpterm(conseq_bd)
    info3=gpterm(conseq_bd)
      { Pconseq (odfl [] cq, (Some info1,Some info2,Some info3)) }

| CONSEQ cq=cqoptions? UNDERSCORE info2=gpterm(conseq_bd) UNDERSCORE?
    { Pconseq (odfl [] cq, (None,Some info2, None)) }

| CONSEQ cq=cqoptions? UNDERSCORE UNDERSCORE info3=gpterm(conseq_bd)
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

(* DEBUG *)
| DEBUG
    { Pdebug }

%inline tactic_core:
| x=loc(tactic_core_r) { x }

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

tactic:
| t=tactic_ip %prec prec_below_IMPL
    { t }

| t1=tactic_ip ORA t2=tactic
    { let loc = EcLocation.make $startpos $endpos in
        mk_core_tactic (mk_loc loc (Por (t1, t2))) }

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

tactics:
| t=tactic %prec SEMICOLON { [t] }
| t=tactic SEMICOLON ts=subtactics { t :: ts }

tactics0:
| ts=tactics   { Pseq ts }
| x=loc(empty) { Pseq [mk_core_tactic (mk_loc x.pl_loc (Pidtac None))] }

toptactic:
| PLUS  t=tactics { t }
| STAR  t=tactics { t }
| MINUS t=tactics { t }
|       t=tactics { t }

tactics_or_prf:
| t=toptactic  { `Actual t    }
| p=proof      { `Proof  p    }

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

proofmode1:
| b=boption(MINUS) pm=loc(proofmodename) { (pm, not b) }

proofmodename:
| STRICT { `Strict }

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
(* Theory cloning                                                       *)

theory_clone:
| local=boption(LOCAL) CLONE options=clone_opts?
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
    | (xs, `Named x ) -> `Named (mk_loc l.pl_loc (xs, x))
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
| EQ     { `Alias }
| LARROW { `Inline }

cltyparams:
| empty { [] }
| x=tident { [x] }
| xs=paren(plist1(tident, COMMA)) { xs }

clone_override:
| TYPE ps=cltyparams x=qident EQ t=loc(type_exp)
   { (x, PTHO_Type (ps, t, `Alias)) }

| TYPE ps=cltyparams x=qident LARROW t=loc(type_exp)
   { (x, PTHO_Type (ps, t, `Inline)) }

| OP st=nosmt x=qoident tyvars=bracket(tident*)? COLON sty=loc(type_exp) mode=opclmode e=expr
   { let ov = {
       opov_nosmt  = st;
       opov_tyvars = tyvars;
       opov_args   = [];
       opov_retty  = sty;
       opov_body   = e;
     } in
       (x, PTHO_Op (ov, mode)) }

| OP st=nosmt x=qoident tyvars=bracket(tident*)? mode=loc(opclmode) e=expr
   { let ov = {
       opov_nosmt  = st;
       opov_tyvars = tyvars;
       opov_args   = [];
       opov_retty  = mk_loc mode.pl_loc PTunivar;
       opov_body   = e;
     } in
       (x, PTHO_Op (ov, unloc mode)) }

| OP st=nosmt x=qoident tyvars=bracket(tident*)? p=ptybindings mode=loc(opclmode) e=expr
   { let ov = {
       opov_nosmt  = st;
       opov_tyvars = tyvars;
       opov_args   = p;
       opov_retty  = mk_loc mode.pl_loc PTunivar;
       opov_body   = e;
     } in
       (x, PTHO_Op (ov, unloc mode)) }

| PRED x=qoident tyvars=bracket(tident*)? p=ptybindings mode=loc(opclmode) f=form
   { let ov = {
       prov_tyvars = tyvars;
       prov_args   = p;
       prov_body   = f;
     } in
       (x, PTHO_Pred (ov, unloc mode)) }

| PRED x=qoident tyvars=bracket(tident*)? mode=loc(opclmode) f=form
   { let ov = {
       prov_tyvars = tyvars;
       prov_args   = [];
       prov_body   = f;
     } in
       (x, PTHO_Pred (ov, unloc mode)) }

| THEORY x=uqident LARROW y=uqident
   { (x, PTHO_Theory y) }

realize:
| REALIZE x=qident
    {  { pr_name = x; pr_proof = None; } }

| REALIZE x=qident BY t=tactics
    {  { pr_name = x; pr_proof = Some (Some t); } }

| REALIZE x=qident BY bracket(empty)
    {  { pr_name = x; pr_proof = Some None; } }

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


smt_info:
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
| local=iboption(LOCAL) HINT REWRITE p=lqident COLON l=lqident*
    { (local, p, l) }

hint:
| local=iboption(LOCAL) HINT EXACT base=lident? COLON l=qident*
    { { ht_local = local; ht_prio  = 0;
        ht_base  = base ; ht_names = l; } }

| local=iboption(LOCAL) HINT SOLVE i=word base=lident? COLON l=qident*
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

| xs=paren(plist1(qident, COMMA)) i=prefix(AT, sword)?
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
| section_open     { GsctOpen     $1 }
| section_close    { GsctClose    $1 }
| top_decl         { Gdeclare     $1 }
| top_mod_def      { Gmodule      $1 }
| sig_def          { Ginterface   $1 }
| typedecl         { Gtype        $1 }
| typeclass        { Gtypeclass   $1 }
| tycinstance      { Gtycinstance $1 }
| operator         { Goperator    $1 }
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
| tm=boption(TIME) g=loc(global_action) FINAL
  { { gl_action = g; gl_timed = tm; } }

prog_r:
| g=global { P_Prog ([g], false) }
| stop     { P_Prog ([ ], true ) }

| UNDO d=word FINAL
   { P_Undo d }

| error
   { parse_error (EcLocation.make $startpos $endpos) None }

prog:
| x=loc(prog_r) { x }

(* -------------------------------------------------------------------- *)
%inline plist0(X, S):
| aout=separated_list(S, X) { aout }

iplist1_r(X, S):
| x=X { [x] }
| xs=iplist1_r(X, S) S x=X { x :: xs }

%inline iplist1(X, S):
| xs=iplist1_r(X, S) { List.rev xs }

%inline plist1(X, S):
| aout=separated_nonempty_list(S, X) { aout }

%inline plist2(X, S):
| x=X S xs=plist1(X, S) { x :: xs }

%inline list2(X):
| x=X xs=X+ { x :: xs }

%inline empty:
| /**/ { () }

(* -------------------------------------------------------------------- *)
__rlist1(X, S):                         (* left-recursive *)
| x=X { [x] }
| xs=__rlist1(X, S) S x=X { x :: xs }

%inline rlist0(X, S):
| /* empty */     { [] }
| xs=rlist1(X, S) { xs }

%inline rlist1(X, S):
| xs=__rlist1(X, S) { List.rev xs }

%inline rlist2(X, S):
| xs=__rlist1(X, S) S x=X { List.rev (x :: xs) }

(* -------------------------------------------------------------------- *)
%inline paren(X):
| LPAREN x=X RPAREN { x }

%inline brace(X):
| LBRACE x=X RBRACE { x }

%inline bracket(X):
| LBRACKET x=X RBRACKET { x }

(* -------------------------------------------------------------------- *)
%inline seq(X, Y):
| x=X y=Y { (x, y) }

%inline prefix(S, X):
| S x=X { x }

%inline postfix(X, S):
| x=X S { x }

%inline sep(S1, X, S2):
| x=S1 X y=S2 { (x, y) }

%inline either(X, Y):
| X {}
| Y {}

(* -------------------------------------------------------------------- *)
or3(X, Y, Z):
| x=X { `Or13 x }
| y=Y { `Or23 y }
| z=Z { `Or33 z }

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X {
    { pl_desc = x;
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }

(* -------------------------------------------------------------------- *)
%inline iboption(X):
| X { true  }
|   { false }

%inline uoption(X):
| x=X { Some x }
| UNDERSCORE { None }

(* -------------------------------------------------------------------- *)
%inline ior_(X, Y):
| x=X { `Left  x }
| y=Y { `Right y }

(* -------------------------------------------------------------------- *)
%inline ID(X):
| x=X { x }
