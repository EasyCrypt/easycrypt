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

  let mk_tydecl ~locality (tyvars, name) body = {
    pty_name     = name;
    pty_tyvars   = tyvars;
    pty_body     = body;
    pty_locality = locality;
  }

  let opdef_of_opbody ty b =
    match b with
    | None            -> PO_abstr ty
    | Some (`Form f ) -> PO_concr (ty, f)
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

  let mk_axiom  ?(nosmt = false) ~locality (x, ty, pv, vd, f) k =
    { pa_name     = x;
      pa_tyvars   = ty;
      pa_pvars   = pv;
      pa_vars     = vd;
      pa_formula  = f;
      pa_kind     = k;
      pa_nosmt    = nosmt;
      pa_locality = locality; }

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

  let mk_rel_pterm info =
    odfl ({ fp_mode = `Implicit;
            fp_head = FPCut (None, None);
            fp_args = []; }) info

  (* ------------------------------------------------------------------ *)
  let locality_as_local (lc : locality located) =
    match unloc lc with
    | `Global  -> `Global
    | `Local   -> `Local
    | `Declare -> parse_error (loc lc)
                   (Some "cannot mark with 'declare' this kind of objects ")

  let bool_as_local b =
    if b then `Local else `Global
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
    | `DUMPIN         of string located
    | `SELECTED
    | `DEBUG
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
           "dumpin"        ;
           "selected"      ;
           "debug"         ]

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
      | "debug"          -> get_as_none s o; (`DEBUG)
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
      let dumpin   = ref None in
      let selected = ref None in
      let debug    = ref None in

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
        | `DUMPIN         f -> dumpin   := Some f
        | `SELECTED         -> selected := Some true
        | `DEBUG            -> debug    := Some true
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
        plem_dumpin     = !dumpin;
        plem_selected   = !selected;
        psmt_debug      = !debug;
      }
  end
%}

%%

(* -------------------------------------------------------------------- *)
%public %inline plist0(X, S):
| aout=separated_list(S, X) { aout }

iplist1_r(X, S):
| x=X { [x] }
| xs=iplist1_r(X, S) S x=X { x :: xs }

%public %inline iplist1(X, S):
| xs=iplist1_r(X, S) { List.rev xs }

%public %inline plist1(X, S):
| aout=separated_nonempty_list(S, X) { aout }

%public %inline plist2(X, S):
| x=X S xs=plist1(X, S) { x :: xs }

%public %inline list2(X):
| x=X xs=X+ { x :: xs }

%public %inline empty:
| /**/ { () }

(* -------------------------------------------------------------------- *)
__rlist1(X, S):                         (* left-recursive *)
| x=X { [x] }
| xs=__rlist1(X, S) S x=X { x :: xs }

%public %inline rlist0(X, S):
| /* empty */     { [] }
| xs=rlist1(X, S) { xs }

%public %inline rlist1(X, S):
| xs=__rlist1(X, S) { List.rev xs }

%public %inline rlist2(X, S):
| xs=__rlist1(X, S) S x=X { List.rev (x :: xs) }

(* -------------------------------------------------------------------- *)
%public %inline paren(X):
| LPAREN x=X RPAREN { x }

%public %inline brace(X):
| LBRACE x=X RBRACE { x }

%public %inline bracket(X):
| LBRACKET x=X RBRACKET { x }

(* -------------------------------------------------------------------- *)
%public %inline seq(X, Y):
| x=X y=Y { (x, y) }

%public %inline prefix(S, X):
| S x=X { x }

%public %inline postfix(X, S):
| x=X S { x }

%public %inline sep(S1, X, S2):
| x=S1 X y=S2 { (x, y) }

%public %inline either(X, Y):
| X {}
| Y {}

(* -------------------------------------------------------------------- *)
%public or3(X, Y, Z):
| x=X { `Or13 x }
| y=Y { `Or23 y }
| z=Z { `Or33 z }

(* -------------------------------------------------------------------- *)
%public %inline loc(X):
| x=X {
    { pl_desc = x;
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }

(* -------------------------------------------------------------------- *)
%public %inline iboption(X):
| X { true  }
|   { false }

%public %inline uoption(X):
| x=X { Some x }
| UNDERSCORE { None }

(* -------------------------------------------------------------------- *)
%public %inline ID(X):
| x=X { x }
