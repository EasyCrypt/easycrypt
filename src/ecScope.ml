(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcLocation
open EcPath
open EcParsetree
open EcAst
open EcTypes
open EcDecl
open EcModules
open EcFol
open EcTyping
open EcHiInductive
open EcBigInt.Notations

module Sid  = EcIdent.Sid
module Mid  = EcIdent.Mid
module MSym = EcSymbols.Msym
module BI   = EcBigInt

(* -------------------------------------------------------------------- *)
exception HiScopeError of EcLocation.t option * string

let pp_hi_scope_error fmt exn =
  match exn with
  | HiScopeError (None, s) ->
      Format.fprintf fmt "%s" s

  | HiScopeError (Some loc, s) ->
      Format.fprintf fmt "%s: %s" (EcLocation.tostring loc) s

  | _ -> raise exn

let _ = EcPException.register pp_hi_scope_error

let hierror ?loc fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in

    Format.kfprintf
      (fun _ ->
         Format.pp_print_flush bfmt ();
         raise (HiScopeError (loc, Buffer.contents buf)))
      bfmt fmt

(* -------------------------------------------------------------------- *)
exception ImportError of EcLocation.t option * symbol * exn

let is_import_error = function ImportError _ -> true | _ -> false

let pp_import_error fmt exn =
  match exn with
  | ImportError (None, name, e) ->
      Format.fprintf fmt "In external theory %s [<unknown> location]:@\n%a"
        name EcPException.exn_printer e

  | ImportError (Some l, name, e) when is_import_error e ->
      Format.fprintf fmt "In external theory %s [%s]:@\n%a"
        name (EcLocation.tostring l)
        EcPException.exn_printer e

  | ImportError (Some l, name, e) ->
      Format.fprintf fmt "In external theory %s [%s]:@\n@\n%a"
        name (EcLocation.tostring l)
        EcPException.exn_printer e

  | _ -> raise exn

let _ = EcPException.register pp_import_error

(* -------------------------------------------------------------------- *)
exception TopError of EcLocation.t * exn

let rec toperror_of_exn_r ?gloc exn =
  match exn with
  | TyError    (loc, _, _) -> Some (loc, exn)
  | RcError    (loc, _, _) -> Some (loc, exn)
  | DtError    (loc, _, _) -> Some (loc, exn)
  | ParseError (loc, _)    -> Some (loc, exn)

  | EcHiPredicates.TransPredError (loc, _, _) -> Some (loc, exn)
  | EcHiNotations .NotationError  (loc, _, _) -> Some (loc, exn)

  | EcLexer.LexicalError (loc, _) ->
      Some (odfl (odfl _dummy gloc) loc, exn)

  | EcCoreGoal.TcError { EcCoreGoal.tc_location = None } ->
      Some (odfl _dummy gloc, exn)

  | EcCoreGoal.TcError
      { EcCoreGoal.tc_location = Some { EcCoreGoal.plc_loc = loc } } ->
      let gloc = if EcLocation.isdummy loc then gloc else Some loc in
      Some (odfl _dummy gloc, exn)

  | LocError (loc, e)    -> begin
      let gloc = if EcLocation.isdummy loc then gloc else Some loc in
      match toperror_of_exn_r ?gloc e with
      | None -> Some (loc, e)
      | Some (loc, e) -> Some (loc, e)
    end

  | ImportError _ ->
      Some (odfl _dummy gloc, exn)

  | TopError (loc, e) ->
      let gloc = if EcLocation.isdummy loc then gloc else Some loc in
      toperror_of_exn_r ?gloc e
  | EcSection.SectionError _ ->
    Some (odfl _dummy gloc, exn)
  | HiScopeError (loc, msg) ->
      let gloc =
        match loc with
        | None     -> gloc
        | Some loc -> if EcLocation.isdummy loc then gloc else Some loc
      in
        Some (odfl _dummy gloc, HiScopeError (None, msg))

  | Sys.Break ->
      Some (odfl _dummy gloc, HiScopeError (None, "interrupted"))

  | _ -> None

let toperror_of_exn ?gloc exn =
  match toperror_of_exn_r ?gloc exn with
  | Some (loc, exn) -> TopError (loc, exn)
  | None            -> exn

let pp_toperror fmt loc exn =
  Format.fprintf fmt "%s: %a"
    (EcLocation.tostring loc)
    EcPException.exn_printer exn

let () =
  let pp fmt exn =
    match exn with
    | TopError (loc, exn) -> pp_toperror fmt loc exn
    | _ -> raise exn
  in
    EcPException.register pp

(* -------------------------------------------------------------------- *)
type goption = ..

module type IOptions = sig
  type oid
  type options

  type action = { for_loading : goption -> goption; }

  val register     : ?action:action -> goption -> oid
  val freeze       : unit -> options
  val get          : options -> oid -> goption
  val set          : options -> oid -> goption -> options
  val for_loading  : options -> options
  val for_subscope : options -> options
end

(* -------------------------------------------------------------------- *)
module GenOptions : IOptions = struct
  type action  = { for_loading : goption -> goption; }
  type oid     = EcUid.uid
  type options = (action * goption) EcUid.Muid.t

  let options : options ref =
    ref EcUid.Muid.empty

  let identity = { for_loading = (fun x -> x); }

  let register ?(action = identity) goption =
    let oid = EcUid.unique () in
    options := EcUid.Muid.add oid (action, goption) !options; oid

  let freeze () =
    !options

  let get (options : options) (oid : oid) =
    snd (oget (EcUid.Muid.find_opt oid options))

  let set (options : options) (oid : oid) (goption : goption) =
    EcUid.Muid.change (fun k -> Some (fst (oget k), goption)) oid options

  let for_loading options =
    EcUid.Muid.map (fun (act, exn) -> act, act.for_loading exn) options

  let for_subscope options =
    options
end

(* -------------------------------------------------------------------- *)
module Check_mode = struct
  type mode = [`Off | `On | `Forced]

  type goption += Check of mode

  let oid =
    let for_loading = function
      | Check `Off    -> Check `Off
      | Check `On     -> Check `Off
      | Check `Forced -> Check `Forced
      | exn           -> exn
    in GenOptions.register ~action:({ GenOptions.for_loading }) (Check `On)

  let check options =
    match GenOptions.get options oid with
    | Check `On     -> true
    | Check `Forced -> true
    | Check `Off    -> false
    | _ -> true

  let set_checkproof options b =
    match GenOptions.get options oid with
    | Check `On  when not b -> GenOptions.set options oid (Check `Off)
    | Check `Off when     b -> GenOptions.set options oid (Check `On )
    | _ -> options

  let set_fullcheck options =
    GenOptions.set options oid (Check `Forced)
end

(* -------------------------------------------------------------------- *)
module Prover_info = struct
  type goption += PI of EcProvers.prover_infos

  let oid = GenOptions.register (PI EcProvers.dft_prover_infos)

  let set options pi =
    GenOptions.set options oid (PI pi)

  let get options =
    match GenOptions.get options oid with
    | PI pi -> pi
    | _     -> assert false
end

(* -------------------------------------------------------------------- *)
module KnownFlags = struct
  let implicits = "implicits"
  let oldip     = "oldip"
  let redlogic  = "redlogic"
  let und_delta = "und_delta"

  let flags = [
    (implicits, false);
    (oldip    , false);
    (redlogic , true );
    (und_delta, false);
  ]
end

exception UnknownFlag of string

module Flags : sig
  open GenOptions

  val get : options -> string -> bool
  val set : options -> string -> bool -> options
end = struct
  type flags    = bool Mstr.t
  type goption += Flags of flags

  let asflags = function Flags m -> m | _ -> assert false

  let oid =
    let default = Mstr.of_list KnownFlags.flags in
    let for_loading = function
      | Flags _ -> Flags default
      | exn -> exn
    in GenOptions.register ~action:{ GenOptions.for_loading } (Flags default)

  let get options name =
    let flags = asflags (GenOptions.get options oid) in
    oget ~exn:(UnknownFlag name) (Mstr.find_opt name flags)

  let set options name value =
    let flags = asflags (GenOptions.get options oid) in
    let flags =
      Mstr.change (fun x ->
        ignore (oget ~exn:(UnknownFlag name) x : bool);
        Some value)
      name flags in

    GenOptions.set options oid (Flags flags)
end

(* -------------------------------------------------------------------- *)
type proof_uc = {
  puc_active : (proof_auc * (proof_ctxt option)) option;
  puc_cont   : proof_ctxt list * (EcSection.scenv option);
  puc_init   : EcSection.scenv;
}

and proof_auc = {
  puc_name    : symbol option;
  puc_started : bool;
  puc_jdg     : proof_state;
  puc_flags   : pucflags;
  puc_crt     : EcDecl.axiom;
}

and proof_ctxt =
  (symbol option * EcDecl.axiom) * EcPath.path * EcSection.scenv

and proof_state =
  PSNoCheck | PSCheck of EcCoreGoal.proof

and pucflags = {
  puc_smt : bool;
  puc_local      : bool;
}

(* -------------------------------------------------------------------- *)
type docentity =
  | ItemDoc   of string list * docitem
  | SubDoc    of (string list * docitem) * docentity list

and docitem =
  mode * itemkind * string * string list

and itemkind = [`Type | `Operator | `Axiom | `Lemma | `ModuleType | `Module | `Theory]

and mode = [`Abstract | `Specific]

(* -------------------------------------------------------------------- *)
type required_info = {
  rqd_name      : symbol;
  rqd_namespace : EcLoader.namespace option;
  rqd_kind      : EcLoader.kind;
  rqd_digest    : Digest.t;
  rqd_direct    : bool;
}

type required = required_info list

type prelude = {
  pr_env      : EcEnv.env;
  pr_required : required;
}

type thloaded = EcEnv.Theory.compiled_theory

type scope = {
  sc_name     : (symbol * EcTheory.thmode);
  sc_env      : EcSection.scenv;
  sc_top      : scope option;
  sc_prelude  : ([`Frozen | `InPrelude] * prelude);
  sc_loaded   : (thloaded * required) Msym.t;
  sc_required : required;
  sc_clears   : path list;
  sc_pr_uc    : proof_uc option;
  sc_options  : GenOptions.options;
}

(* -------------------------------------------------------------------- *)
let get_gdocstrings (_ : scope) : string list = []
let get_ldocentities (_ : scope) : docentity list = []

(* -------------------------------------------------------------------- *)
let empty (gstate : EcGState.gstate) =
  let env = EcEnv.initial gstate in
  { sc_name       = (EcPath.basename (EcEnv.root env), `Concrete);
    sc_env        = EcSection.initial env;
    sc_top        = None;
    sc_prelude    = (`InPrelude, { pr_env = env; pr_required = []; });
    sc_loaded     = Msym.empty;
    sc_required   = [];
    sc_clears     = [];
    sc_pr_uc      = None;
    sc_options    = GenOptions.freeze (); }

(* -------------------------------------------------------------------- *)
let env (scope : scope) =
  EcSection.env scope.sc_env

(* -------------------------------------------------------------------- *)
let gstate (scope : scope) =
  EcEnv.gstate (env scope)

(* -------------------------------------------------------------------- *)
let name (scope : scope) =
  scope.sc_name

(* -------------------------------------------------------------------- *)
let path (scope : scope) =
  EcEnv.root (env scope)

(* -------------------------------------------------------------------- *)
let attop (scope : scope) =
  scope.sc_top = None

(* -------------------------------------------------------------------- *)
let freeze (scope : scope) =
  match scope.sc_prelude with
  | `Frozen   , _  -> assert false
  | `InPrelude, pr -> { scope with sc_prelude = (`Frozen, pr) }

(* -------------------------------------------------------------------- *)
let goal (scope : scope) =
  scope.sc_pr_uc |> obind (fun x -> omap fst x.puc_active)

(* -------------------------------------------------------------------- *)
let xgoal (scope : scope) =
  scope.sc_pr_uc

(* -------------------------------------------------------------------- *)
let dump_why3 (scope : scope) (filename : string) =
  try  EcSmt.dump_why3 (env scope) filename
  with
  | Sys_error msg ->
      hierror "cannot dump to `%s`: system error: %s"
        filename msg
  | Unix.Unix_error (e, _, _) ->
      hierror "cannot dump to `%s`: system error: %s"
        filename (Unix.error_message e)

(* -------------------------------------------------------------------- *)
type topmode = [`InProof | `InActiveProof | `InTop]

let check_state (mode : topmode) action (scope : scope) =
  match mode with
  | `InProof when scope.sc_pr_uc = None ->
      hierror "cannot process [%s] outside a proof script" action

  | `InActiveProof when scope.sc_pr_uc = None ->
      hierror "cannot process [%s] outside a proof script" action

  | `InTop when scope.sc_pr_uc <> None ->
      hierror "cannot process [%s] inside a proof script" action

  | _ -> ()

(* -------------------------------------------------------------------- *)
let notify (scope : scope) (lvl : EcGState.loglevel) =
  EcEnv.notify (env scope) lvl

(* -------------------------------------------------------------------- *)
module Options = struct
  let get scope name =
    Flags.get scope.sc_options name

  let set scope name value =
    { scope with sc_options =
        Flags.set scope.sc_options name value }

  let get_implicits scope =
    get scope KnownFlags.implicits

  let set_implicits scope value =
    set scope KnownFlags.implicits value

  let get_oldip scope =
    get scope KnownFlags.oldip

  let set_oldip scope value =
    set scope KnownFlags.oldip value

  let get_redlogic scope =
    get scope KnownFlags.redlogic

  let set_redlogic scope value =
    set scope KnownFlags.redlogic value

  let get_und_delta scope =
    get scope KnownFlags.und_delta

  let set_und_delta scope value =
    set scope KnownFlags.und_delta value
end

(* -------------------------------------------------------------------- *)
let for_loading (scope : scope) =
  let pr  = snd (scope.sc_prelude) in
  let env = EcEnv.copy pr.pr_env in
  let lg  = EcGState.loglevel (EcEnv.gstate env) in

  EcGState.set_loglevel
    (EcGState.max_loglevel `Warning lg)
    (EcEnv.gstate env);

  { sc_name       = (EcPath.basename (EcEnv.root pr.pr_env), `Concrete);
    sc_env        = EcSection.initial env;
    sc_top        = None;
    sc_prelude    = scope.sc_prelude;
    sc_loaded     = scope.sc_loaded;
    sc_required   = pr.pr_required;
    sc_clears     = [];
    sc_pr_uc      = None;
    sc_options    = GenOptions.for_loading scope.sc_options;
  }

(* -------------------------------------------------------------------- *)
let subscope (scope : scope) (mode : EcTheory.thmode) (name : symbol) lc =
  let env = EcSection.enter_theory name lc mode scope.sc_env in

  { sc_name       = (name, mode);
    sc_env        = env;
    sc_top        = Some scope;
    sc_prelude    = scope.sc_prelude;
    sc_loaded     = scope.sc_loaded;
    sc_required   = scope.sc_required;
    sc_clears     = [];
    sc_pr_uc      = None;
    sc_options    = GenOptions.for_subscope scope.sc_options; }

(* -------------------------------------------------------------------- *)
module Prover = struct
  let all_provers () =
    List.map
      (fun p -> p.EcProvers.pr_name)
      (EcProvers.known ~evicted:false)

  let check_prover_name { pl_desc = name; pl_loc = loc } =
    if not (EcProvers.is_prover_known name) then
      hierror ~loc "Unknown prover %s" name;
    name

  (* -------------------------------------------------------------------- *)
  let process_dbhint env db =
    let add hints x =
      let nf kind p =
        hierror
          ~loc:p.pl_loc "cannot find %s `%s'"
          (match kind with `Lemma -> "lemma" | `Theory -> "theory")
          (string_of_qsymbol (unloc p))
      in

      let addm hints hflag p =
        match EcEnv.Theory.lookup_opt (unloc p) env with
        | None -> nf `Theory p
        | Some (p, _) -> EcProvers.Hints.addm p hflag hints

      and add1 hints hflag p =
        match EcEnv.Ax.lookup_opt (unloc p) env with
        | None -> nf `Lemma p
        | Some (p, _) -> EcProvers.Hints.add1 p hflag hints
      in

      match x.pht_kind with
      | `Theory -> addm hints x.pht_flag x.pht_name
      | `Lemma  -> add1 hints x.pht_flag x.pht_name

    in
    let hints = EcProvers.Hints.empty in
    let hints = List.fold_left add hints db in
    hints

  (* -------------------------------------------------------------------- *)
  type smt_options = {
    po_timeout    : int option;
    po_cpufactor  : int option;
    po_nprovers   : int option;
    po_provers    : string list option * (include_exclude * string) list;
    po_quorum     : int option;
    po_verbose    : int option;
    pl_all        : bool option;
    pl_max        : int option;
    pl_wanted     : EcProvers.hints option;
    pl_unwanted   : EcProvers.hints option;
    pl_dumpin     : string located option;
    pl_selected   : bool option;
    gn_debug      : bool option;
  }

  (* -------------------------------------------------------------------- *)
  let empty_options = {
    po_timeout   = None;
    po_cpufactor = None;
    po_nprovers  = None;
    po_provers   = (None, []);
    po_quorum    = None;
    po_verbose   = None;
    pl_all       = None;
    pl_max       = None;
    pl_wanted    = None;
    pl_unwanted  = None;
    pl_dumpin    = None;
    pl_selected  = None;
    gn_debug     = None;
  }

  (* -------------------------------------------------------------------- *)
  let process_prover_option env ppr =
    let provers =
      match ppr.pprov_names with
      | None -> None, []
      | Some pl ->
        let do_uo uo s =
          match s.pl_desc with
          | "!" -> all_provers ()
          | ""  -> []
          | _   ->
            let x = check_prover_name s in
            if List.exists ((=) x) uo then uo else x :: uo in
        let uo =
          if pl.pp_use_only = [] then None
          else Some (List.fold_left do_uo [] pl.pp_use_only) in
        let do_ar (k,s) = k, check_prover_name s in
        uo, List.map do_ar pl.pp_add_rm in
    let verbose = omap (odfl 1) ppr.pprov_verbose in
    {
      po_timeout   = ppr.pprov_timeout;
      po_cpufactor = ppr.pprov_cpufactor;
      po_nprovers  = ppr.pprov_max;
      po_provers   = provers;
      po_quorum    = ppr.pprov_quorum;
      po_verbose   = verbose;
      pl_all       = ppr.plem_all;
      pl_max       =
        begin match ppr.plem_max, ppr.plem_wanted with
        | Some i, _      -> Some (odfl max_int i)
        | None  , None   -> None
        | None  , Some _ -> Some 0
        end;
      pl_wanted    = omap (process_dbhint env) ppr.plem_wanted;
      pl_unwanted  = omap (process_dbhint env) ppr.plem_unwanted;
      pl_dumpin    = ppr.plem_dumpin;
      pl_selected  = ppr.plem_selected;
      gn_debug     = ppr.psmt_debug;
    }

  (* -------------------------------------------------------------------- *)
  let mk_prover_info_from_dft (dft : EcProvers.prover_infos)
      (options : smt_options) : EcProvers.prover_infos =
    let open EcProvers in

    let gn_debug     = odfl dft.gn_debug options.gn_debug in
    let pr_maxprocs  = odfl dft.pr_maxprocs options.po_nprovers in
    let pr_timelimit = max 0 (odfl dft.pr_timelimit options.po_timeout) in
    let pr_cpufactor = max 0 (odfl dft.pr_cpufactor options.po_cpufactor) in
    let pr_verbose   = max 0 (odfl dft.pr_verbose options.po_verbose) in
    let pr_all       = odfl dft.pr_all options.pl_all in
    let pr_max       = odfl dft.pr_max options.pl_max in
    let pr_wanted    = odfl dft.pr_wanted options.pl_wanted in
    let pr_unwanted  = odfl dft.pr_unwanted options.pl_unwanted in
    let pr_selected  = odfl dft.pr_selected options.pl_selected in
    let pr_quorum    = max 1 (odfl dft.pr_quorum options.po_quorum) in
    let pr_dumpin    = options.pl_dumpin in
    let pr_provers   =
      let l = odfl dft.pr_provers (fst options.po_provers) in
      let do_ar l (k, p) =
        match k with
        | `Exclude -> List.remove_all l p
        | `Include -> if List.exists ((=) p) l then l else p::l
      in List.fold_left do_ar l (snd options.po_provers) in

    { pr_maxprocs; pr_provers ; pr_timelimit; pr_cpufactor;
      pr_verbose ; pr_all     ; pr_max      ;
      pr_wanted  ; pr_unwanted; pr_selected ; pr_quorum   ;
      pr_dumpin  ;
      gn_debug   ; }

  (* -------------------------------------------------------------------- *)
  let mk_prover_info scope (options : smt_options) =
    let dft = Prover_info.get scope.sc_options in
    mk_prover_info_from_dft dft options

  (* -------------------------------------------------------------------- *)
  let do_prover_info scope ?(default = empty_options) ppr =
    let options = Option.map (process_prover_option (env scope)) ppr in
    let options = Option.value ~default options in
    mk_prover_info scope options

  (* -------------------------------------------------------------------- *)
  let pprover_infos_to_prover_infos
      (env : EcEnv.env) (dft : EcProvers.prover_infos)
      (ppr : pprover_infos) : EcProvers.prover_infos =
    let options = process_prover_option env ppr in
    mk_prover_info_from_dft dft options

  (* -------------------------------------------------------------------- *)
  let process scope ppr =
    let pi = do_prover_info scope (Some ppr) in
    { scope with sc_options = Prover_info.set scope.sc_options pi }

  (* -------------------------------------------------------------------- *)
  let set_default scope options =
    let provers = match fst options.po_provers with
      | None   ->
        let provers = EcProvers.dft_prover_names in
        List.filter EcProvers.is_prover_known provers

      | Some l ->
        List.iter
          (fun name -> if not (EcProvers.is_prover_known name) then
              hierror "unknown prover %s" name) l; l in
    let options =
      { options with po_provers = (Some provers, snd options.po_provers) } in
    let pi = mk_prover_info scope options in
    { scope with sc_options = Prover_info.set scope.sc_options pi }

  (* -------------------------------------------------------------------- *)
  let full_check scope =
    { scope with sc_options = Check_mode.set_fullcheck scope.sc_options }

  (* -------------------------------------------------------------------- *)
  let check_proof scope b =
    { scope with sc_options = Check_mode.set_checkproof scope.sc_options b }
end

(* -------------------------------------------------------------------- *)
module Tactics = struct
  type prinfos =
    EcCoreGoal.proofenv * (EcCoreGoal.handle * EcCoreGoal.handle list)

  type proofmode = [`WeakCheck | `Check | `Report]

  let pi scope pi = Prover.do_prover_info scope pi

  let proof ?src:_ (scope : scope) =
    check_state `InActiveProof "proof script" scope;

    match (oget scope.sc_pr_uc).puc_active with
    | None -> hierror "no active lemmas"
    | Some (pac, pct) ->
      let pac =
        if pac.puc_started then
          hierror "[proof] can only be used at beginning of a proof script";
        { pac with puc_started = true }
      in
        { scope with sc_pr_uc =
            Some { (oget scope.sc_pr_uc) with puc_active = Some (pac, pct); } }

  let process_r ?reloc mark (mode : proofmode) (scope : scope) (tac : ptactic list) =
    check_state `InProof "proof script" scope;

    let scope =
      match (oget scope.sc_pr_uc).puc_active with
      | None -> hierror "no active lemma"
      | Some (pac, _) ->
          if   mark && not pac.puc_started
          then proof scope
          else scope
    in

    let puc = oget (scope.sc_pr_uc) in
    let pac, pct = oget (puc).puc_active in

    match pac.puc_jdg with
    | PSNoCheck ->
        None, scope

    | PSCheck juc ->
        let module TTC = EcHiTacticals in

        let htmode =
          match mode with
          | `WeakCheck -> `Admit
          | `Check     -> `Strict
          | `Report    -> `Report
        in

        let ttenv = {
          EcHiGoal.tt_provers    = pi scope;
          EcHiGoal.tt_smtmode    = htmode;
          EcHiGoal.tt_implicits  = Options.get_implicits scope;
          EcHiGoal.tt_oldip      = Options.get_oldip scope;
          EcHiGoal.tt_redlogic   = Options.get_redlogic scope;
          EcHiGoal.tt_und_delta  = Options.get_und_delta scope; } in

        let (hds, juc) =
          try  TTC.process ttenv tac juc
          with EcCoreGoal.TcError tcerror ->
            let tcerror =
              ofold
                (fun reloc error ->
                  { error with EcCoreGoal.tc_reloced = Some (reloc, true) })
                tcerror reloc
            in raise (EcCoreGoal.TcError tcerror)
        in

        let penv = EcCoreGoal.proofenv_of_proof juc in

        let pac = { pac with puc_jdg = PSCheck juc } in
        let puc = { puc with puc_active = Some (pac, pct); } in
        let scope = { scope with sc_pr_uc = Some puc } in
        Some (penv, hds), scope

  let process1_r mark mode scope t =
    process_r mark mode scope [t]

  let process_core mark mode (scope : scope) (ts : ptactic_core list) =
    let ts = List.map (fun t -> { pt_core = t; pt_intros = []; }) ts in
    snd (process_r mark mode scope ts)

  let process ?src:_ scope mode tac =
    process_r true mode scope tac
end

(* -------------------------------------------------------------------- *)
module Auto = struct
  let add_rw scope ~local ~base l =
    let scope, base =
      match EcEnv.BaseRw.lookup_opt base.pl_desc (env scope) with
      | None ->
        let pre, ibase = unloc base in
        if not (List.is_empty pre) then
          hierror ~loc:base.pl_loc
            "cannot create rewrite hints out of its enclosing theory";
        let scope =
          let item = EcTheory.mkitem ~import:true (EcTheory.Th_baserw (ibase, local)) in
          { scope with sc_env = EcSection.add_item item scope.sc_env; } in
        (scope, fst (EcEnv.BaseRw.lookup base.pl_desc (env scope)))

      | Some (base, _) -> (scope, base) in

    let env = env scope in
    let l = List.map (fun l -> EcEnv.Ax.lookup_path (unloc l) env) l in
    let item = EcTheory.mkitem ~import:true (Th_addrw (base, l, local)) in
    { scope with sc_env =  EcSection.add_item item scope.sc_env }

  let bind_hint scope ~local ~level ?base axioms =
    let item = EcTheory.mkitem ~import:true (Th_auto { level; base; axioms; locality = local; }) in
    { scope with sc_env = EcSection.add_item item scope.sc_env }

  let add_hint scope hint =
    let base = omap unloc hint.ht_base in
    let env = env scope in
    let names = List.map
      (fun l -> EcEnv.Ax.lookup_path (unloc l) env)
      hint.ht_names in
    let mode = if List.mem `Rigid hint.ht_options then `Rigid else `Default in
    let names = List.map (fun p -> (p, mode)) names in

    bind_hint scope ~local:hint.ht_local ~level:hint.ht_prio ?base names
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  open EcParsetree
  open EcDecl

  module TT = EcTyping

  type proofmode = Tactics.proofmode

  (* ------------------------------------------------------------------ *)
  let bind ?(import = true) (scope : scope) ((x, ax) : _ * axiom) =
    assert (scope.sc_pr_uc = None);
    let item = EcTheory.mkitem ~import (EcTheory.Th_axiom (x, ax)) in
    { scope with sc_env = EcSection.add_item item scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let start_lemma scope (cont, axflags) check ?name (axd, ctxt) =
    let puc =
      match check with
      | false -> PSNoCheck
      | true  ->
          let hyps  = EcEnv.LDecl.init (env scope) axd.ax_tparams in
          let proof = EcCoreGoal.start hyps axd.ax_spec in
          PSCheck proof
    in
    let puc =
      let active =
        { puc_name    = name
        ; puc_started = false
        ; puc_jdg     = puc
        ; puc_flags   = axflags
        ; puc_crt     = axd }
      in
        { puc_active    = Some (active, ctxt);
          puc_cont      = cont;
          puc_init      = scope.sc_env; }
    in
      { scope with sc_pr_uc = Some puc }

  (* ------------------------------------------------------------------ *)
  let rec add_r (scope : scope) (mode : proofmode) (ax : paxiom located) =
    assert (scope.sc_pr_uc = None);

    let env = env scope in
    let loc = ax.pl_loc and ax = ax.pl_desc in
    let ue  = TT.transtyvars env (loc, ax.pa_tyvars) in

    let (pconcl, tintro) =
      match ax.pa_vars with
      | None ->
          (ax.pa_formula, [])
      | Some vs ->
          let pconcl = mk_loc loc (PFforall (vs, ax.pa_formula)) in
          (pconcl, List.flatten (List.map fst vs))
    in

    let ip =
      let ip x = x |> omap (fun x -> `Named (unloc x)) |> odfl `Clear in
      List.map (lmap (fun x -> IPCore (ip x))) tintro in
    let tintro = mk_loc loc (Plogic (Pmove prevertv0)) in
    let tintro = { pt_core = tintro; pt_intros = [`Ip ip]; } in

    let concl = TT.trans_prop env ue pconcl in

    Option.iter (fun infos ->
      hierror
        "the formula contains free %a variables"
        EcUserMessages.TypingError.pp_uniflags infos
    ) (EcUnify.UniEnv.xclosed ue);

    let uidmap = EcUnify.UniEnv.close ue in
    let tw_uni = EcUnify.UniEnv.tw_assubst ue in
    let fs = Tuni.subst ~tw_uni uidmap in
    let concl   = Fsubst.f_subst fs concl in
    let tparams = EcUnify.UniEnv.tparams ue in

    let axd  =
      let kind =
        match ax.pa_kind with
        | PAxiom tags -> `Axiom (Ssym.of_list (List.map unloc tags), false)
        | _ -> `Lemma

      in { ax_tparams    = tparams;
           ax_spec       = concl;
           ax_kind       = kind;
           ax_loca       = ax.pa_locality;
           ax_smt = true; }
    in

    match ax.pa_kind with
    | PLemma tc -> begin
        let local =
          match ax.pa_locality with
          | `Declare -> hierror ~loc "cannot mark with `declare` a lemma"
          | `Local   -> true
          | `Global  -> false in

        let check    = Check_mode.check scope.sc_options in
        let pucflags = { puc_smt = axd.ax_smt; puc_local = local; } in
        let pucflags = (([], None), pucflags) in

        match tc with
        | None ->
            let scope =
              start_lemma scope ~name:(unloc ax.pa_name)
                pucflags check (axd, None) in
            let scope = snd (Tactics.process1_r false `Check scope tintro) in
            None, scope

        | Some tc ->
            start_lemma_with_proof scope
              (Some tintro) pucflags (mode, mk_loc loc tc) check
              ~name:(unloc ax.pa_name) axd
      end

    | PAxiom _ ->
        (Some (unloc ax.pa_name), bind scope (unloc ax.pa_name, axd))

  (* ------------------------------------------------------------------ *)
  and add_defer (scope : scope) proofs =
    match proofs with
    | [] -> scope
    | _  ->
        assert (scope.sc_pr_uc = None);
        let puc = { puc_active = None;
                    puc_cont   = (proofs, Some scope.sc_env);
                    puc_init   = scope.sc_env; }
        in { scope with sc_pr_uc = Some puc; }

  (* ------------------------------------------------------------------ *)
  and save_r ?(mode = `Save) scope =
    let puc = oget scope.sc_pr_uc in
    let pac, pct =
      match puc.puc_active with
      | None -> hierror "no active lemma"
      | Some (pac, pct) -> begin
          match pac.puc_jdg with
          | PSNoCheck -> ()
          | PSCheck _ when mode <> `Save -> ()
          | PSCheck pf -> begin
              if not (EcCoreGoal.closed pf) then
                hierror "cannot save an incomplete proof"
          end
      end; (pac, pct)
    in

    let scope = { scope with
      sc_pr_uc = Some { puc with puc_active = None; } }
    in

    let puc =
      if mode = `Abort then pct
        |> omap (fun pct ->
          { puc with puc_cont =
              fst_map (fun x -> pct :: x) puc.puc_cont })
        |> odfl puc
      else puc in

    let puc   = { puc with puc_active = None; } in
    let scope = { scope with sc_pr_uc = Some puc } in

    let scope =
      match fst puc.puc_cont with
      | [] -> { scope with sc_pr_uc = None; }
      | _  -> scope
    in

    match mode with
    | `Save | `Admit ->
      let scope =
        match snd puc.puc_cont with
        | Some e ->
            { scope with sc_env = e }

        | None ->
            let bind name scope = bind scope (name, pac.puc_crt) in
            pac.puc_name |> ofold bind scope

      in (pac.puc_name, scope)

    | `Abort ->
         (None, { scope with sc_env = puc.puc_init })

  (* ------------------------------------------------------------------ *)
  and start_lemma_with_proof scope tintro pucflags (mode, tc) check ?name axd =
    let { pl_loc = loc; pl_desc = tc } = tc in

    let scope = start_lemma scope pucflags check ?name (axd, None) in
    let scope =
      tintro |> ofold
        (fun t sc -> snd (Tactics.process1_r false `Check sc t))
        scope in
    let scope = Tactics.proof scope in

    let tc =
      match tc with
      | Some tc -> tc
      | None    ->
          let dtc = { pl_loc = loc; pl_desc = Pby None; } in
          [{ pt_core = dtc; pt_intros = []; }]
    in

    let tc = { pl_loc = loc; pl_desc = Pby (Some tc) } in
    let tc = { pt_core = tc; pt_intros = []; } in

    let _, scope = Tactics.process_r false mode scope [tc] in
    save_r scope

  (* ------------------------------------------------------------------ *)
  let save ?src:_ scope =
    check_state `InProof "save" scope;
    save_r ~mode:`Save scope

  (* ------------------------------------------------------------------ *)
  let admit ?src:_ scope =
    check_state `InProof "admitted" scope;
    save_r ~mode:`Admit scope

  (* ------------------------------------------------------------------ *)
  let abort ?src:_ scope =
    check_state `InProof "abort" scope;
    snd (save_r ~mode:`Abort scope)

  (* ------------------------------------------------------------------ *)
  let add ?src:_ (scope : scope) (mode : proofmode) (ax : paxiom located) =
    add_r scope mode ax

  (* ------------------------------------------------------------------ *)
  let realize (scope : scope) (mode : proofmode) (rl : prealize located) =
    check_state `InProof "activate" scope;

    let loc = rl.pl_loc and rl = rl.pl_desc in
    let qn  = EcPath.fromqsymbol (unloc rl.pr_name) in

    let puc = oget scope.sc_pr_uc in
    let _ =
      match puc.puc_active with
      | Some _ -> hierror "a lemma is already active"
      | None -> ()
    in

    let (((axname, ax), _, axenv) as st, proofs) =
      let rec doit past proofs =
        match proofs with
        | [] -> hierror "no such lemma: `%s'" (EcPath.tostring qn)
        | (((_, _), p, _) as st) :: proofs ->
            match EcPath.p_equal p qn with
            | false -> doit (st :: past) proofs
            | true  -> (st, List.rev_append past proofs)
      in
        doit [] (fst puc.puc_cont)
    in
    let pucflags = { puc_smt = ax.ax_smt; puc_local = false; } in
    let pucflags = ((proofs, snd puc.puc_cont), pucflags) in
    let check    = Check_mode.check scope.sc_options in

    let scope = { scope with sc_env = axenv } in

    match rl.pr_proof with
    | None ->
        None, start_lemma scope pucflags check ?name:axname (ax, Some st)

    | Some tc ->
        start_lemma_with_proof scope
          None pucflags (mode, mk_loc loc tc) check
          ?name:axname ax
end

(* -------------------------------------------------------------------- *)
module Op = struct
  open EcTypes
  open EcDecl
  open EcFol

  module TT  = EcTyping
  module EHI = EcHiInductive

  let bind ?(import = true) (scope : scope) ((x, op) : _ * operator) =
    assert (scope.sc_pr_uc = None);
    let item = EcTheory.mkitem ~import (EcTheory.Th_operator (x, op)) in
    { scope with sc_env = EcSection.add_item item scope.sc_env; }

  (* -------------------------------------------------------------------- *)
  let axiomatized_op ?(nargs = 0) ?(nosmt = false) path (tparams, axbd) lc =
    let axpm, axbd =
      let subst, axpm = EcSubst.fresh_tparams EcSubst.empty tparams in
      (axpm, EcSubst.subst_form subst axbd)
    in

    let args, axbd =
      match axbd.f_node with
      | Fquant (Llambda, bds, axbd) ->
          let bds, flam = List.split_at nargs bds in
          (bds, f_lambda flam axbd)
      | _ -> [], axbd
    in

    let opargs = List.map (fun (x, ty) -> f_local x (gty_as_ty ty)) args in
    let opty   = toarrow (List.map f_ty opargs) axbd.EcAst.f_ty in
    let op     = f_op_tc path (etyargs_of_tparams axpm) opty in
    let op     = f_app op opargs axbd.f_ty in
    let axspec = f_forall args (f_eq op axbd) in

    { ax_tparams    = axpm;
      ax_spec       = axspec;
      ax_kind       = `Axiom (Ssym.empty, false);
      ax_loca       = lc;
      ax_smt = if nosmt then false else true; }

  let add ?src:_ (scope : scope) (op : poperator located) =
    assert (scope.sc_pr_uc = None);
    let op = op.pl_desc and loc = op.pl_loc in
    let eenv = env scope in
    let ue = TT.transtyvars eenv (loc, op.po_tyvars) in

    let lc = op.po_locality in
    let args = fst op.po_args @ odfl [] (snd op.po_args) in
    let (ty, body, refts) =
      match op.po_def with
      | PO_abstr pty ->
          let codom = TT.transty TT.tp_relax eenv ue pty in
          let xs    = snd (TT.trans_binding eenv ue args) in
          (EcTypes.toarrow (List.map snd xs) codom, `Abstract, [])

      | PO_concr (pty, pf) ->
          let codom   = TT.transty TT.tp_relax eenv ue pty in
          let env, xs = TT.trans_binding eenv ue args in
          let body    = TT.trans_form env ue pf codom in
          let lam     = f_lambda (List.map (fun (x, ty) -> (x, GTty ty)) xs) body in
          (lam.f_ty, `Plain lam, [])

      | PO_case (pty, pbs) -> begin
          let name = { pl_loc = loc; pl_desc = unloc op.po_name } in
          match EHI.trans_matchfix eenv ue name (args, pty, pbs) with
          | (ty, opinfo) -> (ty, `Fix opinfo, [])
        end

      | PO_reft (pty, (rname, reft)) ->
          let env      = env scope in
          let codom    = TT.transty TT.tp_relax eenv ue pty in
          let _env, xs = TT.trans_binding eenv ue args in
          let opty     = EcTypes.toarrow (List.map snd xs) codom in
          let opabs    = EcDecl.mk_op ~opaque:optransparent [] codom None lc in
          let openv    = EcEnv.Op.bind (unloc op.po_name) opabs env in
          let openv    = EcEnv.Var.bind_locals xs openv in
          let reft     = TT.trans_prop openv ue reft in
          (opty, `Abstract, [(rname, xs, reft, codom)])
    in

    Option.iter (fun infos ->
      hierror ~loc
        "this operator type contains free %a variables"
        EcUserMessages.TypingError.pp_uniflags infos
    ) (EcUnify.UniEnv.xclosed ue);

    let uidmap  = EcUnify.UniEnv.close ue in
    let tw_uni  = EcUnify.UniEnv.tw_assubst ue in
    let ts      = Tuni.subst ~tw_uni uidmap in
    let fs      = Fsubst.f_subst ts in
    let ty      = ty_subst ts ty in
    let tparams = EcUnify.UniEnv.tparams ue in
    let body    =
      match body with
      | `Abstract -> None
      | `Plain e  -> Some (OP_Plain (fs e))
      | `Fix opfx ->
          Some (OP_Fix {
            opf_recp     = EcPath.psymbol "_";
            opf_args     = opfx.EHI.mf_args;
            opf_resty    = opfx.EHI.mf_codom;
            opf_struct   = (opfx.EHI.mf_recs, List.length opfx.EHI.mf_args);
            opf_branches = opfx.EHI.mf_branches;
          })

    in

    let tags   = Sstr.of_list (List.map unloc op.po_tags) in
    let opaque = {
      smt       = Sstr.mem "smt_opaque" tags;
      reduction = Sstr.mem "opaque" tags
    } in
    let unfold =
      match op.po_args with
      | (a, Some _) -> Some (List.length a)
      | (_, None) -> None in

    let tyop   = EcDecl.mk_op ~opaque ?unfold tparams ty body lc in
    let opname = EcPath.pqname (EcEnv.root eenv) (unloc op.po_name) in

    if op.po_kind = `Const then begin
      let tue   = EcUnify.UniEnv.copy ue in
      let ty, _ = EcUnify.UniEnv.openty tue tparams None ty in
      let tdom  = EcUnify.UniEnv.fresh tue in
      let tcom  = EcUnify.UniEnv.fresh tue in
      let tfun  = EcTypes.tfun tdom tcom in

        try
          EcUnify.unify eenv tue ty tfun;
          let msg = "this operator type is (unifiable to) a function type" in
            hierror ~loc "%s" msg
        with EcUnify.UnificationFailure _ -> ()
    end;

    let scope =
      match op.po_ax with
      | None    -> bind scope (unloc op.po_name, tyop)
      | Some ax -> begin
          match tyop.op_kind with
          | OB_oper (Some (OP_Plain bd)) ->
              let path  = EcPath.pqname (path scope) (unloc op.po_name) in
              let axop  =
                let nargs = List.sum (List.map (fst |- List.length) args) in
                  axiomatized_op ~nargs path (tyop.op_tparams, bd) lc in
              let tyop  = { tyop with op_opaque = { reduction = true; smt = false; }} in
              let scope = bind scope (unloc op.po_name, tyop) in
              Ax.bind scope (unloc ax, axop)

          | _ -> hierror ~loc "cannot axiomatize non-plain operators"
      end
    in

    let scope =
      List.fold_left (fun scope (rname, xs, ax, codom) ->
          let ax =
            let opargs  = List.map (fun (x, xty) -> e_local x xty) xs in
            let opapp   = List.map (fst |- tvar) tparams in
            let opapp   = e_app (e_op opname opapp ty) opargs codom in

            let subst   = EcSubst.add_opdef EcSubst.empty opname ([], opapp) in
            let ax      = EcSubst.subst_form subst ax in
            let ax      = f_forall (List.map (snd_map gtty) xs) ax in

            let uidmap  = EcUnify.UniEnv.close ue in
            let tw_uni  = EcUnify.UniEnv.tw_assubst ue in
            let subst   = Tuni.subst ~tw_uni uidmap in
            let ax      = Fsubst.f_subst subst ax in

            ax
          in

          let axpm, ax =
            let subst, tparams = EcSubst.fresh_tparams EcSubst.empty tparams in
            (tparams, EcSubst.subst_form subst ax) in

          let ax =
            { ax_tparams    = axpm;
              ax_spec       = ax;
              ax_kind       = `Axiom (Ssym.empty, false);
              ax_loca       = lc;
              ax_smt = true; }
          in Ax.bind scope (unloc rname, ax))
        scope refts
    in

    let scope =
      if not (List.is_empty op.po_aliases) then begin
        if not (EcUtils.is_none body) || not (List.is_empty refts) then
          hierror ~loc
            "multiple names are only allowed for non-refined abstract operators";
        let addnew scope name =
          let subst, nparams =
            EcSubst.fresh_tparams EcSubst.empty tparams in
          let rop =
            EcDecl.mk_op ~opaque:optransparent
            nparams (EcSubst.subst_ty subst ty) None lc in
          bind scope (unloc name, rop)
        in List.fold_left addnew scope op.po_aliases

      end else scope
    in

    let axs = ref [] in

    let add_distr_tag
        (pred : path) (bases : string list) (tag : string) (suffix : string) scope
    =
      if not (EcAlgTactic.is_module_loaded (env scope)) then
        hierror "for tag %s, load Distr first" tag;

      let subst, nparams =
        EcSubst.fresh_tparams EcSubst.empty tyop.op_tparams in
      let oppath = EcPath.pqname (path scope) (unloc op.po_name) in
      let optyargs =
        let mktcw (a : EcIdent.t) (i : int) =
          TCIAbstract { support = `Var a; offset = i; lift = [] }
        in
          List.map
            (fun (a, tcs) -> (tvar a, List.mapi (fun i _ -> mktcw a i) tcs))
            nparams
      in
      let ty = EcSubst.subst_ty subst tyop.op_ty in
      let aty, rty = EcTypes.tyfun_flat ty in

      let dty =
        match EcTypes.as_tdistr (EcEnv.ty_hnorm rty (env scope)) with
        | None -> hierror ~loc "[%s] can only be applied to distributions" tag
        | Some dty -> dty
      in

      let bds = List.combine (List.map EcTypes.fresh_id_of_ty aty) aty in
      let ax  = EcFol.f_op_tc oppath optyargs ty in
      let ax  = EcFol.f_app ax (List.map (curry f_local) bds) rty in
      let ax  = EcFol.f_app (EcFol.f_op pred [dty] (tfun rty tbool)) [ax] tbool in
      let ax  = EcFol.f_forall (List.map (snd_map gtty) bds) ax in

      let ax =
        { ax_tparams    = nparams;
          ax_spec       = ax;
          ax_kind       = `Axiom (Ssym.empty, false);
          ax_loca       = lc;
          ax_smt = true; } in

      let scope, axname =
        let axname = Printf.sprintf "%s_%s" (unloc op.po_name) suffix in
        (Ax.bind scope (axname, ax), axname) in

      axs := axname :: !axs;

      let axpath = EcPath.pqname (path scope) axname in

      List.fold_left
        (fun scope base ->
            Auto.bind_hint ~local:(local_of_locality lc) ~level:0 ~base scope [(axpath, `Default)])
        scope bases

    in

    let scope =
      if   Sstr.mem "lossless" tags
      then add_distr_tag EcCoreLib.CI_Distr.p_lossless
             [EcCoreLib.base_ll; EcCoreLib.base_rnd] "lossless" "ll" scope
      else scope in

    let scope =
      if   Sstr.mem "uniform" tags
      then add_distr_tag EcCoreLib.CI_Distr.p_uniform
             [EcCoreLib.base_rnd] "uniform" "uni" scope
      else scope in

    let scope =
      if   Sstr.mem "full" tags
      then add_distr_tag EcCoreLib.CI_Distr.p_full
             [EcCoreLib.base_rnd] "full" "fu" scope
      else scope in

    tyop, List.rev !axs, scope


  let add_opsem ?src:_ (scope : scope) (op : pprocop located) =
    let module Sem = EcProcSem in

    let op = unloc op in
    let f  = EcTyping.trans_gamepath (env scope) op.ppo_target  in
    let sig_, body =
      let f = EcEnv.Fun.by_xpath f (env scope) in
      let body =
        match f.f_def with
        | FBdef body -> body
        | _ -> raise Sem.SemNotSupported in

        (f.f_sig, body) in

    let ret = oget ~exn:Sem.SemNotSupported body.f_ret in

    let params =
      let for1 (v : ovariable) =
        (oget ~exn:Sem.SemNotSupported v.ov_name, v.ov_type) in
      List.map for1 sig_.fs_anames in

    let env = Sem.Env.empty (env scope) in
    let env, ids = List.fold_left_map Sem.Env.fresh env (List.fst params) in

    let cont (env : Sem.senv) =
      (`Det, Sem.translate_e env ret) in

    let mode, aout = Sem.translate_s env cont body.f_body in
    let aout =
      let m = EcIdent.create "&hr" in
      form_of_expr ~m aout in (* FIXME: translate to forms directly? *)
    let aout = f_lambda (List.map2 (fun (_, ty) x -> (x, GTty ty)) params ids) aout in

    let opdecl = EcDecl.{
      op_tparams  = [];
      op_ty       = aout.f_ty;
      op_kind     = OB_oper (Some (OP_Plain aout));
      op_loca     = op.ppo_locality;
      op_opaque   = optransparent;
      op_clinline = false;
      op_unfold   = None;
    } in

    let oppath = EcPath.pqname (path scope) (unloc op.ppo_name) in

    let scope = bind scope (unloc op.ppo_name, opdecl) in

    let scope =
      let prax =
        let m     = EcIdent.create "&hr" in
        let locs  = List.map (fun (x, ty) -> (EcIdent.create x, ty)) params in
        let res   = f_pvar pv_res sig_.fs_ret m in
        let resx  = EcIdent.create "v" in
        let resv  = f_local resx sig_.fs_ret in
        let prmem = EcIdent.create "&m" in

        let mu =
          let sem =
            f_app
              (f_op oppath [] opdecl.op_ty)
              (List.map (fun (x, ty) -> f_local x ty) locs)
              (match mode with `Det -> sig_.fs_ret | `Distr -> tdistr sig_.fs_ret) in

          match mode with
          | `Det ->
             f_if (f_eq sem resv) f_r1 f_r0

          | `Distr ->
             f_mu_x sem resv
        in

        f_forall
          [(prmem, GTmem EcMemory.abstract_mt)]
          (f_forall
             (List.map (fun (x, ty) -> (x, GTty ty)) ((resx, sig_.fs_ret) :: locs))
             (f_eq
                (f_pr prmem
                   f
                   (f_tuple (List.map (fun (x, ty) -> f_local x ty) locs))
                   { m; inv = f_eq res.inv resv })
                mu))
      in

      let prax = EcDecl.{
        ax_tparams    = [];
        ax_spec       = prax;
        ax_kind       = `Lemma;
        ax_loca       = op.ppo_locality;
        ax_smt = true;
      } in

      Ax.bind scope (unloc op.ppo_name ^ "_opsem", prax) in

    let scope =
      match mode with
      | `Det ->
         let hax =
           let m     = EcIdent.create "&hr" in
           let locs  = List.map (fun (x, ty) -> (EcIdent.create x, ty)) params in
           let res   = f_pvar pv_res sig_.fs_ret m in
           let args  = f_pvar pv_arg sig_.fs_arg m in

           f_forall
             (List.map (fun (x, ty) -> (x, GTty ty)) locs)
             (f_hoareF
                { m; inv = f_eq
                   args.inv
                   (f_tuple (List.map (fun (x, ty) -> f_local x ty) locs)) }
                f
                (POE.lift { m; inv = f_eq
                   res.inv
                   (f_app
                      (f_op oppath [] opdecl.op_ty)
                      (List.map (fun (x, ty) -> f_local x ty) locs)
                      sig_.fs_ret) }))
         in

         let prax = EcDecl.{
           ax_tparams    = [];
           ax_spec       = hax;
           ax_kind       = `Lemma;
           ax_loca       = op.ppo_locality;
           ax_smt = true;
         } in

         Ax.bind scope (unloc op.ppo_name ^ "_opsem_det", prax)

      | `Distr ->
         scope
    in

    scope
end

(* -------------------------------------------------------------------- *)
module Exception = struct
  module TT = EcTyping

  let add (scope : scope) (pe : pexception_decl located) =
    assert (scope.sc_pr_uc = None);
    let loc = loc pe in
    let pe = pe.pl_desc in
    let lc = pe.pe_locality in
    let eenv = env scope in
    let ue = TT.transtyvars eenv (loc, Some []) in
    let e_dom = transtys tp_nothing eenv ue pe.pe_dom in
    let tparams = EcUnify.UniEnv.tparams ue in
    if tparams <> [] then
      hierror ~loc "Polymorphic expression are not allowed";
    let e   = EcDecl.mk_exception lc e_dom in
    let op  = EcDecl.operator_of_exception e in
    let scope = Op.bind scope (unloc pe.pe_name, op) in
    e, scope
end

(* -------------------------------------------------------------------- *)
module Pred = struct
  module TT = EcTyping

  let add ?src:_ (scope : scope) (pr : ppredicate located) =
    assert (scope.sc_pr_uc = None);

    let typr  = EcHiPredicates.trans_preddecl (env scope) pr in
    let scope = Op.bind scope (unloc (unloc pr).pp_name, typr) in
    typr, scope
end

(* -------------------------------------------------------------------- *)
module Notations = struct
  module TT  = EcTyping

  let add (scope : scope) (nt : pnotation located) =
    EcHiNotations.trans_notation (env scope) nt; scope

  let add_abbrev (scope : scope) (ab : pabbrev located) =
    let op = EcHiNotations.trans_abbrev (env scope) ab in
    Op.bind scope op
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  module TT = EcTyping

  let bind ?(import = true) (scope : scope) (m : top_module_expr) =
    assert (scope.sc_pr_uc = None);
    let item = EcTheory.mkitem ~import (EcTheory.Th_module m) in
    { scope with sc_env = EcSection.add_item item scope.sc_env }

  let add_concrete (scope : scope) lc (ptm : pmodule_def) =
    assert (scope.sc_pr_uc = None);

    if lc = `Declare then
      hierror "cannot use [declare] for concrete modules";

    let m = TT.transmod (env scope) ~attop:true ptm in
    let ur = EcModules.get_uninit_read_of_module (path scope) m in

    if not (List.is_empty ur) then begin
      let ppe = EcPrinting.PPEnv.ofenv (env scope) in
      let pp fmt (xp, names) =
        Format.fprintf fmt "  - %a -> [%a]"
          (EcPrinting.pp_funname ppe) (xastrip xp)
          (EcPrinting.pp_list ", " pp_symbol)
          (Ssym.elements names)
      in

      notify scope `Warning
        "these procedures may use uninitialized local variables:@\n@[<v>%a@]"
        (EcPrinting.pp_list "@," pp) ur
    end;

    bind scope {tme_expr = m; tme_loca = lc}

  let declare (scope : scope) (m : pmodule_decl) =
    let modty = m.ptm_modty in
    let name  = EcIdent.create (unloc m.ptm_name) in
    let tysig = fst (TT.transmodtype (env scope) modty.pmty_pq) in
    (* We modify tysig restrictions according if necessary. *)
    let tysig = trans_restr_for_modty (env scope) tysig modty.pmty_mem in

    { scope with
        sc_env = EcSection.add_decl_mod name tysig scope.sc_env }

  let add ?src:_ (scope : scope) (m : pmodule_def_or_decl) =
    match m with
    | { ptm_locality = lc; ptm_def = `Concrete def } ->
      add_concrete scope lc def

    | { ptm_locality = lc; ptm_def = `Abstract decl } ->
      if lc <> `Declare then
        hierror "use declare for abstract module";
      declare scope decl

  let import (scope : scope) (m : pmsymbol located) : scope =
    let m, _ = EcTyping.trans_msymbol (env scope) m in
    { scope with sc_env = EcSection.import_vars m scope.sc_env }

end

(* -------------------------------------------------------------------- *)
module ModType = struct
  let bind
        ?(import = true) (scope : scope)
        ((x, tysig) : _ * top_module_sig)
  =
    assert (scope.sc_pr_uc = None);
    let item = EcTheory.mkitem ~import (EcTheory.Th_modtype (x, tysig)) in
    { scope with sc_env = EcSection.add_item item scope.sc_env }

  let add ?src:_ (scope : scope) (intf : pinterface) =
    assert (scope.sc_pr_uc = None);
    let tysig = EcTyping.transmodsig (env scope) intf in
    bind scope (unloc intf.pi_name, tysig)
end

(* -------------------------------------------------------------------- *)
(* Forward reference: filled in later by [Cloning] (which depends on
   [Theory] which is defined after [Ty]). *)
let subtype_hooks_ref : scope EcTheoryReplay.ovrhooks ref =
  ref { EcTheoryReplay.henv      = (fun _ -> assert false);
        EcTheoryReplay.hadd_item = (fun _ ~import:_ _ -> assert false);
        EcTheoryReplay.hthenter  = (fun _ _ _ _ -> assert false);
        EcTheoryReplay.hthexit   = (fun _ ~import:_ _ -> assert false);
        EcTheoryReplay.herr      = (fun ?loc:_ _ -> assert false); }

(* -------------------------------------------------------------------- *)
module Ty = struct
  open EcDecl
  open EcTyping

  module TT  = EcTyping
  module ELI = EcInductive
  module EHI = EcHiInductive

  (* ------------------------------------------------------------------ *)
  let check_name_available scope x =
    let pname = EcPath.pqname (EcEnv.root (env scope)) x.pl_desc in

    if    EcEnv.Ty       .by_path_opt pname (env scope) <> None
       || EcEnv.TypeClass.by_path_opt pname (env scope) <> None then
      hierror ~loc:x.pl_loc "duplicated type/type-class name `%s'" x.pl_desc

  (* ------------------------------------------------------------------ *)
  let bind ?(import = true) (scope : scope) ((x, tydecl) : (_ * tydecl)) =
    assert (scope.sc_pr_uc = None);
    let item = EcTheory.mkitem ~import (EcTheory.Th_type (x, tydecl)) in
    { scope with sc_env = EcSection.add_item item scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let add_subtype (scope : scope) ({ pl_desc = subtype } : psubtype located) =
    let loced x = mk_loc _dummy x in
    let env = env scope in

    let carrier =
      let ue = EcUnify.UniEnv.create None in
      transty tp_tydecl env ue subtype.pst_carrier in

    let pred =
      let x = EcIdent.create (fst subtype.pst_pred).pl_desc in
      let env = EcEnv.Var.bind_local x carrier env in
      let ue = EcUnify.UniEnv.create None in
      let pred = EcTyping.trans_prop env ue (snd subtype.pst_pred) in
      if not (EcUnify.UniEnv.closed ue) then
        hierror ~loc:(snd subtype.pst_pred).pl_loc
          "the predicate contains free type variables";
      let uidmap = EcUnify.UniEnv.close ue in
      let tw_uni = EcUnify.UniEnv.tw_assubst ue in
      let fs = EcCoreSubst.Tuni.subst ~tw_uni uidmap in
      f_lambda [(x, GTty carrier)] (Fsubst.f_subst fs pred) in

    let scope =
      let decl = EcDecl.{
        tyd_params  = [];
        tyd_type    = `Abstract [];
        tyd_resolve = true;
        tyd_loca    = `Global;
        (* Carry the carrier+predicate so [tydecl_fv] picks up the
           dependency on section-declared types and [generalize_tydecl]
           produces the right tparams at section close. *)
        tyd_subtype = Some (carrier, pred);
      } in bind scope (unloc subtype.pst_name, decl) in

    let evclone : EcThCloning.evclone =
      let t_entry : EcThCloning.xty_override = (`Direct carrier, `Inline `Clear) in
      let st_entry : EcThCloning.xty_override =
        ((`ByPath
            (EcPath.pqname (EcEnv.root env) (unloc subtype.pst_name))
          :> [`ByPath of EcPath.path | `BySyntax of EcParsetree.ty_override_def | `Direct of EcAst.ty]),
         `Inline `Clear) in
      let p_entry : EcThCloning.xop_override = (`Direct pred, `Inline `Clear) in
      { EcThCloning.evc_empty with
          evc_types = Msym.of_list [
            "T", loced t_entry;
            "sT", loced st_entry;
          ];
          evc_ops = Msym.of_list [
            "P", loced p_entry;
          ];
          evc_lemmas = {
            ev_bynames = Msym.empty;
            ev_global  =  [ (None, Some [`Include, "prove"]) ]
          } } in

    let cname = Option.map unloc subtype.pst_cname in
    let npath = ofold ((^~) EcPath.pqname) (EcEnv.root env) cname in
    let cpath = EcPath.fromqsymbol ([EcCoreLib.i_top], "Subtype") in
    let theory = EcEnv.Theory.by_path ~mode:`Abstract cpath env in

    let renames : EcThCloning.renaming list =
      match subtype.pst_rename with
      | None -> []
      | Some (insub, val_) -> [
        (`All, (EcRegexp.regexp "val", EcRegexp.subst val_));
        (`All, (EcRegexp.regexp "insub", EcRegexp.subst insub));
      ] in

    let theory = theory.cth_items in

    let (proofs, scope) =
      EcTheoryReplay.replay !subtype_hooks_ref
        ~abstract:false ~override_locality:None ~incl:(Option.is_none cname)
        ~clears:Sp.empty ~renames ~opath:cpath ~npath
        evclone scope
        (Option.value ~default:(EcPath.basename cpath) cname, theory, `Global)
    in
    let proofs =
      List.pmap (fun axc ->
        match axc.EcThCloning.axc_tac with
        | None ->
            Some (fst_map some axc.EcThCloning.axc_axiom,
                  axc.EcThCloning.axc_path,
                  axc.EcThCloning.axc_env)
        | Some _ ->
            (* tactic-bearing proofs require Tactics.process_r which
               isn't available at this point (defined after Ty); they
               are not produced by Subtype's evclone (which only
               provides ev_global), so this branch is unreachable. *)
            assert false)
        proofs
    in
    Ax.add_defer scope proofs

  (* ------------------------------------------------------------------ *)
  let add ?src:_ scope (tyd : ptydecl located) =
    let loc = loc tyd in

    let { pty_name = name; pty_tyvars = args;
          pty_body = body; pty_locality = tyd_loca } = unloc tyd in

    check_name_available scope name;
    let env = env scope in
    let tyd_params, tyd_type =
      match body with
      | PTYD_Abstract tcs ->
        let ue = TT.transtyvars env (loc, Some args) in
        let tcs = List.map (TT.transtc env ue) tcs in
        let tp = EcUnify.UniEnv.tparams ue in
        tp, `Abstract tcs

      | PTYD_Alias bd ->
        let ue     = TT.transtyvars env (loc, Some args) in
        let body   = transty tp_tydecl env ue bd in
        EcUnify.UniEnv.tparams ue, `Concrete body

      | PTYD_Datatype dt ->
        let datatype = EHI.trans_datatype env (mk_loc loc (args,name)) dt in
        let ty_from_ctor ctor = EcEnv.Ty.by_path ctor env in
        let tparams, tydt =
          try
            ELI.check_positivity ty_from_ctor datatype;
            ELI.datatype_as_ty_dtype datatype
          with ELI.NonPositive ctx -> EHI.dterror loc env (EHI.DTE_NonPositive (unloc name, ctx))
        in
        tparams, `Datatype tydt

      | PTYD_Record rt ->
        let record  = EHI.trans_record env (mk_loc loc (args,name)) rt in
        let scheme  = ELI.indsc_of_record record in
        record.ELI.rc_tparams, `Record (scheme, record.ELI.rc_fields)
    in

    bind scope (unloc name,
      { tyd_params; tyd_type; tyd_loca; tyd_resolve = true;
        tyd_subtype = None; })

  (* ------------------------------------------------------------------ *)
  let bindclass ?(import = true) (scope : scope) (x, tc) =
    assert (scope.sc_pr_uc = None);
    let item = EcTheory.mkitem ~import (EcTheory.Th_typeclass(x, tc)) in
    { scope with sc_env = EcSection.add_item item scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let add_class (scope : scope) { pl_desc = tcd; pl_loc = loc } =
    assert (scope.sc_pr_uc = None);
    let lc = tcd.ptc_loca in
    let name  = unloc tcd.ptc_name in
    let scenv = (env scope) in

    check_name_available scope tcd.ptc_name;

    let tclass =
      (* Check typeclasses arguments *)
      let ue = TT.transtyvars scenv (loc, tcd.ptc_params) in

      let uptcs =
        let parent_ue = EcUnify.UniEnv.copy ue in
        let uptcs = List.map
          (fun (p, lbl, ren) ->
            let tcp = TT.transtc scenv parent_ue p in
            (* Default label is the parent class's bare name. *)
            let lbl =
              match lbl with
              | Some l -> unloc l
              | None -> EcPath.basename tcp.tc_name in
            (tcp, lbl,
             List.map (fun (s, t) -> (unloc s, unloc t)) ren))
          tcd.ptc_inth in
        let subst = Tuni.subst
          ~tw_uni:(EcUnify.UniEnv.tw_assubst parent_ue)
          (EcUnify.UniEnv.close parent_ue) in
        List.map (fun (tcp, lbl, ren) ->
          ({ tcp with tc_args = List.map (EcCoreSubst.etyarg_subst subst) tcp.tc_args },
           lbl, ren))
          uptcs in

      (* Reject duplicate edge labels at the same level. If a user
         writes [<: monoid & monoid], both default to label [monoid]
         and ambiguity is unavoidable for any future [proof X<:monoid>]
         clause — force them to disambiguate via explicit [as]. *)
      let () =
        let seen = ref Sstr.empty in
        List.iter (fun (_, lbl, _) ->
          if Sstr.mem lbl !seen then
            hierror ~loc
              "parent edge label `%s' is used by more than one parent \
               of class `%s'. Disambiguate with an explicit \
               [(<parent> as <Label>)] clause."
              lbl (unloc tcd.ptc_name);
          seen := Sstr.add lbl !seen)
          uptcs in

      (* The carrier's [tcs] should reference the class being declared
         (so its own ops can be resolved via [Abs mypath, l=0]) and the
         parent class is reachable via the ancestor chain. To make
         [EcTypeClass.ancestors] work during axiom typing, we pre-bind
         a stub typeclass record. The full record replaces the stub at
         end of [add_class]. *)
      let mypath = EcPath.pqname (path scope) name in
      let stub_tc : tc_decl = {
        tc_tparams = EcUnify.UniEnv.tparams ue;
        tc_prts    = uptcs;
        tc_ops     = [];
        tc_axs     = [];
        tc_loca    = lc;
        tc_ops_origin = [];
      } in
      let scenv =
        EcEnv.TypeClass.rebind name stub_tc scenv in

      let tc_self =
        { tc_name = mypath;
          tc_args = EcDecl.etyargs_of_tparams stub_tc.tc_tparams; } in
      let asty  =
        { tyd_params  = [];
          tyd_type    = `Abstract [tc_self];
          tyd_resolve = true;
          tyd_loca    = (lc :> locality);
          tyd_subtype = None; } in
      let scenv = EcEnv.Ty.bind name asty scenv in

      (* ----------------------------------------------------------------
         Compute the renamed parent ops auto-imported into this class's
         body scope. For each parent edge [(parent_tc, parent_ren)] in
         [uptcs], walk the parent's ancestor DAG via
         [ancestors_with_renaming], compose each ancestor's renaming
         with [parent_ren], and apply the cumulative rename to the
         ancestor's [tc_ops] names. The ancestor's op types use the
         ancestor's tparams; substitute them through to the current
         class's carrier via the chain of [tc_args].

         When the same local name arises from more than one parent
         path (or from independent ancestor ops on the same path),
         reject — the user must add an explicit [with X = Y] rename
         to disambiguate.
         ---------------------------------------------------------------- *)
      let inherited_ops :
        (EcSymbols.symbol * EcTypes.ty * bool
         * (EcPath.path * EcSymbols.symbol)) list =
        (* Current-class carrier as seen from within the body. *)
        let self_carrier =
          EcTypes.tconstr_tc mypath
            (EcDecl.etyargs_of_tparams stub_tc.tc_tparams) in
        (* Rewrite every [Tconstr(anc_path, _)] occurrence to the
           current class's carrier. Ancestor classes are abstract type
           aliases whose only inhabitant is the carrier, so any
           [Tconstr(anc.tc_name, ...)] in a parent op type refers to
           that ancestor's carrier and must be translated to [self]. *)
        let rewrite_carrier (anc_paths : EcPath.Sp.t) (ty : EcTypes.ty) : EcTypes.ty =
          let rec aux t =
            match t.EcAst.ty_node with
            | EcAst.Tconstr (p, _) when EcPath.Sp.mem p anc_paths ->
              self_carrier
            | _ -> EcTypes.ty_map aux t
          in aux ty in
        let collect_from_parent (parent_tc, _parent_lbl, parent_ren) =
          (* All ancestors of [parent_tc] (including itself, with empty rename) *)
          let anc_list = EcTypeClass.ancestors_with_renaming scenv parent_tc in
          let anc_paths =
            List.fold_left (fun s (anc, _) -> EcPath.Sp.add anc.tc_name s)
              EcPath.Sp.empty anc_list in
          List.concat_map (fun (anc, anc_to_parent_ren) ->
            let cumul =
              EcTypeClass.compose_renaming
                ~outer:parent_ren ~inner:anc_to_parent_ren in
            let anc_decl = EcEnv.TypeClass.by_path anc.tc_name scenv in
            let subst =
              List.fold_left2
                (fun s (a, _) etyarg -> Mid.add a etyarg s)
                Mid.empty anc_decl.tc_tparams anc.tc_args in
            List.map (fun (op_id, op_ty) ->
              let orig_name = EcIdent.name op_id in
              let local_name, renamed =
                match List.assoc_opt orig_name cumul with
                | Some n' when n' <> orig_name -> (n', true)
                | _ -> (orig_name, false) in
              let op_ty = EcCoreSubst.Tvar.subst subst op_ty in
              let op_ty = rewrite_carrier anc_paths op_ty in
              (* Origin: the canonical "source of truth" for this op.
                 If the ancestor itself auto-promoted this op from a
                 grandparent, [tc_ops_origin] tells us the deeper
                 origin; we follow it so that ops reached via different
                 inheritance paths (one through the ancestor's
                 [tc_ops], one through a direct walk of the
                 grandparent) get the same origin and dedupe silently.
                 Falls back to [(ancestor_path, op_name)] for ops the
                 ancestor declared itself. *)
              let origin =
                match List.assoc_opt orig_name anc_decl.tc_ops_origin with
                | Some o -> o
                | None -> (anc.tc_name, orig_name) in
              (local_name, op_ty, renamed, origin)
            ) anc_decl.tc_ops
          ) anc_list in
        let all = List.concat_map collect_from_parent uptcs in
        (* Dedup by (local_name, origin). Same op reached through
           multiple inheritance paths in the DAG (same origin =
           (ancestor_path, orig_op_name)) is silently merged. Same
           local_name with DIFFERENT origins is a genuine cross-class
           name collision: reject. *)
        let by_name = Msym.empty in
        let by_name =
          List.fold_left (fun acc (n, ty, renamed, origin) ->
            match Msym.find_opt n acc with
            | None -> Msym.add n (ty, renamed, origin) acc
            | Some (_, _, origin') when origin = origin' -> acc
            | Some _ ->
              hierror ~loc
                "auto-imported parent op `%s' collides with another \
                 inherited op of the same name (different origin). Add \
                 an explicit rename clause [<: P with %s = …] to \
                 disambiguate."
                n n)
            by_name all in
        Msym.bindings by_name
        |> List.map (fun (n, (ty, renamed, origin)) -> (n, ty, renamed, origin)) in

      (* Check for duplicated field names *)
      Msym.odup unloc (List.map fst tcd.ptc_ops)
        |> oiter (fun (x, y) -> hierror ~loc:y.pl_loc
                    "duplicated operator name: `%s'" x.pl_desc);
      Msym.odup unloc (List.map fst tcd.ptc_axs)
        |> oiter (fun (x, y) -> hierror ~loc:y.pl_loc
                    "duplicated axiom name: `%s'" x.pl_desc);

      (* Reject explicit user-declared ops that shadow auto-imported
         inherited ops with the same name. The user must either use the
         inherited op (no redeclaration) or rename it via a [with]
         clause on the parent. *)
      List.iter (fun (x, _) ->
        let xs = unloc x in
        if List.exists (fun (n, _, _, _) -> n = xs) inherited_ops then
          hierror ~loc:x.pl_loc
            "operator `%s' is already provided by a parent class (via \
             inheritance); remove the redundant declaration, or rename \
             the inherited op via a [with %s = …] clause on the parent."
            xs xs
      ) tcd.ptc_ops;

      (* Pre-allocate idents for inherited ops. RENAMED inherited ops
         must share their ident between the body-local binding (used
         during body elaboration) and the [tc_ops] entry (which the
         env-bind machinery uses to build the final substitution that
         rewrites local references into global [OP_TC] references in
         stored axioms). If we used distinct idents, axiom bodies
         elaborated to [Flocal id_local] would NOT match the global
         [Fop (OP_TC mypath name)] emitted at instance-use time, and
         rewrites would fail. Non-renamed inherited ops only appear
         as body-locals (no [tc_ops] entry, since their global lives
         under the ancestor path). *)
      let inherited_idents =
        List.map (fun (n, ty, renamed, origin) ->
          (EcIdent.create n, n, ty, renamed, origin))
          inherited_ops in
      let scenv =
        (* Only bind RENAMED inherited ops as body-locals. Non-renamed
           ops are already resolvable via the global namespace (their
           ancestor class published an [OP_TC] global at the
           ancestor's path), so locally binding them would create
           parallel [Flocal] references that can't be substituted to
           the global at env-bind time (they're not in [tc_ops]),
           leading to axiom-body ops that fail to match use-site
           [Fop] references. *)
        let inherited_locals =
          List.filter_map
            (fun (id, _n, ty, renamed, _) ->
              if renamed then Some (id, ty) else None)
            inherited_idents in
        EcEnv.Var.bind_locals inherited_locals scenv in

      (* Check operators types *)
      let operators =
        let check1 (x, ty) =
          let ue = EcUnify.UniEnv.copy ue in
          let ty = transty tp_tydecl scenv ue ty in
          let uidmap =
            try EcUnify.UniEnv.close ue
            with EcUnify.UninstanciateUni _ ->
              hierror ~loc:x.pl_loc
                "operator `%s' has free type/typeclass variables in its type. \
                 Provide an explicit type instantiation (e.g. via `<:%s>`) to \
                 fix the carrier."
                (unloc x) (unloc tcd.ptc_name)
          in
          let tw_uni = EcUnify.UniEnv.tw_assubst ue in
          let ty = ty_subst (Tuni.subst ~tw_uni uidmap) ty in
            (EcIdent.create (unloc x), ty)
        in
          tcd.ptc_ops |> List.map check1 in

      (* Check axioms *)
      let axioms =
        let scenv = EcEnv.Var.bind_locals operators scenv in
        let check1 (x, ax) =
          let ue = EcUnify.UniEnv.copy ue in
          let ax = trans_prop scenv ue ax in
          let uidmap =
            try EcUnify.UniEnv.close ue
            with EcUnify.UninstanciateUni _ ->
              hierror ~loc:x.pl_loc
                "axiom `%s' is type-ambiguous: free type/typeclass variables \
                 remain after typing. Provide an explicit type instantiation \
                 (e.g. via `<:%s>`) to fix the carrier."
                (unloc x) (unloc tcd.ptc_name)
          in
          let tw_uni = EcUnify.UniEnv.tw_assubst ue in
          let fs = Tuni.subst ~tw_uni uidmap in
          let ax = Fsubst.f_subst fs ax in
            (unloc x, ax)
        in
          tcd.ptc_axs |> List.map check1 in

      (* Promote auto-imported inherited ops to first-class entries of
         [tc_ops]. They are placed before user-declared ops; collisions
         have already been rejected. This makes inherited ops
         externally visible (the env-level [bind_typeclass] loop in
         [ecEnv.ml] creates one global [OP_TC] per [tc_ops] entry) and
         requires each instance to supply a realisation under the
         (possibly renamed) local name — which the instance-side
         [tcsyms] walk already demands via the chain's rename. *)
      (* Only RENAMED inherited ops are promoted to [tc_ops]. Non-renamed
         inherited ops remain accessible via the chain walk (the resolver
         walks [tc_prts] and finds them in the ancestor's [tc_ops]);
         re-emitting them under the current class's path would create a
         duplicate global [OP_TC] symbol and clash with the ancestor's
         own global op. Renamed ops have no ancestor-side global under
         the new name, so we must emit one. The ident is shared with
         the body-local binding (see [inherited_idents] above) so that
         axiom bodies elaborated against the local get correctly
         substituted to the global by the env-bind machinery. *)
      let inherited_tc_ops, inherited_origins =
        let promoted =
          inherited_idents
          |> List.filter_map (fun (id, n, ty, renamed, origin) ->
               if renamed then Some ((id, ty), (n, origin)) else None) in
        List.split promoted in
      (* User-declared ops get origin [(mypath, name)] — they are the
         canonical source for that op (within this class hierarchy). *)
      let user_origins =
        List.map (fun (id, _ty) ->
          let n = EcIdent.name id in (n, (mypath, n))) operators in

      (* Construct actual type-class *)
      { tc_prts = uptcs; tc_tparams = EcUnify.UniEnv.tparams ue;
        tc_ops = inherited_tc_ops @ operators;
        tc_axs = axioms; tc_loca = lc;
        tc_ops_origin = inherited_origins @ user_origins; }
    in
      bindclass scope (name, tclass)

  (* ------------------------------------------------------------------ *)
  let check_tci_operators env tcty ops reqs =
    (* Each binding [op X = body] is elaborated as a form at the type
       the class declares for [X] (after substituting the instance's
       tparams). The body can be anything well-typed at that type — a
       bare op path, a literal, a lambda — not just a [pqsymbol]. *)
    let ops =
      let tt1 m (x, body) =
        if not (Mstr.mem (unloc x) reqs) then
          hierror ~loc:x.pl_loc "invalid operator name: `%s'" (unloc x);
        Mstr.change
          (function
            | None   -> Some (x.pl_loc, body)
            | Some _ -> hierror ~loc:(x.pl_loc)
              "duplicated operator name: `%s'" (unloc x))
          (unloc x) m
      in
        List.fold_left tt1 Mstr.empty ops
    in
      Mstr.iter
        (fun x (req, _) ->
           if req && not (Mstr.mem x ops) then
             hierror "no definition for operator `%s'" x)
        reqs;
      Mstr.fold
        (fun x (_, ty) m ->
           match Mstr.find_opt x ops with
           | None -> m
           | Some (loc, body) ->
               let ue = EcUnify.UniEnv.create (Some (fst tcty)) in
               let f =
                 try TT.trans_form env ue body ty
                 with TT.TyError (loc, env, e) ->
                   hierror ~loc "%a"
                     (EcUserMessages.TypingError.pp_tyerror env) e
               in
               if not (EcUnify.UniEnv.closed ue) then
                 hierror ~loc
                   "the body of operator `%s' contains free type variables" x;
               let subst =
                 Tuni.subst
                   ~tw_uni:(EcUnify.UniEnv.tw_assubst ue)
                   (EcUnify.UniEnv.assubst ue) in
               let f = Fsubst.f_subst subst f in
               Mstr.add x f m)
        reqs Mstr.empty

  (* ------------------------------------------------------------------ *)
  (* [reqs] is the obligation list: each entry is [(name, labels, form)]
     where [labels] is the label-path from the leaf class to the
     ancestor class introducing this axiom. Multiple obligations may
     share the same [name] if reached through distinct chain paths
     (different [labels]) — typical for [mopA] reached through both
     addmonoid and mulmonoid views.

     [axs] is the user's proof list: each entry is
     [(name, label_qualifier option, tactic)]. The qualifier is a
     [(non-empty) label list] that must appear as a sub-path of an
     obligation's [labels] to match.

     Matching: a user clause [(name, qual, tac)] is matched against
     obligations whose [name] matches and whose [labels] suffix-
     contains [qual] (if [qual = None], require unique match by
     name). Ambiguous = error; missing = error. *)
  let check_tci_axioms ?(tparams = []) scope mode axs reqs lc =
    (* Sub-path containment: [qual] matches [labels] if [qual] occurs
       as a contiguous subsequence of [labels]. A single-element
       qualifier matches any obligation whose path contains that
       label anywhere; multi-element qualifiers match a contiguous
       run. *)
    let labels_match (qual : string list) (labels : string list) =
      let qlen = List.length qual in
      let llen = List.length labels in
      let rec scan i =
        if i + qlen > llen then false
        else
          let slice =
            List.filteri (fun j _ -> j >= i && j < i + qlen) labels in
          if slice = qual then true else scan (i + 1)
      in qlen = 0 || scan 0 in
    (* Match a user clause against the obligation list. Returns the
       matched obligation's [form] and a string identifier for the
       lemma name. Errors on miss or ambiguity. *)
    let match_user_clause (x : psymbol)
        (qual_opt : psymbol list option)
      : EcCoreFol.form =
      let xs = unloc x in
      let qual = Option.map (List.map unloc) qual_opt in
      let candidates =
        List.filter (fun (n, ls, _) ->
          n = xs
          && (match qual with
              | None -> true
              | Some qs -> labels_match qs ls))
          reqs in
      match candidates, qual with
      | [], _ ->
        hierror ~loc:x.pl_loc "invalid axiom name: `%s'" xs
      | [_, _, f], _ -> f
      | _ :: _ :: _, None ->
        hierror ~loc:x.pl_loc
          "ambiguous axiom name `%s' (reached through multiple parent \
           paths). Disambiguate with [<:Label>]." xs
      | _ :: _ :: _, Some _ ->
        hierror ~loc:x.pl_loc
          "ambiguous label qualifier for axiom `%s'. Try a longer \
           label path." xs in

    (* Resolve each user clause to (effective_name, tactic, form).
       Effective name encodes the label path for uniqueness, since
       the same [name] may be discharged twice with different labels. *)
    let resolved =
      List.map (fun (x, qual_opt, t) ->
        let f = match_user_clause x qual_opt in
        let label_tag =
          match qual_opt with
          | None -> ""
          | Some qs ->
            "<:" ^ String.concat "/" (List.map unloc qs) ^ ">" in
        (unloc x ^ label_tag, t, f))
        axs in

    (* Detect duplicate user clauses (same name + same qualifier
       matching the same obligation) by checking effective names. *)
    let () =
      let seen = ref Sstr.empty in
      List.iter (fun (eff, _, _) ->
        if Sstr.mem eff !seen then
          hierror "duplicated proof clause: `%s'" eff;
        seen := Sstr.add eff !seen)
        resolved in

    (* Effective names of all obligations: for unambiguous-by-name
       obligations, the bare name; for ambiguous ones, the
       name<:labels> form. *)
    let oblig_eff_name =
      let by_name =
        List.fold_left (fun m (n, _, _) ->
          Mstr.change (function None -> Some 1 | Some k -> Some (k + 1)) n m)
          Mstr.empty reqs in
      fun (n, ls, _) ->
        match Mstr.find_opt n by_name with
        | Some 1 -> n
        | _ -> n ^ "<:" ^ String.concat "/" ls ^ ">" in

    (* Interactive list: obligations the user did not discharge. *)
    let resolved_names =
      List.fold_left (fun s (n, _, _) -> Sstr.add n s) Sstr.empty resolved in
    let interactive =
      List.pmap
        (fun ((_n, _ls, req) as oblig) ->
          let eff = oblig_eff_name oblig in
          if not (Sstr.mem eff resolved_names) then
            let ax = {
              ax_tparams    = tparams;
              ax_spec       = req;
              ax_kind       = `Lemma;
              ax_loca       = lc;
              ax_smt = false;
            } in Some ((None, ax), EcPath.psymbol eff, scope.sc_env)
          else None)
        reqs in
      List.iter
        (fun (x, pt, f) ->
          let x  = "$" ^ x in
          let t  = { pt_core = pt; pt_intros = []; } in
          let t  = { pl_loc = pt.pl_loc; pl_desc = Pby (Some [t]) } in
          let t  = { pt_core = t; pt_intros = []; } in
          let ax = {
              ax_tparams    = tparams;
              ax_spec       = f;
              ax_kind       = `Lemma;
              ax_smt = false;
              ax_loca       = lc;
          } in

          let pucflags = { puc_smt = true; puc_local = false; } in
          let pucflags = (([], None), pucflags) in
          let check    = Check_mode.check scope.sc_options in

          let escope = scope in
          let escope = Ax.start_lemma escope pucflags check ~name:x (ax, None) in
          let escope = Tactics.proof escope in
          let escope = snd (Tactics.process_r ~reloc:x false mode escope [t]) in
            ignore (Ax.save_r escope))
        resolved;
      interactive

  (* ------------------------------------------------------------------ *)
  let get_ring_field_op (name : string) (symbols : EcCoreFol.form Mstr.t) =
    Option.map
      (fun (f : EcCoreFol.form) ->
        match f.EcAst.f_node with
        | EcAst.Fop (p, tys) -> assert (List.is_empty tys); p
        | _ -> assert false)
      (Mstr.find_opt name symbols)

  let ring_of_symmap env ty kind symbols =
    { r_type  = ty;
      r_zero  = oget (get_ring_field_op "rzero" symbols);
      r_one   = oget (get_ring_field_op "rone"  symbols);
      r_add   = oget (get_ring_field_op "add"   symbols);
      r_opp   =      (get_ring_field_op "opp"   symbols);
      r_mul   = oget (get_ring_field_op "mul"   symbols);
      r_exp   =      (get_ring_field_op "expr"  symbols);
      r_sub   =      (get_ring_field_op "sub"   symbols);
      r_kind  = kind;
      r_embed =
        (match get_ring_field_op "ofint" symbols with
         | None when EcReduction.EqTest.for_type env ty tint -> `Direct
         | None -> `Default | Some p -> `Embed p); }

  let addring ~import (scope : scope) mode (kind, { pl_desc = tci; pl_loc = loc }) =
    let env = env scope in
    if not (EcAlgTactic.is_module_loaded env) then
      hierror "load AlgTactic/Ring first";

    let ty =
      let ue = TT.transtyvars env (loc, Some (fst tci.pti_type)) in
      let ty = transty tp_tydecl env ue (snd tci.pti_type) in
      assert (EcUnify.UniEnv.closed ue);
      let uidmap = EcUnify.UniEnv.close ue in
        (EcUnify.UniEnv.tparams ue, ty_subst (Tuni.subst uidmap) ty)
    in

    if not (List.is_empty (fst ty)) then
      hierror "ring instances cannot be polymorphic";

    let symbols = EcAlgTactic.ring_symbols env kind (snd ty) in
    let symbols = Mstr.of_list symbols in
    let symbols = check_tci_operators env ty tci.pti_ops symbols in
    let cr      = ring_of_symmap env (snd ty) kind symbols in
    let axioms  = EcAlgTactic.ring_axioms env cr in
    let axioms  = List.map (fun (n, f) -> (n, [], f)) axioms in
    let lc      = (tci.pti_loca :> locality) in
    let inter   = check_tci_axioms scope mode tci.pti_axs axioms lc in

    let instance = EcTheory.
      { tci_params       = fst ty
      ; tci_type         = snd ty
      ; tci_instance     = `Ring cr
      ; tci_local        = (tci.pti_loca :> locality)
      ; tci_parents      = []
      ; tci_reducible    = tci.pti_reducible
      ; tci_chain_rename = None
      ; tci_chain_labels = None } in

    let scope =
      let item = EcTheory.Th_instance (None, instance) in
      let item = EcTheory.mkitem ~import item in
      { scope with sc_env = EcSection.add_item item scope.sc_env } in

    Ax.add_defer scope inter

  (* ------------------------------------------------------------------ *)
  let field_of_symmap env ty symbols =
    { f_ring = ring_of_symmap env ty `Integer symbols;
      f_inv  = oget (get_ring_field_op "inv" symbols);
      f_div  = get_ring_field_op "div" symbols; }

  let addfield ~import (scope : scope) mode { pl_desc = tci; pl_loc = loc; } =
    let env = env scope in
    if not (EcAlgTactic.is_module_loaded env) then
      hierror "load AlgTactic/Ring first";

    let ty =
      let ue = TT.transtyvars env (loc, Some (fst tci.pti_type)) in
      let ty = transty tp_tydecl env ue (snd tci.pti_type) in
      assert (EcUnify.UniEnv.closed ue);
      let uidmap = EcUnify.UniEnv.close ue in
        (EcUnify.UniEnv.tparams ue, ty_subst (Tuni.subst uidmap) ty)
    in

    if not (List.is_empty (fst ty)) then
      hierror "field instances cannot be polymorphic";

    let symbols = EcAlgTactic.field_symbols env (snd ty) in
    let symbols = Mstr.of_list symbols in
    let symbols = check_tci_operators env ty tci.pti_ops symbols in
    let cr      = field_of_symmap env (snd ty) symbols in
    let axioms  = EcAlgTactic.field_axioms env cr in
    let axioms  = List.map (fun (n, f) -> (n, [], f)) axioms in
    let lc      = (tci.pti_loca :> locality) in
    let inter   = check_tci_axioms scope mode tci.pti_axs axioms lc; in

    let instance = EcTheory.
      { tci_params       = fst ty
      ; tci_type         = snd ty
      ; tci_instance     = `Field cr
      ; tci_local        = (tci.pti_loca :> locality)
      ; tci_parents      = []
      ; tci_reducible    = tci.pti_reducible
      ; tci_chain_rename = None
      ; tci_chain_labels = None } in

    let scope =
      let item = EcTheory.Th_instance (None, instance) in
      let item = EcTheory.mkitem ~import item in
      { scope with sc_env = EcSection.add_item item scope.sc_env } in
  
    Ax.add_defer scope inter

  (* ------------------------------------------------------------------ *)
  let symbols_of_tc (_env : EcEnv.env) ((tparams, ty) : ty_params * ty) (tcp, tc) =
    (* The instance's tparams are the same idents we'll later resolve
       op-clause RHSs against (via [check_tci_operators], which creates
       a [unienv] seeded with these tparams). Build the substitution
       binding each tparam to itself (with appropriate TC witnesses on
       the original ident) — DO NOT freshen, otherwise the expected op
       type uses [c_fresh] while the resolved op uses the instance's
       [c_orig], and [EqTest.for_type] rejects them as different
       (printing identically as ['a] but with different idents).      *)
    let subst =
      List.fold_left
        (fun s (x, tcs) ->
          let tcw =
            List.mapi (fun i _ ->
              EcAst.TCIAbstract {
                support = `Var x; offset = i; lift = [];
              }) tcs
          in EcSubst.add_tyvar s x (EcTypes.tvar x, tcw))
        EcSubst.empty tparams in
    let subst = EcSubst.add_tydef subst tcp.tc_name ([], ty, []) in
    let subst =
      List.fold_left
        (fun subst (a, ty) -> EcSubst.add_tyvar subst a ty)
        subst (List.combine (List.fst tc.tc_tparams) tcp.tc_args) in

    List.map (fun (x, opty) ->
      (EcIdent.name x, (true, EcSubst.subst_ty subst opty)))
      tc.tc_ops

  (* ------------------------------------------------------------------ *)
  let add_generic_instance
    ~import (scope : scope) mode { pl_desc = tci; pl_loc = loc; }
  =
    let (typarams, _) as ty =
      let ue = TT.transtyvars (env scope) (loc, Some (fst tci.pti_type)) in
      let ty = transty tp_tydecl (env scope) ue (snd tci.pti_type) in
      assert (EcUnify.UniEnv.closed ue);
      (
        EcUnify.UniEnv.tparams ue,
        ty_subst (Tuni.subst (EcUnify.UniEnv.close ue)) ty
      )
    in

    let tcp =
      let ue = EcUnify.UniEnv.create (Some typarams) in
      let tcp = TT.transtc (env scope) ue tci.pti_tc in
      let subst = Tuni.subst (EcUnify.UniEnv.close ue) in
      { tcp with tc_args = List.map (EcCoreSubst.etyarg_subst subst) tcp.tc_args } in

    (* Walk the parent DAG with cumulative op renamings: [(tcp, []);
       (parent_1, ren_1); ...]. The empty renaming on [tcp] is identity:
       each ancestor op [n] maps to a local op [n]. Renamings on parent
       edges (declared via [<: P with { ... }]) compose along the path,
       so a renamed grandparent op resolves to a local op. *)
    let chain = EcTypeClass.ancestors_with_labels (env scope) tcp in
    let chain_decls =
      List.map
        (fun (anc, ren, labels) ->
          (anc, EcEnv.TypeClass.by_path anc.tc_name (env scope), ren, labels))
        chain in

    let lookup_ren ren n = odfl n (Mstr.find_opt n (Mstr.of_list ren)) in

    (* Build the set of expected operators. Immediate-class ops (no
       renaming applied) are required. Ancestor ops are mapped through
       the cumulative renaming to local op names; if an ancestor op's
       local name is already in [tcsyms] (e.g. via the immediate class
       or via another path), keep the existing entry. *)
    let tcsyms =
      match chain_decls with
      | [] -> assert false
      | (tcp_self, tc_self, _, _) :: rest ->
        let immediate = symbols_of_tc (env scope) ty (tcp_self, tc_self) in
        let immediate_set = Sstr.of_list (List.map fst immediate) in
        let parents =
          List.concat_map
            (fun (anc, anc_decl, ren, _labels) ->
              symbols_of_tc (env scope) ty (anc, anc_decl)
              |> List.map (fun (n, (_, opty)) ->
                   (lookup_ren ren n, (false, opty))))
            rest in
        let parents =
          List.filter
            (fun (n, _) -> not (Sstr.mem n immediate_set))
            parents in
        Mstr.of_list (immediate @ parents) in
    let symbols = check_tci_operators (env scope) ty tci.pti_ops tcsyms in

    (* For any ancestor op (after renaming) the user didn't provide,
       look up an existing instance of that ancestor on the same
       carrier and reuse its realisation. *)
    let existing_anc_symbols anc =
      List.fold_left (fun acc (_, tci_existing) ->
        match acc with
        | Some _ -> acc
        | None ->
          match tci_existing.EcTheory.tci_instance with
          | `General (tgp, Some sym)
            when EcPath.p_equal tgp.tc_name anc.tc_name
              && EcReduction.EqTest.for_type
                   (env scope) tci_existing.EcTheory.tci_type (snd ty) ->
              Some sym
          | _ -> None)
        None (EcEnv.TcInstance.get_all (env scope)) in
    let symbols =
      List.fold_left
        (fun symbols (anc, anc_decl, ren, _labels) ->
          let missing =
            List.filter (fun (id, _) ->
              not (Mstr.mem (lookup_ren ren (EcIdent.name id)) symbols))
              anc_decl.tc_ops in
          if missing = [] then symbols
          else
            match existing_anc_symbols anc with
            | None ->
                let id, _ = List.hd missing in
                hierror "no definition for operator `%s'" (EcIdent.name id)
            | Some sym ->
                List.fold_left
                  (fun symbols (id, _) ->
                    let n = EcIdent.name id in
                    let local_n = lookup_ren ren n in
                    match Mstr.find_opt n sym with
                    | Some s -> Mstr.add local_n s symbols
                    | None -> symbols)
                  symbols missing)
        symbols (List.tl chain_decls) in

    (* Phase B coherence check: when a chain entry derives an instance
       of [anc] on the carrier and an instance for the same ancestor
       on the same carrier already exists in scope, the two must
       agree on every op realisation. Catches the case where a user
       declares `instance addgroup with int { ... }` and later
       `instance comring with int { ... }` with conflicting +. *)
    List.iter
      (fun (anc, anc_decl, ren, _labels) ->
        match existing_anc_symbols anc with
        | None -> ()
        | Some existing_sym ->
          List.iter
            (fun (id, _) ->
              let n = EcIdent.name id in
              let local_n = lookup_ren ren n in
              let body_head (f : EcCoreFol.form) =
                match f.EcAst.f_node with
                | EcAst.Fop (p, _) -> Some p
                | EcAst.Fapp ({ f_node = Fop (p, _); _ }, _) -> Some p
                | _ -> None in
              match Mstr.find_opt local_n symbols, Mstr.find_opt n existing_sym with
              | Some f1, Some f2 ->
                begin match body_head f1, body_head f2 with
                | Some p1, Some p2 when not (EcPath.p_equal p1 p2) ->
                  hierror
                    "diamond coherence violation: registering an instance \
                     of `%s' on this carrier requires op `%s' to be `%s', \
                     but an existing instance binds it to `%s'"
                    (EcPath.tostring anc.tc_name)
                    n
                    (EcPath.tostring p1)
                    (EcPath.tostring p2)
                | _ -> ()
                end
              | _ -> ())
            anc_decl.tc_ops)
      chain_decls;

    (* Pre-compute the path each chain entry will receive when it is
       registered as a [Th_instance] below. We need these paths up
       front so the [add_tydef] substitution can reference them as
       concrete witnesses — the inherited axiom bodies use
       [`Abs anc.tc_name; offset = 0] which, in the class body's
       semantics, refers to "the carrier-as-this-class". After
       substituting the carrier with [ty], that needs to point at
       the instance for [ty] of [anc] — i.e. exactly the path we are
       about to register. *)
    (* For each chain entry, first check whether an existing instance in
       the env already realises [(anc, snd ty)] with op-symbols matching
       what this declaration would produce. If so, reuse its path rather
       than register a duplicate (which would diverge witnesses and
       violate one-canonical-instance-per-(class, carrier)). The
       returned [name option] is [None] when reusing — the chain
       registration loop below skips those entries.                      *)
    let find_existing_chain_entry (anc : typeclass) (anc_decl : tc_decl) ren =
      let expected =
        List.fold_left
          (fun m (id, _) ->
            let n = EcIdent.name id in
            let local = lookup_ren ren n in
            match Mstr.find_opt local symbols with
            | Some s -> Mstr.add n s m
            | None -> m)
          Mstr.empty anc_decl.tc_ops in
      let head_path (f : EcCoreFol.form) =
        match f.EcAst.f_node with
        | EcAst.Fop (p, _) -> Some p
        | EcAst.Fapp ({ f_node = Fop (p, _); _ }, _) -> Some p
        | _ -> None in
      let same_value f f' =
        match head_path f, head_path f' with
        | Some p, Some p' -> EcPath.p_equal p p'
        | _ ->
          EcReduction.is_alpha_eq
            (EcEnv.LDecl.init (env scope) []) f f' in
      let same_symbols (existing_syms : EcCoreFol.form Mstr.t) =
        Mstr.for_all
          (fun n f ->
            match Mstr.find_opt n existing_syms with
            | Some f' -> same_value f f'
            | None -> false)
          expected in
      (* Carrier-type comparison must be alpha-equivalent (ignore tparam
         identity), since the existing instance's tparams have their own
         fresh idents that don't match the user's tparams here. Use
         [EcTypeClass.ty_match] with the existing instance's tparams as
         pattern variables.                                              *)
      let same_carrier (tci_existing : EcTheory.tcinstance) =
        try
          let _ : ty option Mid.t =
            EcTypeClass.ty_match (env scope)
              (List.fst tci_existing.EcTheory.tci_params)
              ~pattern:tci_existing.EcTheory.tci_type
              ~ty:(snd ty)
          in true
        with EcTypeClass.NoMatch -> false in
      List.opick
        (fun (path_opt, tci_existing) ->
          match path_opt with
          | None -> None
          | Some p ->
            if    same_carrier tci_existing
               && (match tci_existing.EcTheory.tci_instance with
                   | `General (anc', Some syms) ->
                     EcPath.p_equal anc'.tc_name anc.tc_name
                     && same_symbols syms
                   | _ -> false)
            then Some p else None)
        (EcEnv.TcInstance.get_all (env scope)) in
    let chain_paths_pre =
      List.mapi
        (fun idx (anc, anc_decl, ren, _labels) ->
          match find_existing_chain_entry anc anc_decl ren with
          | Some existing_path -> (None, existing_path)
          | None ->
            let name =
              if idx = 0 then
                match tci.pti_name with
                | Some name -> unloc name
                | None ->
                    Printf.sprintf "%s_%d"
                      (EcPath.basename anc.EcAst.tc_name) (EcUid.unique ())
              else
                Printf.sprintf "%s_%d"
                  (EcPath.basename anc.EcAst.tc_name) (EcUid.unique ()) in
            (Some name, EcPath.pqname (path scope) name))
        chain_decls in

    (* Build a substitution mapping every op-ident along the chain to its
       chosen realisation on [ty]. For each ancestor the renaming maps
       its op names to local op names (via [lookup_ren ren]). *)
    let subst, _ =
      (* The chain may contain entries sharing a TC name (under
         different renamings). [add_tydef] asserts no double-binding,
         so we track which TC names we've already added and skip. *)
      List.fold_lefti
        (fun (subst, seen) idx (anc, anc_decl, ren, _labels) ->
          let seen, subst =
            if EcPath.Sp.mem anc.tc_name seen then (seen, subst)
            else
              (* The class body referenced its carrier as
                 [`Abs anc.tc_name; offset = 0; …] (a self-reference,
                 since [anc]'s own [tcs] contains [anc] itself). After
                 substituting the carrier with [ty], that reference
                 must point to the instance for [ty] of [anc] — which
                 is the chain entry we are about to register. We use
                 its pre-computed path. The [`Abs] case of
                 [subst_tcw] then bumps the body's lift onto this
                 concrete witness, walking [tci_parents] correctly. *)
              let _, inst_path = List.nth chain_paths_pre idx in
              (* For parametric carriers ([instance C with ['a <: …] (T 'a)]),
                 the chain instance is registered with the same tparams as the
                 user's instance. Its witness must therefore re-apply those
                 tparams as etyargs (each carrying its own abstract TC
                 witnesses), not [], or [tc_reduce] will hit a
                 [tci_params]/[etyargs] length mismatch when the instance is
                 later consulted via this witness.                          *)
              let self_etyargs =
                List.map
                  (fun (x, tcs) ->
                    let tcws =
                      List.mapi (fun i _ ->
                        EcAst.TCIAbstract {
                          support = `Var x; offset = i; lift = [];
                        }) tcs
                    in (EcTypes.tvar x, tcws))
                  (fst ty) in
              let self_witness =
                TCIConcrete { path = inst_path; etyargs = self_etyargs; lift = [] } in
              (EcPath.Sp.add anc.tc_name seen,
               EcSubst.add_tydef subst anc.tc_name
                 ([], snd ty, [self_witness])) in
          let subst =
            List.fold_left
              (fun subst (a, ty) -> EcSubst.add_tyvar subst a ty)
              subst
              (List.combine (List.fst anc_decl.tc_tparams) anc.tc_args) in
          let subst =
            List.fold_left
              (fun subst (opname, _ty) ->
                let local = lookup_ren ren (EcIdent.name opname) in
                let body = Mstr.find local symbols in
                let op = EcSubst.subst_form subst body in
                EcSubst.add_flocal subst opname op)
              subst anc_decl.tc_ops in
          (subst, seen))
        (EcSubst.empty, EcPath.Sp.empty) chain_decls in

    let lc    = (tci.pti_loca :> locality) in

    (* Compose two renamings (matches the version in [ecTypeClass.ml]
       which is used to build the chain). [outer] is declared on the
       parent edge; [inner] is the cumulative renaming on this entry.
       Result maps grandparent op names to local op names. *)
    let compose_ren ~outer ~inner =
      let inner_map = Mstr.of_list inner in
      let from_outer =
        List.map
          (fun (gp_name, p_name) ->
            let c_name = odfl p_name (Mstr.find_opt p_name inner_map) in
            (gp_name, c_name))
          outer in
      let outer_p_names =
        List.fold_left (fun s (_, p) -> Sstr.add p s) Sstr.empty outer in
      let outer_gp_names =
        List.fold_left (fun s (gp, _) -> Sstr.add gp s) Sstr.empty outer in
      let from_inner =
        List.filter_map
          (fun (p_name, c_name) ->
            if Sstr.mem p_name outer_p_names || Sstr.mem p_name outer_gp_names
            then None
            else Some (p_name, c_name))
          inner in
      from_outer @ from_inner in
    let ren_eq r1 r2 =
      List.length r1 = List.length r2
      && List.for_all2 (fun (a, b) (c, d) -> a = c && b = d) r1 r2 in

    (* Register one instance per ancestor chain entry, in REVERSE
       BFS order (leaves before children) so that when a child entry
       is registered, its parents' paths are already known. The
       [chain_paths] array uses the pre-computed paths from
       [chain_paths_pre] so that proof-obligation substitutions can
       reference them ahead of registration. We register BEFORE
       [check_tci_axioms] so that the substituted obligation's
       concrete witnesses (which point at these paths) resolve
       through the env when [tc_reduce] fires. *)
    let chain_paths =
      Array.of_list
        (List.map (fun (_, p) -> Some p) chain_paths_pre) in
    let scope =
      List.fold_lefti
        (fun scope rev_idx (anc, anc_decl, ren, labels) ->
          let idx = (List.length chain_decls) - 1 - rev_idx in
          let name_opt, _ = List.nth chain_paths_pre idx in
          match name_opt with
          | None ->
            (* Chain entry reuses an existing instance — don't register
               a duplicate. The pre-existing instance already provides
               this ancestor's ops + axioms, and its path is what
               [chain_paths_pre]/[chain_paths] return for [idx].         *)
            scope
          | Some name ->
          let anc_symbols =
            List.fold_left
              (fun m (id, _) ->
                let n = EcIdent.name id in
                let local = lookup_ren ren n in
                match Mstr.find_opt local symbols with
                | Some s -> Mstr.add n s m
                | None -> m)
              Mstr.empty anc_decl.tc_ops in
          (* Find this entry's parent chain entries: for each parent
             of [anc] (in [anc_decl.tc_prts]), the parent chain entry
             has the same TC and the renaming composed with [ren]. *)
          let parents =
            List.map
              (fun (p_tc, _p_lbl, p_ren) ->
                let target_ren = compose_ren ~outer:p_ren ~inner:ren in
                let rec find i = function
                  | [] -> None
                  | (a, _, r, _l) :: rest ->
                    if EcPath.p_equal a.EcAst.tc_name p_tc.EcAst.tc_name
                       && ren_eq r target_ren
                    then chain_paths.(i)
                    else find (i + 1) rest
                in find 0 chain_decls)
              anc_decl.tc_prts in
          let parents = List.pmap (fun x -> x) parents in
          let instance = EcTheory.
            { tci_params       = fst ty
            ; tci_type         = snd ty
            ; tci_instance     = `General (anc, Some anc_symbols)
            ; tci_local        = lc
            ; tci_parents      = parents
            ; tci_reducible    = tci.pti_reducible
              (* Record the cumulative ancestor->leaf renaming on this
                 chain entry. Used by the resolver's op-name preservation
                 filter to disambiguate multiple monoid views at a
                 concrete carrier (e.g. comring's addmonoid vs
                 mulmonoid-renamed paths to monoid).                 *)
            ; tci_chain_rename = Some ren
              (* Label path: how we reached this ancestor from the leaf
                 class along the chain. Used by the obligation collector
                 at downstream instance time to disambiguate axioms. *)
            ; tci_chain_labels = Some labels } in
          let item = EcTheory.Th_instance (Some name, instance) in
          let item = EcTheory.mkitem ~import item in
          { scope with sc_env = EcSection.add_item item scope.sc_env })
        scope (List.rev chain_decls) in

    (* Auto-skip a chain entry's axioms if a previously-declared
       instance for the same (TC name, carrier) already proves them.
       Symbols-equivalent means: for every op declared in the
       ancestor, both the existing instance and the chain entry's
       expected symbol map agree on the underlying op-path.
       This is what lets [instance addmonoid with int] (with just ops,
       no proofs) succeed when [instance monoid with int] is already
       discharged: addmonoid's monoid-axiom obligations are
       discharged by the existing monoid instance. The chain entries
       we register in this declaration are excluded by path. *)
    (* Only freshly-registered paths count as "self": reused paths
       refer to instances that pre-existed, and we want
       [already_discharged] to count them as the discharger.            *)
    let chain_self_paths =
      List.filter_map
        (fun (name_opt, p) ->
          if Option.is_some name_opt then Some p else None)
        chain_paths_pre
      |> EcPath.Sp.of_list in
    let already_discharged (anc : typeclass) (anc_decl : tc_decl) (ren : _) : bool =
      let expected =
        List.fold_left
          (fun m (id, _) ->
            let n = EcIdent.name id in
            let local = lookup_ren ren n in
            match Mstr.find_opt local symbols with
            | Some s -> Mstr.add n s m
            | None -> m)
          Mstr.empty anc_decl.tc_ops in
      let head_path (f : EcCoreFol.form) =
        match f.EcAst.f_node with
        | EcAst.Fop (p, _) -> Some p
        | EcAst.Fapp ({ f_node = Fop (p, _); _ }, _) -> Some p
        | _ -> None in
      (* Compare two symbol-map values for "same realisation": prefer
         the cheap head-path test (covers the legacy Fop-everywhere
         case); fall back to structural alpha-equivalence for cases
         where one or both sides are literals (e.g. [Fint 1]) or other
         non-Fop forms introduced by Path A's form-valued bindings. *)
      let same_value f f' =
        match head_path f, head_path f' with
        | Some p, Some p' -> EcPath.p_equal p p'
        | _ -> EcReduction.is_alpha_eq
                 (EcEnv.LDecl.init (env scope) []) f f' in
      let same_symbols (existing_syms : EcCoreFol.form Mstr.t) =
        Mstr.for_all
          (fun n f ->
            match Mstr.find_opt n existing_syms with
            | Some f' -> same_value f f'
            | None -> false)
          expected in
      List.exists
        (fun (path_opt, tci) ->
          let is_other =
            match path_opt with
            | Some path -> not (EcPath.Sp.mem path chain_self_paths)
            | None -> true in
          is_other
          && EcReduction.EqTest.for_type
               (env scope) tci.EcTheory.tci_type (snd ty)
          && (match tci.EcTheory.tci_instance with
              | `General (anc', Some syms) ->
                EcPath.p_equal anc'.tc_name anc.tc_name
                && same_symbols syms
              | _ -> false))
        (EcEnv.TcInstance.get_all (env scope)) in

    (* Build the proof-obligation list (deduped by axiom name across
       chain entries) and check the user's tactics against it, now
       that the chain instances are bound in the env so [tc_reduce]
       can walk through their pre-computed paths. *)
    (* Obligation collection: each chain entry contributes its axioms
       under the entry's [labels] path. We DO NOT name-dedupe across
       different label paths — two axioms reaching the same local name
       through distinct paths (e.g. [mopA] from addmonoid view vs
       mulmonoid view) are genuinely distinct obligations and must
       both be discharged.

       Same-(name, form) reached through multiple paths IS deduped
       structurally (alpha-equivalence) — typical when the same
       ancestor sits below multiple intermediate classes in a
       diamond. *)
    let axioms =
      let _, axs =
        List.fold_left
          (fun (acc_keys, acc) (anc, anc_decl, ren, labels) ->
            if already_discharged anc anc_decl ren then (acc_keys, acc)
            else
              List.fold_left
                (fun (acc_keys, acc) (name, ax) ->
                  let f = EcSubst.subst_form subst ax in
                  (* Structural dedup: same name + alpha-equivalent
                     form already emitted is the same obligation
                     reached twice. *)
                  let already =
                    List.exists
                      (fun (n', _, f') ->
                        n' = name
                        && EcReduction.is_alpha_eq
                             (EcEnv.LDecl.init (env scope) []) f f')
                      acc in
                  if already then (acc_keys, acc)
                  else (acc_keys, (name, labels, f) :: acc))
                (acc_keys, acc)
                anc_decl.tc_axs)
          ((), []) chain_decls in
      List.rev axs in
    let inter = check_tci_axioms ~tparams:(fst ty) scope mode tci.pti_axs axioms lc in

    Ax.add_defer scope inter

  (* ------------------------------------------------------------------ *)
  let add_instance
    ?(import = true) (scope : scope) mode ({ pl_desc = tci } as toptci)
  =
    (* The legacy AlgTactic [instance ring/field/bring with T …] uses
       the unqualified names [ring], [field], [bring] as fixed keywords.
       Those names collide with the TC framework's [type class ring]
       and [type class field] (when in scope). Dispatch to
       [add_generic_instance] when the name resolves to a typeclass
       — only fall back to the legacy AlgTactic handlers if no such
       typeclass exists.                                               *)
    let resolves_as_tc () =
      Option.is_some
        (EcEnv.TypeClass.lookup_opt (unloc (fst tci.pti_tc)) (env scope)) in
    match unloc (fst tci.pti_tc) with
    | ([], "bring") when not (resolves_as_tc ()) -> begin
        if EcUtils.is_some tci.pti_args then
          hierror "unsupported-option";
        addring ~import scope mode (`Boolean, toptci)
    end

    | ([], "ring") when not (resolves_as_tc ()) -> begin
      let kind =
        match tci.pti_args with
        | None -> `Integer
        | Some (`Ring (c, p)) ->
            if odfl false (c |> omap (fun c -> c <^ BI.of_int 2)) then
              hierror "invalid coefficient modulus";
            if odfl false (p |> omap (fun p -> p <^ BI.of_int 2)) then
              hierror "invalid power modulus";
            if      opt_equal BI.equal c (Some (BI.of_int 2))
                 && opt_equal BI.equal p (Some (BI.of_int 2))
            then `Boolean
            else `Modulus (c, p)
      in addring ~import scope mode (kind, toptci)
    end

    | ([], "field") when not (resolves_as_tc ()) ->
        addfield ~import scope mode toptci

    | _ ->
        if EcUtils.is_some tci.pti_args then
          hierror "unsupported-option";
        add_generic_instance ~import scope mode toptci
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  open EcTheory

  exception TopScope

  (* ------------------------------------------------------------------ *)
  let bind ?(import = true) (scope : scope) (cth : thloaded) =
    assert (scope.sc_pr_uc = None);
    { scope with
        sc_env = EcSection.add_th ~import cth scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let required (scope : scope) (name : required_info) =
    assert (scope.sc_pr_uc = None);
    List.exists (fun x ->
        if x.rqd_name = name.rqd_name then (
          (* FIXME: raise an error message *)
          assert (x.rqd_digest = name.rqd_digest);
          true)
        else false)
      scope.sc_required

  (* ------------------------------------------------------------------ *)
  let mark_as_direct (scope : scope) (name : symbol) =
    let for1 rq =
      if   rq.rqd_name = name
      then { rq with rqd_direct = true }
      else rq
    in { scope with sc_required = List.map for1 scope.sc_required }

  (* ------------------------------------------------------------------ *)
  let enter ?src:_ (scope : scope) (mode : thmode) (name : symbol) =
    assert (scope.sc_pr_uc = None);
    subscope scope mode name

  (* ------------------------------------------------------------------ *)
  let rec require_loaded (id : required_info) scope =
    if required scope id then
      scope
    else
      match Msym.find_opt id.rqd_name scope.sc_loaded with
      | Some (rth, ids) ->
          let scope = List.fold_right require_loaded ids scope in
          let env   = EcSection.require rth scope.sc_env in
            { scope with
                sc_env      = env;
                sc_required = id :: scope.sc_required; }

      | None -> assert false

  (* ------------------------------------------------------------------ *)
  let update_with_required ~(dst : scope) ~(src : scope) =
    let dst =
      let sc_loaded =
        Msym.union
          (fun _ x y -> assert (x ==(*phy*) y); Some x)
          dst.sc_loaded src.sc_loaded
      in { dst with sc_loaded }
    in List.fold_right require_loaded src.sc_required dst

  (* ------------------------------------------------------------------ *)
  let add_clears clears scope =
    let clears =
      let for1 = function
        | None -> EcEnv.root (env scope)
        | Some { pl_loc = loc; pl_desc = (xs, x) as q } ->
          let xp = EcEnv.root (env scope) in
          let xp = EcPath.pqname (EcPath.extend xp xs) x in
          if is_none (EcEnv.Theory.by_path_opt xp (env scope)) then
            hierror ~loc "unknown theory: `%s`" (string_of_qsymbol q);
          xp
      in List.map for1 clears
    in { scope with sc_clears = scope.sc_clears @ clears }

  (* -------------------------------------------------------------------- *)
  let exit_r ?pempty (scope : scope) =
    match scope.sc_top with
    | None     -> raise TopScope
    | Some sup ->
      let clears   = scope.sc_clears in
      let _, cth, _ = EcSection.exit_theory ?pempty ~clears scope.sc_env in
      let loaded   = scope.sc_loaded in
      let required = scope.sc_required in
      let sup = { sup with sc_loaded = loaded; } in
      ((cth, required), scope.sc_name, sup)

  (* ------------------------------------------------------------------ *)
  let exit ?(import = true) ?(pempty = `ClearOnly) ?(clears =[]) (scope : scope) =
    assert (scope.sc_pr_uc = None);

    let cth = exit_r ~pempty (add_clears clears scope) in
    let ((cth, required), (name, _), scope) = cth in
    let scope = List.fold_right require_loaded required scope in
    let scope = ofold (fun cth scope -> bind ~import scope cth) scope cth in
    (name, scope)

  (* ------------------------------------------------------------------ *)
  let bump_prelude (scope : scope) =
    match scope.sc_prelude with
    | `InPrelude, _ ->
         { scope with sc_prelude = (`InPrelude,
             { pr_env      = env scope;
               pr_required = scope.sc_required; }) }
    | _ -> scope

  (* ------------------------------------------------------------------ *)
  let import (scope : scope) (name : qsymbol) =
    assert (scope.sc_pr_uc = None);

    match EcEnv.Theory.lookup_opt ~mode:`All name (env scope) with
    | None ->
        hierror
          "cannot import the non-existent theory `%s'"
          (string_of_qsymbol name)

    | Some (path, cth) ->
      if cth.cth_mode = `Abstract then
        hierror "cannot import an abstract theory";
      bump_prelude
        { scope with
          sc_env = EcSection.import path scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let export_p scope (p, lc) =
    let item = mkitem ~import:true (EcTheory.Th_export (p, lc)) in
    { scope with sc_env = EcSection.add_item item scope.sc_env }

  let export (scope : scope) (name : qsymbol) =
    assert (scope.sc_pr_uc = None);

    match EcEnv.Theory.lookup_opt ~mode:`All name (env scope) with
    | None ->
        hierror
          "cannot export the non-existent theory `%s'"
          (string_of_qsymbol name)

    | Some (path, cth) ->
      if cth.cth_mode = `Abstract then
        hierror "cannot export an abstract theory";
      (* The section will fix the locality *)
      bump_prelude (export_p scope (path, `Global))

  (* ------------------------------------------------------------------ *)
  let check_end_required scope thname =
    if fst scope.sc_name <> thname then
      hierror "end-of-file while processing external theory %s %s"
        (fst scope.sc_name) thname;
    if scope.sc_pr_uc <> None then
      hierror
        "end-of-file while processing proof %s" (fst scope.sc_name)

  (* -------------------------------------------------------------------- *)
  let require_start (scope : scope) (thname : symbol) (mode : thmode) : scope =
    let new_ = enter (for_loading scope) mode thname `Global in
    { new_ with sc_env = EcSection.astop new_.sc_env }

  let require_finish ?(old : scope option = None) ~(new_ : scope)
      (ri : required_info) : scope =
    let (cth, rqs), (name1, _), new_ = exit_r ~pempty:`No new_ in
    assert (ri.rqd_name = name1);
    let scope =
      { (odfl new_ old) with sc_loaded =
          Msym.add ri.rqd_name (oget cth, rqs) new_.sc_loaded; } in
    bump_prelude (require_loaded ri scope)

  let require (scope : scope) ((name, mode) : required_info * thmode) loader =
    assert (scope.sc_pr_uc = None);

    if required scope name then begin
      if   name.rqd_direct
      then mark_as_direct scope name.rqd_name
      else scope
    end else
      match Msym.find_opt name.rqd_name scope.sc_loaded with
      | Some _ -> require_loaded name scope

      | None ->
        try
          let imported = require_start scope name.rqd_name mode in
          let thname   = fst imported.sc_name in
          let imported = loader imported in
          check_end_required imported thname;
          require_finish ~old:(Some scope) ~new_:imported name
        with e -> begin
          match toperror_of_exn_r e with
          | Some (l, e) when not (EcLocation.isdummy l) ->
              raise (ImportError (Some l, name.rqd_name, e))
          | _ ->
              raise (ImportError (None, name.rqd_name, e))
        end

  let required scope = scope.sc_required

  (* -------------------------------------------------------------------- *)
  let alias (scope : scope) ((name, target) : psymbol * pqsymbol) =
    let thpath = EcEnv.Theory.lookup_opt (unloc target) (env scope) in
    let thpath, _ = ofdfl (fun () ->
      hierror ~loc:(loc target) "unknown theory: %a" pp_qsymbol (unloc target)
    ) thpath in
    let item = EcTheory.mkitem ~import:true (EcTheory.Th_alias (unloc name, thpath)) in

    { scope with sc_env = EcSection.add_item item scope.sc_env }
end

(* -------------------------------------------------------------------- *)
module Section = struct
  module T = EcTheory

  let enter (scope : scope) (name : psymbol option) =
    assert (scope.sc_pr_uc = None);
    { scope with
      sc_env = EcSection.enter_section (omap unloc name) scope.sc_env }

  let exit (scope : scope) (name : psymbol option) =
    let sc_env = EcSection.exit_section (omap unloc name) scope.sc_env in
    { scope with sc_env }
end

(* -------------------------------------------------------------------- *)
module Reduction = struct
  (* FIXME: section -> allow "local" flag *)
  let add_reduction scope (opts, reds) =
    check_state `InTop "hint simplify" scope;

    let rules =
      let for1 idx name =
        let idx  = odfl 0 idx in
        let ax_p = EcEnv.Ax.lookup_path (unloc name) (env scope) in
        let opts = EcTheory.{
          ur_delta  = List.mem `Delta  opts;
          ur_eqtrue = List.mem `EqTrue opts;
        } in

        let red_info =
          EcReduction.User.compile ~opts ~prio:idx (env scope) ax_p in
        (ax_p, opts, Some red_info) in

      let rules = List.map (fun (xs, idx) -> List.map (for1 idx) xs) reds in
      List.flatten rules

    in

    let item = EcTheory.mkitem ~import:true (EcTheory.Th_reduction rules) in
    { scope with sc_env = EcSection.add_item item scope.sc_env }
end

(* -------------------------------------------------------------------- *)
module Cloning = struct
  (* ------------------------------------------------------------------ *)
  open EcTheory
  open EcThCloning

  module C = EcThCloning
  module R = EcTheoryReplay

  (* ------------------------------------------------------------------ *)
  let hooks ~(override_locality : is_local option) : scope R.ovrhooks =
    let thexit sc ~import pempty = snd (Theory.exit ~import ?clears:None ~pempty sc) in
    let add_item scope ~import item =
      let item = EcTheory.mkitem ~import item in
      { scope with
          sc_env = EcSection.add_item ~override_locality item scope.sc_env } in
    { R.henv      = (fun scope -> scope.sc_env);
      R.hadd_item = add_item;
      R.hthenter  = Theory.enter;
      R.hthexit   = thexit;
      R.herr      = (fun ?loc -> hierror ?loc "%s"); }

  let () = subtype_hooks_ref := hooks ~override_locality:None

  (* ------------------------------------------------------------------ *)
  module Options = struct
    open EcTheoryReplay

    let default = { clo_abstract = false; }

    let merge1 opts (b, (x : theory_cloning_option)) =
      match x with
      | `Abstract -> { opts with clo_abstract = b; }

    let merge opts (specs : theory_cloning_options) =
      List.fold_left merge1 opts specs
  end

  (* ------------------------------------------------------------------ *)
  let clone (scope : scope) mode (thcl : theory_cloning) =
    assert (scope.sc_pr_uc = None);

    let { cl_name   = name;
          cl_theory = (opath, oth);
          cl_clone  = ovrds;
          cl_rename = rnms;
          cl_ntclr  = ntclr; }

        = C.clone scope.sc_env thcl in

    let incl  = thcl.pthc_import = Some `Include in
    let opts  = Options.merge Options.default thcl.pthc_opts in

    if thcl.pthc_import = Some `Include && opts.R.clo_abstract then
      hierror "cannot include an abstract theory";
    if thcl.pthc_import = Some `Include && EcUtils.is_some thcl.pthc_name then
      hierror "cannot give an alias to an included clone";

    let cpath = EcEnv.root (env scope) in
    let npath = if incl then cpath else EcPath.pqname cpath name in

    let (proofs, scope) =
      EcTheoryReplay.replay (hooks ~override_locality:thcl.pthc_local)
        ~abstract:opts.R.clo_abstract ~override_locality:thcl.pthc_local ~incl
        ~clears:ntclr ~renames:rnms ~opath ~npath ovrds
        scope (name, oth.cth_items, oth.cth_loca)
    in

    let proofs = List.pmap (fun axc ->
      match axc.C.axc_tac with
      | None ->
          Some (fst_map some axc.C.axc_axiom, axc.C.axc_path, axc.C.axc_env)

      | Some pt ->
          let t = { pt_core = pt; pt_intros = []; } in
          let t = { pl_loc = pt.pl_loc; pl_desc = Pby (Some [t]); } in
          let t = { pt_core = t; pt_intros = []; } in
          let (x, ax) = axc.C.axc_axiom in

          let pucflags = { puc_smt = true; puc_local = false; } in
          let pucflags = (([], None), pucflags) in
          let check    = Check_mode.check scope.sc_options in

          let escope = { scope with sc_env = axc.C.axc_env; } in
          let escope = Ax.start_lemma escope pucflags check ~name:x (ax, None) in
          let escope = Tactics.proof escope in
          let escope = snd (Tactics.process_r ~reloc:x false mode escope [t]) in
            ignore (Ax.save_r escope); None)
      proofs
    in

    let scope =
      thcl.pthc_import |> ofold (fun flag scope ->
        match flag with
        | `Import  ->
          { scope with sc_env = EcSection.import npath scope.sc_env; }
        | `Export  ->
          let item = EcTheory.mkitem ~import:true (Th_export (npath, `Global)) in
          { scope with sc_env = EcSection.add_item item scope.sc_env; }
        | `Include -> scope)
        scope

    in Ax.add_defer scope proofs

end

(* -------------------------------------------------------------------- *)
module Search = struct
  let search (scope : scope) qs =
    let env = env scope in
    let paths =
      let do1 fp =
        match unloc fp with
        | PFident (q, None) -> begin
            match EcEnv.Op.all ~name:q.pl_desc env with
            | [] ->
                hierror ~loc:q.pl_loc "unknown operator: `%s'"
                  (EcSymbols.string_of_qsymbol q.pl_desc)
            | paths -> begin
                let for1 (paths, pts) (p, decl) =
                  match decl.op_kind with
                  | OB_nott nt -> begin
                    let ps  = ref Mid.empty in
                    let ue  = EcUnify.UniEnv.create None in
                    let tip = EcUnify.UniEnv.opentvi ue decl.op_tparams None in
                    let tip = f_subst_init ~tv:(Mid.map fst tip.subst) () in
                    let es  = e_subst tip in
                    let xs  = List.map (snd_map (ty_subst tip)) nt.ont_args in
                    let bd  = EcFol.form_of_expr ~m:(EcIdent.create "&hr") (es nt.ont_body) in
                    let fp  = EcFol.f_lambda (List.map (snd_map EcFol.gtty) xs) bd in

                    match fp.f_node with
                    | Fop (pf, _) -> (pf :: paths, pts)
                    | _ -> (paths, (ps, ue, fp) :: pts)
                  end

                  | _ -> (p :: paths, pts) in

                let paths, pts = List.fold_left for1 ([], []) paths in
                let pts = List.map (fun (ps, ue, fp) -> `ByPattern ((ps, ue), fp)) pts in

                `ByOr (`ByPath (Sp.of_list paths) :: pts)
              end
        end

        | _ ->
          let ps = ref Mid.empty in
          let ue = EcUnify.UniEnv.create None in
          let fp = EcTyping.trans_pattern env ps ue fp in
          `ByPattern ((ps, ue), fp)
      in List.map do1 qs in

    let relevant =
      let get_path r = function `ByPath s -> Sp.union r s | _ -> r in
      List.fold_left get_path Sp.empty paths in

    let search_res = EcSearch.search env paths in
    let search_res = EcSearch.sort relevant search_res in

    let buffer = Buffer.create 0 in
    let fmt    = Format.formatter_of_buffer buffer in
    let ppe    = EcPrinting.PPEnv.ofenv env in

    List.iter (fun (p, ax) ->
      Format.fprintf fmt "%a@." (EcPrinting.pp_axiom ~long:true ppe) (p,ax)
    ) search_res;
    notify scope `Info "%s" (Buffer.contents buffer)

  let locate (scope : scope) ({ pl_desc = name } : pqsymbol) =
    let shorten lk p =
      let rec doit prefix (nm, x) =
        match lk (nm, x) (env scope) with
        | Some (p', _) when EcPath.p_equal p p' ->
            (nm, x)
        | _ -> begin
            match prefix with
            | [] -> (nm, x)
            | n :: prefix -> doit prefix (n :: nm, x)
          end
      in

      let (nm, x) = EcPath.toqsymbol p in
      let nm =
        match nm with
        | top :: nm when top = EcCoreLib.i_top ->
            nm
        | _ -> nm in

      let nm', x' = doit (List.rev nm) ([], x) in
      let plong, pshort = (nm, x), (nm', x') in

      (plong, if plong = pshort then None else Some pshort)
    in

    let buffer = Buffer.create 0 in
    let fmt    = Format.formatter_of_buffer buffer in

    let for_kind section getall shorten =
      let objs = getall ?check:None ?name:(Some name) (env scope) in
      let objs = List.map shorten (List.fst objs) in

      if not (List.is_empty objs) then begin
        Format.fprintf fmt "In section [%s]@\n@\n" section;

        List.iter (fun (long, short) ->
            match short with
            | None ->
                Format.fprintf fmt " - %a@\n"
                  EcSymbols.pp_qsymbol long
            | Some short ->
                Format.fprintf fmt " - %a (shorten name: %a)@\n"
                  EcSymbols.pp_qsymbol long
                  EcSymbols.pp_qsymbol short
          )  objs
      end in

    for_kind "operators" EcEnv.Op.all (shorten EcEnv.Op.lookup_opt);
    for_kind "types"     EcEnv.Ty.all (shorten EcEnv.Ty.lookup_opt);
    for_kind "lemmas"    EcEnv.Ax.all (shorten EcEnv.Ax.lookup_opt);

    Format.pp_print_flush fmt ();

    if Buffer.length buffer = 0 then begin
      Format.fprintf fmt
        "no objects found for `%a'"
        EcSymbols.pp_qsymbol name
    end;

    notify scope `Info "%s" (Buffer.contents buffer)
end


(* -------------------------------------------------------------------- *)
module DocComment = struct
  let add (scope : scope) ((_, _) : [`Global | `Item] * string) : scope =
    scope
end
