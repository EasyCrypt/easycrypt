(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcLocation
open EcPath
open EcParsetree
open EcTypes
open EcDecl
open EcModules
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

  let flags = [
    (implicits, false);
    (oldip    , true );
    (redlogic , true );
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
  puc_cont   : proof_ctxt list * (EcEnv.env option);
  puc_init   : EcEnv.env;
}

and proof_auc = {
  puc_name   : symbol option;
  puc_mode   : bool option;
  puc_jdg    : proof_state;
  puc_flags  : pucflags;
  puc_crt    : EcDecl.axiom;
}

and proof_ctxt =
  (symbol option * EcDecl.axiom) * EcPath.path * EcEnv.env

and proof_state =
  PSNoCheck | PSCheck of EcCoreGoal.proof

and pucflags = {
  puc_nosmt : bool;
  puc_local : bool;
}

(* -------------------------------------------------------------------- *)
type required_info = {
  rqd_name      : symbol;
  rqd_namespace : EcLoader.namespace option;
  rqd_kind      : EcLoader.kind;
  rqd_digest    : Digest.t;
}

type required = required_info list

type prelude = {
  pr_env      : EcEnv.env;
  pr_required : required;
}

type thloaded = (EcTheory.ctheory * EcTheory.thmode)

type scope = {
  sc_name     : (symbol * EcTheory.thmode);
  sc_env      : EcEnv.env;
  sc_top      : scope option;
  sc_prelude  : ([`Frozen | `InPrelude] * prelude);
  sc_loaded   : (thloaded * required) Msym.t;
  sc_required : required;
  sc_clears   : path list;
  sc_pr_uc    : proof_uc option;
  sc_options  : GenOptions.options;
  sc_section  : EcSection.t;
}

(* -------------------------------------------------------------------- *)
let empty (gstate : EcGState.gstate) =
  let env = EcEnv.initial gstate in
  { sc_name       = (EcPath.basename (EcEnv.root env), `Concrete);
    sc_env        = env;
    sc_top        = None;
    sc_prelude    = (`InPrelude, { pr_env = env; pr_required = []; });
    sc_loaded     = Msym.empty;
    sc_required   = [];
    sc_clears     = [];
    sc_pr_uc      = None;
    sc_options    = GenOptions.freeze ();
    sc_section    = EcSection.initial; }

(* -------------------------------------------------------------------- *)
let gstate (scope : scope) =
  EcEnv.gstate scope.sc_env

(* -------------------------------------------------------------------- *)
let name (scope : scope) =
  scope.sc_name

(* -------------------------------------------------------------------- *)
let path (scope : scope) =
  EcEnv.root scope.sc_env

(* -------------------------------------------------------------------- *)
let env (scope : scope) =
  scope.sc_env

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
  try  EcSmt.dump_why3 scope.sc_env filename
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
  EcEnv.notify scope.sc_env lvl

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
    sc_env        = env;
    sc_top        = None;
    sc_prelude    = scope.sc_prelude;
    sc_loaded     = scope.sc_loaded;
    sc_required   = pr.pr_required;
    sc_clears     = [];
    sc_pr_uc      = None;
    sc_options    = GenOptions.for_loading scope.sc_options;
    sc_section    = EcSection.initial; }

(* -------------------------------------------------------------------- *)
let subscope (scope : scope) (mode : EcTheory.thmode) (name : symbol) =
  let env = EcEnv.Theory.enter name scope.sc_env in

  { sc_name       = (name, mode);
    sc_env        = env;
    sc_top        = Some scope;
    sc_prelude    = scope.sc_prelude;
    sc_loaded     = scope.sc_loaded;
    sc_required   = scope.sc_required;
    sc_clears     = [];
    sc_pr_uc      = None;
    sc_options    = GenOptions.for_subscope scope.sc_options;
    sc_section    = scope.sc_section; }

(* -------------------------------------------------------------------- *)
let maybe_add_to_section scope item =
  match EcSection.opath scope.sc_section with
  | None -> scope
  | Some (_, sp) -> begin
      match EcPath.p_equal sp (EcEnv.root scope.sc_env) with
      | false -> scope
      | true  ->
        let ec = EcSection.add_item item scope.sc_section in
          { scope with sc_section = ec }
  end

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
    pl_iterate    : bool option;
    pl_wanted     : EcProvers.hints option;
    pl_unwanted   : EcProvers.hints option;
    pl_selected   : bool option;
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
    pl_iterate   = None;
    pl_wanted    = None;
    pl_unwanted  = None;
    pl_selected  = None;
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
      pl_iterate   = ppr.plem_iterate;
      pl_wanted    = omap (process_dbhint env) ppr.plem_wanted;
      pl_unwanted  = omap (process_dbhint env) ppr.plem_unwanted;
      pl_selected  = ppr.plem_selected;
    }

  (* -------------------------------------------------------------------- *)
  let mk_prover_info scope options =
    let open EcProvers in

    let dft          = Prover_info.get scope.sc_options in
    let pr_maxprocs  = odfl dft.pr_maxprocs options.po_nprovers in
    let pr_timelimit = max 0 (odfl dft.pr_timelimit options.po_timeout) in
    let pr_cpufactor = max 0 (odfl dft.pr_cpufactor options.po_cpufactor) in
    let pr_verbose   = max 0 (odfl dft.pr_verbose options.po_verbose) in
    let pr_all       = odfl dft.pr_all options.pl_all in
    let pr_max       = odfl dft.pr_max options.pl_max in
    let pr_iterate   = odfl dft.pr_iterate options.pl_iterate in
    let pr_wanted    = odfl dft.pr_wanted options.pl_wanted in
    let pr_unwanted  = odfl dft.pr_unwanted options.pl_unwanted in
    let pr_selected  = odfl dft.pr_selected options.pl_selected in
    let pr_quorum    = max 1 (odfl dft.pr_quorum options.po_quorum) in
    let pr_provers   =
      let l = odfl dft.pr_provers (fst options.po_provers) in
      let do_ar l (k, p) =
        match k with
        | `Exclude -> List.remove_all l p
        | `Include -> if List.exists ((=) p) l then l else p::l
      in List.fold_left do_ar l (snd options.po_provers) in

    { pr_maxprocs; pr_provers ; pr_timelimit; pr_cpufactor;
      pr_verbose ; pr_all     ; pr_max      ; pr_iterate  ;
      pr_wanted  ; pr_unwanted; pr_selected ; pr_quorum  ; }

  (* -------------------------------------------------------------------- *)
  let do_prover_info scope ppr =
    let options = process_prover_option scope.sc_env ppr in
    mk_prover_info scope options

  (* -------------------------------------------------------------------- *)
  let process scope ppr =
    let pi = do_prover_info scope ppr in
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

  let pi scope pi = Prover.do_prover_info scope pi

  let proof (scope : scope) mode (strict : bool) =
    check_state `InActiveProof "proof script" scope;

    match (oget scope.sc_pr_uc).puc_active with
    | None -> hierror "no active lemmas"
    | Some (pac, pct) ->
      let pac =
        match pac.puc_mode with
        | None when not strict && mode = `WeakCheck -> begin
            match pac.puc_jdg with
            | PSNoCheck -> { pac with puc_mode = Some false; }
            | PSCheck _ ->
                let pac = { pac with puc_jdg = PSNoCheck } in
                  { pac with puc_mode = Some false; }
        end

        | None   -> { pac with puc_mode = Some strict }
        | Some _ -> hierror "[proof] can only be used at beginning of a proof script"
      in
        { scope with sc_pr_uc =
            Some { (oget scope.sc_pr_uc) with puc_active = Some (pac, pct); } }

  let process_r ?reloc mark mode (scope : scope) (tac : ptactic list) =
    check_state `InProof "proof script" scope;

    let scope =
      match (oget scope.sc_pr_uc).puc_active with
      | None -> hierror "no active lemma"
      | Some (pac, _) ->
          if   mark && pac.puc_mode = None
          then proof scope mode true
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
          match pac.puc_mode, mode with
          | Some true , `WeakCheck -> `Admit
          | _         , `WeakCheck ->
               hierror "cannot weak-check a non-strict proof script"
          | Some true , `Check     -> `Strict
          | Some false, `Check     -> `Standard
          | None      , `Check     -> `Strict
          | Some true , `Report    -> `Report
          | Some false, `Report    -> `Standard
          | None      , `Report    -> `Report
        in

        let ttenv = {
          EcHiGoal.tt_provers    = pi scope;
          EcHiGoal.tt_smtmode    = htmode;
          EcHiGoal.tt_implicits  = Options.get_implicits scope;
          EcHiGoal.tt_oldip      = Options.get_oldip scope;
          EcHiGoal.tt_redlogic   = Options.get_redlogic scope; } in

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

  let process scope mode tac =
    process_r true mode scope tac
end

(* -------------------------------------------------------------------- *)
module Auto = struct
  let add_rw scope ~local ~base l =
    let env = env scope in

    if local then
      hierror "rewrite hints cannot be local";

    let env, base =
      match EcEnv.BaseRw.lookup_opt base.pl_desc env with
      | None ->
        let pre, ibase = unloc base in
        if not (List.is_empty pre) then
          hierror ~loc:base.pl_loc
            "cannot create rewrite hints out of its enclosing theory";
        let env = EcEnv.BaseRw.add ibase env in
        (env, fst (EcEnv.BaseRw.lookup base.pl_desc env))

      | Some (base, _) -> (env, base) in

    let l = List.map (fun l -> EcEnv.Ax.lookup_path (unloc l) env) l in
    { scope with sc_env = EcEnv.BaseRw.addto base l env }

  let bind_hint scope ~local ~level ?base names =
    { scope with sc_env =
        EcEnv.Auto.add ~local ~level ?base names scope.sc_env }

  let add_hint scope hint =
    let base = omap unloc hint.ht_base in

    let names = List.map
      (fun l -> EcEnv.Ax.lookup_path (unloc l) scope.sc_env)
      hint.ht_names in

    bind_hint scope ~local:hint.ht_local ~level:hint.ht_prio ?base names
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  open EcParsetree
  open EcDecl

  module TT = EcTyping

  type mode = [`WeakCheck | `Check | `Report]

  (* ------------------------------------------------------------------ *)
  let bind (scope : scope) local ((x, ax) : _ * axiom) =
    assert (scope.sc_pr_uc = None);
    let scope = { scope with sc_env = EcEnv.Ax.bind x ax scope.sc_env; } in
    let scope = maybe_add_to_section scope (EcTheory.CTh_axiom (x, ax)) in
    let scope =
      match EcSection.opath scope.sc_section with
      | None -> scope
      | Some _ ->
          let lvl1 = if local then `Local else `Global in
          let lvl2 = if is_axiom ax.ax_kind then `Axiom else `Lemma in

          if lvl2 = `Axiom && ax.ax_tparams <> [] then
            hierror "axiom must be monomorphic in sections";

          let axpath = EcPath.pqname (path scope) x in
          let ec = EcSection.add_lemma axpath (lvl1, lvl2) scope.sc_section in
            { scope with sc_section = ec }
    in
      scope

  (* ------------------------------------------------------------------ *)
  let start_lemma scope (cont, axflags) check ?name (axd, ctxt) =
    let puc =
      match check with
      | false -> PSNoCheck
      | true  ->
          let hyps  = EcEnv.LDecl.init scope.sc_env axd.ax_tparams in
          let proof = EcCoreGoal.start hyps axd.ax_spec in
          PSCheck proof
    in
    let puc =
      { puc_active = Some ({
          puc_name  = name;
          puc_mode  = None;
          puc_jdg   = puc;
          puc_flags = axflags;
          puc_crt   = axd; }, ctxt);
        puc_cont = cont;
        puc_init = scope.sc_env; }
    in
      { scope with sc_pr_uc = Some puc }

  (* ------------------------------------------------------------------ *)
  let rec add_r (scope : scope) (mode : mode) (ax : paxiom located) =
    assert (scope.sc_pr_uc = None);

    let loc = ax.pl_loc and ax = ax.pl_desc in
    let ue  = TT.transtyvars scope.sc_env (loc, ax.pa_tyvars) in

    if ax.pa_local && not (EcSection.in_section scope.sc_section) then
      hierror "cannot declare a local lemma outside of a section";

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

    let concl = TT.trans_prop scope.sc_env ue pconcl in

    if not (EcUnify.UniEnv.closed ue) then
      hierror "the formula contains free type variables";

    let concl   = EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) concl in
    let tparams = EcUnify.UniEnv.tparams ue in

    let axd  =
      let kind =
        match ax.pa_kind with
        | PAxiom tags -> `Axiom (Ssym.of_list (List.map unloc tags), false)
        | _ -> `Lemma

      in { ax_tparams = tparams;
           ax_spec    = concl;
           ax_kind    = kind;
           ax_nosmt   = ax.pa_nosmt; }
    in

    let check    = Check_mode.check scope.sc_options in
    let pucflags = { puc_nosmt = ax.pa_nosmt; puc_local = ax.pa_local; } in
    let pucflags = (([], None), pucflags) in

    if not ax.pa_local then begin
      match EcSection.olocals scope.sc_section with
      | None -> ()
      | Some locals ->
        match EcSection.form_use_local concl locals with
        | Some mp ->
          let ppe = EcPrinting.PPEnv.ofenv scope.sc_env in
          hierror "@[<hov>this lemma uses local modules : %a@\n and must be declared as local@]" (EcPrinting.pp_topmod ppe) mp
        | None -> ()
      end;

    if ax.pa_local && EcDecl.is_axiom axd.ax_kind then
      hierror "an axiom cannot be local";

    match ax.pa_kind with
    | PILemma ->
        let scope =
          start_lemma scope ~name:(unloc ax.pa_name)
            pucflags check (axd, None) in
        let scope = snd (Tactics.process1_r false `Check scope tintro) in
        None, scope

    | PLemma tc ->
        start_lemma_with_proof scope
          (Some tintro) pucflags (mode, mk_loc loc tc) check
          ~name:(unloc ax.pa_name) axd

    | PAxiom _ ->
        Some (unloc ax.pa_name),
        bind scope (snd pucflags).puc_local (unloc ax.pa_name, axd)

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
            let bind name scope =
              bind scope pac.puc_flags.puc_local (name, pac.puc_crt)
            in pac.puc_name |> ofold bind scope

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
    let scope = Tactics.proof scope mode (if tc = None then true else false) in

    let tc =
      match tc with
      | Some tc -> tc
      | None    ->
          let dtc = Plogic (Psmt empty_pprover) in
          let dtc = { pl_loc = loc; pl_desc = dtc } in
          let dtc = { pt_core = dtc; pt_intros = []; } in
          [dtc]
    in

    let tc = { pl_loc = loc; pl_desc = Pby (Some tc) } in
    let tc = { pt_core = tc; pt_intros = []; } in

    let _, scope = Tactics.process_r false mode scope [tc] in
    save_r scope

  (* ------------------------------------------------------------------ *)
  let save scope =
    check_state `InProof "save" scope;
    save_r ~mode:`Save scope

  (* ------------------------------------------------------------------ *)
  let admit scope =
    check_state `InProof "admitted" scope;
    save_r ~mode:`Admit scope

  (* ------------------------------------------------------------------ *)
  let abort scope =
    check_state `InProof "abort" scope;
    snd (save_r ~mode:`Abort scope)

  (* ------------------------------------------------------------------ *)
  let add (scope : scope) (mode : mode) (ax : paxiom located) =
    add_r scope mode ax

  (* ------------------------------------------------------------------ *)
  let realize (scope : scope) (mode : mode) (rl : prealize located) =
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
    let pucflags = { puc_nosmt = ax.ax_nosmt; puc_local = false; } in
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
  module TTC = EcProofTyping
  module EHI = EcHiInductive

  let bind (scope : scope) ((x, op) : _ * operator) =
    assert (scope.sc_pr_uc = None);

    (match EcSection.olocals scope.sc_section with
     | None -> ()
     | Some locals ->
        if EcSection.opdecl_use_local_or_abs op locals then
          hierror "operators cannot use local/abstracts modules");

    let scope = { scope with sc_env = EcEnv.Op.bind x op scope.sc_env } in
    let scope = maybe_add_to_section scope (EcTheory.CTh_operator (x, op)) in
      scope

  let add (scope : scope) (op : poperator located) =
    assert (scope.sc_pr_uc = None);
    let op = op.pl_desc and loc = op.pl_loc in
    let ue = TT.transtyvars scope.sc_env (loc, op.po_tyvars) in

    let (ty, body, refts) =
      match op.po_def with
      | PO_abstr pty ->
          let env   = scope.sc_env in
          let codom = TT.transty TT.tp_relax env ue pty in
          let xs    = snd (TT.trans_binding env ue op.po_args) in
          (EcTypes.toarrow (List.map snd xs) codom, `Abstract, [])

      | PO_concr (pty, pe) ->
          let env     = scope.sc_env in
          let codom   = TT.transty TT.tp_relax env ue pty in
          let env, xs = TT.trans_binding env ue op.po_args in
          let body    = TT.transexpcast env `InOp ue codom pe in
          let lam     = EcTypes.e_lam xs body in
          (lam.EcTypes.e_ty, `Plain lam, [])

      | PO_case (pty, pbs) -> begin
          let name = { pl_loc = loc; pl_desc = unloc op.po_name } in
          match EHI.trans_matchfix (env scope) ue name (op.po_args, pty, pbs) with
          | (ty, opinfo) -> (ty, `Fix opinfo, [])
      end

      | PO_reft (pty, (rname, reft)) ->
          let env      = scope.sc_env in
          let codom    = TT.transty TT.tp_relax env ue pty in
          let _env, xs = TT.trans_binding env ue op.po_args in
          let opty     = EcTypes.toarrow (List.map snd xs) codom in
          let opabs    = EcDecl.mk_op [] codom None in
          let openv    = EcEnv.Op.bind (unloc op.po_name) opabs env in
          let openv    = EcEnv.Var.bind_locals xs openv in
          let reft     = TT.trans_prop openv ue reft in
          (opty, `Abstract, [(rname, xs, reft, codom)])
    in

    if not (EcUnify.UniEnv.closed ue) then
      hierror ~loc "this operator type contains free type variables";

    let nosmt = op.po_nosmt in

    if nosmt &&
       (match body with
        | `Plain _  -> false
        | `Fix _    -> false
        | `Abstract ->
            match refts with
            | [] -> true
            | _  -> false) then
      hierror ~loc ("[nosmt] is not supported for pure abstract operators");

    let uni     = Tuni.offun (EcUnify.UniEnv.close ue) in
    let ty      = uni ty in
    let tparams = EcUnify.UniEnv.tparams ue in
    let body    =
      match body with
      | `Abstract -> None
      | `Plain e  -> Some (OP_Plain (e_mapty uni e, nosmt))
      | `Fix opfx ->
          Some (OP_Fix {
            opf_args     = opfx.EHI.mf_args;
            opf_resty    = opfx.EHI.mf_codom;
            opf_struct   = (opfx.EHI.mf_recs, List.length opfx.EHI.mf_args);
            opf_branches = opfx.EHI.mf_branches;
            opf_nosmt    = nosmt;
          })

    in

    let tyop   = EcDecl.mk_op tparams ty body in
    let opname = EcPath.pqname (EcEnv.root (env scope)) (unloc op.po_name) in

    if op.po_kind = `Const then begin
      let tue   = EcUnify.UniEnv.copy ue in
      let ty, _ = EcUnify.UniEnv.openty tue tparams None ty in
      let tdom  = EcUnify.UniEnv.fresh tue in
      let tcom  = EcUnify.UniEnv.fresh tue in
      let tfun  = EcTypes.tfun tdom tcom in

        try
          EcUnify.unify (env scope) tue ty tfun;
          let msg = "this operator type is (unifiable) to a function type" in
            hierror ~loc "%s" msg
        with EcUnify.UnificationFailure _ -> ()
    end;

    let scope =
      match op.po_ax with
      | None    -> bind scope (unloc op.po_name, tyop)
      | Some ax -> begin
          match tyop.op_kind with
          | OB_oper (Some (OP_Plain (bd, _))) ->
              let path  = EcPath.pqname (path scope) (unloc op.po_name) in
              let axop  =
                let nosmt = op.po_nosmt in
                let nargs = List.sum (List.map (List.length |- fst) op.po_args) in
                  EcDecl.axiomatized_op ~nargs  ~nosmt path (tyop.op_tparams, bd) in
              let tyop  = { tyop with op_kind = OB_oper None; } in
              let scope = bind scope (unloc op.po_name, tyop) in
              Ax.bind scope false (unloc ax, axop)

          | _ -> hierror ~loc "cannot axiomatize non-plain operators"
      end
    in

    let scope =
      List.fold_left (fun scope (rname, xs, ax, codom) ->
          let ax = f_forall (List.map (snd_map gtty) xs) ax in
          let ax =
            let opargs  = List.map (fun (x, xty) -> e_local x xty) xs in
            let opapp   = List.map (tvar |- fst) tparams in
            let opapp   = e_app (e_op opname opapp ty) opargs codom in
            let tyuni   = { ty_subst_id with ts_u = EcUnify.UniEnv.close ue } in
            let subst   = Mp.singleton opname ([], opapp) in
            let subst   = Fsubst.f_subst_init ~sty:tyuni ~opdef:subst () in
            Fsubst.f_subst subst ax
          in

          let ax, axpm =
            let bdpm = List.map fst tparams in
            let axpm = List.map EcIdent.fresh bdpm in
              (EcCoreFol.Fsubst.subst_tvar
                 (EcTypes.Tvar.init bdpm (List.map EcTypes.tvar axpm))
                 ax,
               List.combine axpm (List.map snd tparams)) in
          let ax =
            { ax_tparams = axpm;
              ax_spec    = ax;
              ax_kind    = `Axiom (Ssym.empty, false);
              ax_nosmt   = nosmt; }
          in Ax.bind scope false (unloc rname, ax))
        scope refts
    in

    let scope =
      if not (List.is_empty op.po_aliases) then begin
        if not (EcUtils.is_none body) || not (List.is_empty refts) then
          hierror ~loc
            "multiple names are only allowed for non-refined abstract operators";
        let addnew scope name =
          let nparams = List.map (fst_map EcIdent.fresh) tparams in
          let subst = Tvar.init
            (List.map fst tparams)
            (List.map (tvar |- fst) nparams) in
          let op = EcDecl.mk_op nparams (Tvar.subst subst ty) None in
          bind scope (unloc name, op)
        in List.fold_left addnew scope op.po_aliases

      end else scope
    in

    let tags = Sstr.of_list (List.map unloc op.po_tags) in

    let add_distr_tag
        (pred : path) (bases : string list) (tag : string) (suffix : string) scope
    =
      if not (EcAlgTactic.is_module_loaded scope.sc_env) then
        hierror "for tag %s, load Distr first" tag;

      let oppath   = EcPath.pqname (path scope) (unloc op.po_name) in
      let nparams  = List.map (EcIdent.fresh |- fst) tyop.op_tparams in
      let subst    = Tvar.init (List.fst tyop.op_tparams) (List.map tvar nparams) in
      let ty       = Tvar.subst subst tyop.op_ty in
      let aty, rty = EcTypes.tyfun_flat ty in

      let dty =
        match EcTypes.as_tdistr (EcEnv.ty_hnorm rty (env scope)) with
        | None -> hierror ~loc "[lossless] can only be applied to distributions"
        | Some dty -> dty
      in

      let bds = List.combine (List.map EcTypes.fresh_id_of_ty aty) aty in
      let ax  = EcFol.f_op oppath (List.map tvar nparams) rty in
      let ax  = EcFol.f_app ax (List.map (curry f_local) bds) rty in
      let ax  = EcFol.f_app (EcFol.f_op pred [dty] (tfun rty tbool)) [ax] tbool in
      let ax  = EcFol.f_forall (List.map (snd_map gtty) bds) ax in

      let ax =
        { ax_tparams = List.map (fun ty -> (ty, Sp.empty)) nparams;
          ax_spec    = ax;
          ax_kind    = `Axiom (Ssym.empty, false);
          ax_nosmt   = false; } in

      let scope, axname =
        let axname = Printf.sprintf "%s_%s" (unloc op.po_name) suffix in
        (Ax.bind scope false (axname, ax), axname) in

      let axpath = EcPath.pqname (path scope) axname in

      List.fold_left
        (fun scope base ->
            Auto.bind_hint ~local:false ~level:0 ~base scope [axpath])
        scope bases

    in

    let scope =
      if   Sstr.mem "lossless" tags
      then add_distr_tag EcCoreLib.CI_Distr.p_lossless
             [EcCoreLib.base_ll] "lossless" "ll" scope
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

    tyop, scope
end

(* -------------------------------------------------------------------- *)
module Pred = struct
  module TT = EcTyping

  let add (scope : scope) (pr : ppredicate located) =
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

  let add_local_restr env path m =
    let mpath = EcPath.pqname path m.me_name in
    match m.me_body with
    | ME_Alias _ | ME_Decl _ -> env
    | ME_Structure _ ->
      (* We keep only the internal part, i.e the inner global variables *)
      (* TODO : using mod_use here to compute the set of inner global
         variables is inefficient, change this algo *)
      let mp = EcPath.mpath_crt mpath [] None in
      let use = EcEnv.NormMp.mod_use env mp in
      let rx =
        let add x _ rx =
          if EcPath.m_equal (EcPath.m_functor x.EcPath.x_top) mp then
            Sx.add x rx
          else rx in
        Mx.fold add use.EcEnv.us_pv EcPath.Sx.empty in
      EcEnv.Mod.add_restr_to_locals (rx,EcPath.Sm.empty) env

  let bind (scope : scope) (local : bool) (m : module_expr) =
    assert (scope.sc_pr_uc = None);
    let scope =
      { scope with
          sc_env = EcEnv.Mod.bind m.me_name m scope.sc_env; }
    in
    let scope = maybe_add_to_section scope (EcTheory.CTh_module m) in
    let scope =
      match local with
      | false -> scope
      | true  ->
        let mpath = EcPath.pqname (path scope) m.me_name in
        let env = add_local_restr scope.sc_env (path scope) m in
        let ec = EcSection.add_local_mod mpath scope.sc_section in
        { scope with sc_section = ec; sc_env = env }
    in
      scope

  let add (scope : scope) (ptm : pmodule_def) =
    assert (scope.sc_pr_uc = None);

    if ptm.ptm_local && not (EcSection.in_section scope.sc_section) then
      hierror "cannot declare a local module outside of a section";

    let m = TT.transmod scope.sc_env ~attop:true ptm in

    if not ptm.ptm_local then begin
      match EcSection.olocals scope.sc_section with
      | None -> ()
      | Some locals ->
          if EcSection.module_use_local_or_abs m locals then
            hierror
              "this module uses local/abstracts modules and
               must be declared as local";
    end;

    let ur = EcModules.get_uninit_read_of_module (path scope) m in

    if not (List.is_empty ur) then begin
      let ppe = EcPrinting.PPEnv.ofenv (env scope) in
      let pp fmt (xp, names) =
        Format.fprintf fmt "  - %a -> [%a]"
          (EcPrinting.pp_funname ppe) (xastrip xp)
          (EcPrinting.pp_list ", " pp_symbol)
          (List.map EcPath.xbasename (Sx.ntr_elements names))
      in

      notify scope `Warning
        "these procedures may use uninitialized local variables:@\n@[<v>%a@]"
        (EcPrinting.pp_list "@," pp) ur
    end;

    bind scope ptm.ptm_local m

  let declare (scope : scope) m =
    if not (EcSection.in_section scope.sc_section) then
      hierror "cannot declare an abstract module outside of a section";

    let modty = m.ptmd_modty in
    let tysig = fst (TT.transmodtype scope.sc_env (fst modty)) in
    let restr = List.map (TT.trans_topmsymbol scope.sc_env) (snd modty) in
    let name  = EcIdent.create (unloc m.ptmd_name) in
    let scope =
      let restr = Sx.empty, Sm.of_list restr in
      { scope with
          sc_env = EcEnv.Mod.declare_local
            name tysig restr scope.sc_env;
          sc_section = EcSection.add_abstract
            name (tysig, restr) scope.sc_section }
    in
      scope
end

(* -------------------------------------------------------------------- *)
module ModType = struct
  let bind (scope : scope) ((x, tysig) : _ * module_sig) =
    assert (scope.sc_pr_uc = None);
    let scope =
      { scope with
          sc_env = EcEnv.ModTy.bind x tysig scope.sc_env; }
    in
    let scope = maybe_add_to_section scope (EcTheory.CTh_modtype (x, tysig)) in
      scope

  let add (scope : scope) (name : symbol) (i : pmodule_sig) =
    assert (scope.sc_pr_uc = None);
    let tysig = EcTyping.transmodsig scope.sc_env name i in
      bind scope (name, tysig)
end

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
  let bind (scope : scope) ((x, tydecl) : (_ * tydecl)) =
    assert (scope.sc_pr_uc = None);

    (match EcSection.olocals scope.sc_section with
     | None -> ()
     | Some locals ->
        if EcSection.tydecl_use_local_or_abs tydecl locals then
          hierror "types cannot use local/abstracts modules");

    let scope = { scope with sc_env = EcEnv.Ty.bind x tydecl scope.sc_env; } in
    let scope = maybe_add_to_section scope (EcTheory.CTh_type (x, tydecl)) in
      scope

  (* ------------------------------------------------------------------ *)
  let add (scope : scope) info tcs =
    assert (scope.sc_pr_uc = None);

    let (args, name) = info.pl_desc and loc = info.pl_loc in
    let tcs =
      List.map
        (fun tc -> fst (EcEnv.TypeClass.lookup (unloc tc) scope.sc_env))
        tcs
    in
    let ue = TT.transtyvars scope.sc_env (loc, Some args) in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = `Abstract (Sp.of_list tcs);
    } in
      bind scope (unloc name, tydecl)

  (* ------------------------------------------------------------------ *)
  let define (scope : scope) info body =
    assert (scope.sc_pr_uc = None);
    let (args, name) = info.pl_desc and loc = info.pl_loc in
    let ue     = TT.transtyvars scope.sc_env (loc, Some args) in
    let body   = transty tp_tydecl scope.sc_env ue body in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = `Concrete body;
    } in
      bind scope (unloc name, tydecl)

  (* ------------------------------------------------------------------ *)
  let bindclass (scope : scope) (x, tc) =
    assert (scope.sc_pr_uc = None);
    let scope = { scope with sc_env = EcEnv.TypeClass.bind x tc scope.sc_env; } in
    let scope = maybe_add_to_section scope (EcTheory.CTh_typeclass (x, tc)) in
      scope

  (* ------------------------------------------------------------------ *)
  let add_class (scope : scope) { pl_desc = tcd } =
    assert (scope.sc_pr_uc = None);

    let name  = unloc tcd.ptc_name in
    let scenv = (env scope) in

    check_name_available scope tcd.ptc_name;

    let tclass =
      let uptc =
        tcd.ptc_inth |> omap
          (fun { pl_loc = uploc; pl_desc = uptc } ->
            match EcEnv.TypeClass.lookup_opt uptc scenv with
            | None -> hierror ~loc:uploc "unknown type-class: `%s'"
                        (string_of_qsymbol uptc)
            | Some (tcp, _) -> tcp)
      in

      let asty  =
        let body = ofold (fun p tc -> Sp.add p tc) Sp.empty uptc in
          { tyd_params = []; tyd_type = `Abstract body; } in
      let scenv = EcEnv.Ty.bind name asty scenv in

      (* Check for duplicated field names *)
      Msym.odup unloc (List.map fst tcd.ptc_ops)
        |> oiter (fun (x, y) -> hierror ~loc:y.pl_loc
                    "duplicated operator name: `%s'" x.pl_desc);
      Msym.odup unloc (List.map fst tcd.ptc_axs)
        |> oiter (fun (x, y) -> hierror ~loc:y.pl_loc
                    "duplicated axiom name: `%s'" x.pl_desc);

      (* Check operators types *)
      let operators =
        let check1 (x, ty) =
          let ue = EcUnify.UniEnv.create (Some []) in
          let ty = transty tp_tydecl scenv ue ty in
          let ty = Tuni.offun (EcUnify.UniEnv.close ue) ty in
            (EcIdent.create (unloc x), ty)
        in
          tcd.ptc_ops |> List.map check1 in

      (* Check axioms *)
      let axioms =
        let scenv = EcEnv.Var.bind_locals operators scenv in
        let check1 (x, ax) =
          let ue = EcUnify.UniEnv.create (Some []) in
          let ax = trans_prop scenv ue ax in
          let ax = EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ax in
            (unloc x, ax)
        in
          tcd.ptc_axs |> List.map check1 in

      (* Construct actual type-class *)
      { tc_prt = uptc; tc_ops = operators; tc_axs = axioms; }
    in
      bindclass scope (name, tclass)

  (* ------------------------------------------------------------------ *)
  let check_tci_operators env tcty ops reqs =
    let ue   = EcUnify.UniEnv.create (Some (fst tcty)) in
    let rmap = Mstr.of_list reqs in

    let ops =
      let tt1 m (x, (tvi, op)) =
        if not (Mstr.mem (unloc x) rmap) then
          hierror ~loc:x.pl_loc "invalid operator name: `%s'" (unloc x);

        let tvi = List.map (TT.transty tp_tydecl env ue) tvi in
        let selected =
          EcUnify.select_op ~filter:EcDecl.is_oper
            (Some (EcUnify.TVIunamed tvi)) env (unloc op) ue []
        in
        let op =
          match selected with
          | [] -> hierror ~loc:op.pl_loc "unknown operator"
          | op1::op2::_ ->
              hierror ~loc:op.pl_loc
                "ambiguous operator (%s / %s)"
                (EcPath.tostring (fst (proj4_1 op1)))
                (EcPath.tostring (fst (proj4_1 op2)))
          | [((p, _), _, _, _)] ->
              let op   = EcEnv.Op.by_path p env in
              let opty =
                Tvar.subst
                  (Tvar.init (List.map fst op.op_tparams) tvi)
                  op.op_ty
              in
                (p, opty)

        in
          Mstr.change
            (function
            | None   -> Some (x.pl_loc, op)
            | Some _ -> hierror ~loc:(x.pl_loc)
              "duplicated operator name: `%s'" (unloc x))
            (unloc x) m
      in
        List.fold_left tt1 Mstr.empty ops
    in
      List.iter
        (fun (x, (req, _)) ->
           if req && not (Mstr.mem x ops) then
             hierror "no definition for operator `%s'" x)
        reqs;
      List.fold_left
        (fun m (x, (_, ty)) ->
           match Mstr.find_opt x ops with
           | None -> m
           | Some (loc, (p, opty)) ->
               if not (EcReduction.EqTest.for_type env ty opty) then
                 hierror ~loc "invalid type for operator `%s'" x;
               Mstr.add x p m)
        Mstr.empty reqs

  (* ------------------------------------------------------------------ *)
  let check_tci_axioms scope mode axs reqs =
    let rmap = Mstr.of_list reqs in
    let symbs, axs =
      List.map_fold
        (fun m (x, t) ->
          if not (Mstr.mem (unloc x) rmap) then
            hierror ~loc:x.pl_loc "invalid axiom name: `%s'" (unloc x);
          if Sstr.mem (unloc x) m then
            hierror ~loc:(x.pl_loc) "duplicated axiom name: `%s'" (unloc x);
          (Sstr.add (unloc x) m, (unloc x, t, Mstr.find (unloc x) rmap)))
        Sstr.empty axs in

    let interactive =
      List.pmap
        (fun (x, req) ->
           if not (Mstr.mem x symbs) then
             let ax = {
               ax_tparams = [];
               ax_spec    = req;
               ax_kind    = `Lemma;
               ax_nosmt   = true;
             } in Some ((None, ax), EcPath.psymbol x, scope.sc_env)
           else None)
        reqs in
      List.iter
        (fun (x, pt, f) ->
          let x  = "$" ^ x in
          let t  = { pt_core = pt; pt_intros = []; } in
          let t  = { pl_loc = pt.pl_loc; pl_desc = Pby (Some [t]) } in
          let t  = { pt_core = t; pt_intros = []; } in
          let ax = { ax_tparams = [];
                     ax_spec    = f;
                     ax_kind    = `Axiom (Ssym.empty, false);
                     ax_nosmt   = true; } in

          let pucflags = { puc_nosmt = false; puc_local = false; } in
          let pucflags = (([], None), pucflags) in
          let check    = Check_mode.check scope.sc_options in

          let escope = scope in
          let escope = Ax.start_lemma escope pucflags check ~name:x (ax, None) in
          let escope = Tactics.proof escope mode true in
          let escope = snd (Tactics.process_r ~reloc:x false mode escope [t]) in
            ignore (Ax.save_r escope))
        axs;
      interactive

  (* ------------------------------------------------------------------ *)
  let p_zmod    = EcPath.fromqsymbol ([EcCoreLib.i_top; "Ring"; "ZModule"], "zmodule")
  let p_ring    = EcPath.fromqsymbol ([EcCoreLib.i_top; "Ring"; "ComRing"], "ring"   )
  let p_idomain = EcPath.fromqsymbol ([EcCoreLib.i_top; "Ring"; "IDomain"], "idomain")
  let p_field   = EcPath.fromqsymbol ([EcCoreLib.i_top; "Ring"; "Field"  ], "field"  )

  (* ------------------------------------------------------------------ *)
  let ring_of_symmap env ty kind symbols =
    { r_type  = ty;
      r_zero  = oget (Mstr.find_opt "rzero" symbols);
      r_one   = oget (Mstr.find_opt "rone"  symbols);
      r_add   = oget (Mstr.find_opt "add"   symbols);
      r_opp   =      (Mstr.find_opt "opp"   symbols);
      r_mul   = oget (Mstr.find_opt "mul"   symbols);
      r_exp   =      (Mstr.find_opt "expr"  symbols);
      r_sub   =      (Mstr.find_opt "sub"   symbols);
      r_kind  = kind;
      r_embed =
        (match Mstr.find_opt "ofint" symbols with
         | None when EcReduction.EqTest.for_type env ty tint -> `Direct
         | None -> `Default | Some p -> `Embed p); }

  let addring (scope : scope) mode (kind, { pl_desc = tci; pl_loc = loc }) =
    if not (EcAlgTactic.is_module_loaded scope.sc_env) then
      hierror "load AlgTactic/Ring first";

    let ty =
      let ue = TT.transtyvars scope.sc_env (loc, Some (fst tci.pti_type)) in
      let ty = transty tp_tydecl scope.sc_env ue (snd tci.pti_type) in
        assert (EcUnify.UniEnv.closed ue);
        (EcUnify.UniEnv.tparams ue, Tuni.offun (EcUnify.UniEnv.close ue) ty)
    in
    let symbols = EcAlgTactic.ring_symbols scope.sc_env kind (snd ty) in
    let symbols = check_tci_operators scope.sc_env ty tci.pti_ops symbols in
    let cr      = ring_of_symmap scope.sc_env (snd ty) kind symbols in
    let axioms  = EcAlgTactic.ring_axioms scope.sc_env cr in
    let inter   = check_tci_axioms scope mode tci.pti_axs axioms in
    let scope   =
      { scope with sc_env =
          List.fold_left
            (fun env p -> EcEnv.TypeClass.add_instance ty (`General p) env)
            (EcEnv.Algebra.add_ring (snd ty) cr scope.sc_env)
            [p_zmod; p_ring; p_idomain] }

    in Ax.add_defer scope inter

  (* ------------------------------------------------------------------ *)
  let field_of_symmap env ty symbols =
    { f_ring = ring_of_symmap env ty `Integer symbols;
      f_inv  = oget (Mstr.find_opt "inv" symbols);
      f_div  = Mstr.find_opt "div" symbols; }

  let addfield (scope : scope) mode { pl_desc = tci; pl_loc = loc; } =
    if not (EcAlgTactic.is_module_loaded scope.sc_env) then
      hierror "load AlgTactic/Ring first";

    let ty =
      let ue = TT.transtyvars scope.sc_env (loc, Some (fst tci.pti_type)) in
      let ty = transty tp_tydecl scope.sc_env ue (snd tci.pti_type) in
        assert (EcUnify.UniEnv.closed ue);
        (EcUnify.UniEnv.tparams ue, Tuni.offun (EcUnify.UniEnv.close ue) ty)
    in
    let symbols = EcAlgTactic.field_symbols scope.sc_env (snd ty) in
    let symbols = check_tci_operators scope.sc_env ty tci.pti_ops symbols in
    let cr      = field_of_symmap scope.sc_env (snd ty) symbols in
    let axioms  = EcAlgTactic.field_axioms scope.sc_env cr in
    let inter   = check_tci_axioms scope mode tci.pti_axs axioms; in
    let scope   =
      { scope with sc_env =
          List.fold_left
            (fun env p -> EcEnv.TypeClass.add_instance ty (`General p) env)
            (EcEnv.Algebra.add_field (snd ty) cr scope.sc_env)
            [p_zmod; p_ring; p_idomain; p_field] }

    in Ax.add_defer scope inter

  (* ------------------------------------------------------------------ *)
  let symbols_of_tc (_env : EcEnv.env) ty (tcp, tc) =
    let subst = { ty_subst_id with ts_def = Mp.of_list [tcp, ([], ty)] } in
      List.map (fun (x, opty) ->
        (EcIdent.name x, (true, ty_subst subst opty)))
        tc.tc_ops

(*
  (* ------------------------------------------------------------------ *)
  let add_generic_tc (scope : scope) _mode { pl_desc = tci; pl_loc = loc; } =
    let ty =
      let ue = TT.transtyvars scope.sc_env (loc, Some (fst tci.pti_type)) in
      let ty = transty tp_tydecl scope.sc_env ue (snd tci.pti_type) in
        assert (EcUnify.UniEnv.closed ue);
        (EcUnify.UniEnv.tparams ue, Tuni.offun (EcUnify.UniEnv.close ue) ty)
    in

    let (tcp, tc) =
      match EcEnv.TypeClass.lookup_opt (unloc tci.pti_name) (env scope) with
      | None ->
          hierror ~loc:tci.pti_name.pl_loc
            "unknown type-class: %s" (string_of_qsymbol (unloc tci.pti_name))
      | Some tc -> tc
    in

    let  symbols = symbols_of_tc scope.sc_env (snd ty) (tcp, tc) in
    let _symbols = check_tci_operators scope.sc_env ty tci.pti_ops symbols in

    { scope with
        sc_env = EcEnv.TypeClass.add_instance ty (`General tcp) scope.sc_env }

(*
          let ue = EcUnify.UniEnv.create (Some []) in
          let ty = fst (EcUnify.UniEnv.openty ue (fst ty) None (snd ty)) in
            try  EcUnify.hastc scope.sc_env ue ty (Sp.singleton (fst tc)); tc
            with EcUnify.UnificationFailure _ ->
              hierror "type must be an instance of `%s'" (EcPath.tostring (fst tc))
*)
*)

  (* ------------------------------------------------------------------ *)
  let add_instance (scope : scope) mode ({ pl_desc = tci } as toptci) =
    match unloc tci.pti_name with
    | ([], "bring") -> begin
        if EcUtils.is_some tci.pti_args then
          hierror "unsupported-option";
        addring scope mode (`Boolean, toptci)
    end

    | ([], "ring") -> begin
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
      in addring scope mode (kind, toptci)
    end

    | ([], "field") -> addfield scope mode toptci

    | _ ->
        if EcUtils.is_some tci.pti_args then
          hierror "unsupported-option";
        failwith "unsupported"          (* FIXME *)

  (* ------------------------------------------------------------------ *)
  let add_datatype (scope : scope) (tydname : ptydname) dt =
    let name = snd (unloc tydname) in

    check_name_available scope name;

    let datatype = EHI.trans_datatype (env scope) tydname dt in
    let ctors    = datatype.ELI.dt_ctors in

    (* Generate schemes *)
    let (indsc, casesc) =
      try
        let indsc    = ELI.indsc_of_datatype `Elim datatype in
        let casesc   = ELI.indsc_of_datatype `Case datatype in
        (indsc, casesc)
      with ELI.NonPositive ->
        EHI.dterror tydname.pl_loc (env scope) EHI.DTE_NonPositive
    in

    (* Add final datatype to environment *)
    let tydecl = {
      tyd_params = datatype.ELI.dt_tparams;
      tyd_type   = `Datatype { tydt_ctors   = ctors ;
                               tydt_schcase = casesc;
                               tydt_schelim = indsc ; }; }

    in bind scope (unloc name, tydecl)

  (* ------------------------------------------------------------------ *)
  let add_record (scope : scope) (tydname : ptydname) rt =
    let name = snd (unloc tydname) in

    check_name_available scope name;

    let record  = EHI.trans_record (env scope) tydname rt in
    let scheme  = ELI.indsc_of_record record in

    (* Add final record to environment *)
    let tydecl  = {
      tyd_params = record.ELI.rc_tparams;
      tyd_type   = `Record (scheme, record.ELI.rc_fields); }

    in bind scope (unloc name, tydecl)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  open EcTheory

  exception TopScope

  (* ------------------------------------------------------------------ *)
  let bind (scope : scope) (x, (cth, mode)) =
    assert (scope.sc_pr_uc = None);
    let scope =
      { scope with sc_env = EcEnv.Theory.bind ~mode x cth scope.sc_env; }
    in maybe_add_to_section scope (EcTheory.CTh_theory (x, (cth, mode)))

  (* ------------------------------------------------------------------ *)
  let required (scope : scope) (name : required_info) =
    assert (scope.sc_pr_uc = None);
    List.exists (fun x ->
        if x.rqd_name = name.rqd_name then (
(* PY: FIXME, should we ensure this, raise an error message ... *)
          assert (x.rqd_digest = name.rqd_digest);
          true)
        else false) scope.sc_required

  (* ------------------------------------------------------------------ *)
  let enter (scope : scope) (mode : thmode) (name : symbol) =
    assert (scope.sc_pr_uc = None);
    subscope scope mode name

  (* ------------------------------------------------------------------ *)
  let rec require_loaded (id:required_info) scope =
    if required scope id then
      scope
    else
      match Msym.find_opt id.rqd_name scope.sc_loaded with
      | Some ((rth, mode), ids) ->
          let scope = List.fold_right require_loaded ids scope in
          let env   = EcEnv.Theory.require ~mode id.rqd_name rth scope.sc_env in
            { scope with
                sc_env      = env;
                sc_required = id :: scope.sc_required; }

      | None -> assert false

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
        begin
          match EcSection.opath scope.sc_section with
          | None -> ()
          | Some (_, sp) ->
              if p_equal sp (EcEnv.root scope.sc_env) then
                hierror "cannot close a theory with active sections";
        end;
        let clears   = scope.sc_clears in
        let cth      = EcEnv.Theory.close ?pempty ~clears scope.sc_env in
        let loaded   = scope.sc_loaded in
        let section  = scope.sc_section in
        let required = scope.sc_required in
        let sup = { sup with sc_loaded = loaded; sc_section = section; } in

        ((cth, required), section, scope.sc_name, sup)

  (* ------------------------------------------------------------------ *)
  let exit ?(pempty = `ClearOnly) ?(clears =[]) (scope : scope) =
    let rec add_restr1 section where env item : EcEnv.env =
      match item with
      | EcTheory.CTh_theory (name, th) ->
          add_restr section (EcPath.pqname where name) th env

      | EcTheory.CTh_module me ->
          if EcSection.in_section section then begin
            let islocal =
              EcSection.is_local `Module
                (EcPath.pqname where me.me_name)
                (EcSection.locals section)
            in

            if islocal then
              Mod.add_local_restr env where me
            else
              env
          end else
            env

      | _ -> env

    and add_restr section where (th, thmode) env =
      match thmode with
      | `Abstract -> env
      | `Concrete ->
          List.fold_left (add_restr1 section where) env th.EcTheory.cth_struct
    in

    assert (scope.sc_pr_uc = None);

    let cth = exit_r ~pempty (add_clears clears scope) in
    let ((cth, required), section, (name, mode), scope) = cth in
    let scope = List.fold_right require_loaded required scope in
    let scope = cth |> ofold (fun cth scope ->
    let scope = bind scope (name, (cth, mode)) in
      { scope with sc_env =
          add_restr section
            (EcPath.pqname (path scope) name) (cth, mode) scope.sc_env })
      scope

    in (name, scope)

  (* ------------------------------------------------------------------ *)
  let bump_prelude (scope : scope) =
    match scope.sc_prelude with
    | `InPrelude, _ ->
         { scope with sc_prelude = (`InPrelude,
             { pr_env      = scope.sc_env;
               pr_required = scope.sc_required; }) }
    | _ -> scope

  (* ------------------------------------------------------------------ *)
  let import (scope : scope) (name : qsymbol) =
    assert (scope.sc_pr_uc = None);

    match EcEnv.Theory.lookup_opt ~mode:`All name scope.sc_env with
    | None ->
        hierror
          "cannot import the non-existent theory `%s'"
          (string_of_qsymbol name)

    | Some (_, (_, `Abstract)) ->
        hierror "cannot import an abstract theory"

    | Some (path, (_, `Concrete)) ->
        bump_prelude
          { scope with sc_env = EcEnv.Theory.import path scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let export (scope : scope) (name : qsymbol) =
    assert (scope.sc_pr_uc = None);

    match EcEnv.Theory.lookup_opt ~mode:`All name scope.sc_env with
    | None ->
        hierror
          "cannot export the non-existent theory `%s'"
          (string_of_qsymbol name)

    | Some (_, (_, `Abstract)) ->
        hierror "cannot export an abstract theory"

    | Some (path, (_, `Concrete)) ->
        bump_prelude
          { scope with sc_env = EcEnv.Theory.export path scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let check_end_required scope thname =
    if fst scope.sc_name <> thname then
      hierror "end-of-file while processing external theory %s %s"
        (fst scope.sc_name) thname;
    if scope.sc_pr_uc <> None then
      hierror
        "end-of-file while processing proof %s" (fst scope.sc_name)

  (* -------------------------------------------------------------------- *)
  let require (scope : scope) ((name, mode) : required_info * thmode) loader =
    assert (scope.sc_pr_uc = None);

    if required scope name then
      scope
    else
      match Msym.find_opt name.rqd_name scope.sc_loaded with
      | Some _ -> require_loaded name scope

      | None ->
        try
          let imported = enter (for_loading scope) mode name.rqd_name in
          let imported = { imported with sc_env = EcEnv.astop imported.sc_env } in
          let thname   = fst imported.sc_name in
          let imported = loader imported in

          check_end_required imported thname;

          let cth = exit_r ~pempty:`No imported in
          let (cth, rqs), _, (name1, _), imported = cth in
          assert (name.rqd_name = name1);
          let scope = { scope with sc_loaded =
            Msym.add name.rqd_name ((oget cth, mode), rqs) imported.sc_loaded; } in

          bump_prelude (require_loaded name scope)

        with e -> begin
          match toperror_of_exn_r e with
          | Some (l, e) when not (EcLocation.isdummy l) ->
              raise (ImportError (Some l, name.rqd_name, e))
          | _ ->
              raise (ImportError (None, name.rqd_name, e))
        end

  let required scope = scope.sc_required

end

(* -------------------------------------------------------------------- *)
module Section = struct
  module T = EcTheory

  let enter (scope : scope) (name : psymbol option) =
    assert (scope.sc_pr_uc = None);
    { scope with
        sc_section =
          EcSection.enter scope.sc_env
            (omap unloc name) scope.sc_section; }

  let exit (scope : scope) (name : psymbol option) =
    match EcSection.opath scope.sc_section with
    | None -> hierror "no section to close"
    | Some (sname, sp) ->
        if not (p_equal sp (EcEnv.root (scope.sc_env))) then
          hierror "cannot close a section containing pending theories";
        if sname <> (omap unloc name) then
          hierror "expecting [%s], not [%s]"
            (match sname with None -> "<empty>" | Some x -> x)
            (match  name with None -> "<empty>" | Some x -> unloc x);
        let (locals, osc) = EcSection.exit scope.sc_section in
        let oenv   = EcSection.env_of_locals locals in
        let oitems = EcSection.items_of_locals locals in
        let scenv  = scope.sc_env in
        let scope  = { scope with sc_env = oenv; sc_section = osc; } in

        let rec bind1 scope item =
          match item with
          | T.CTh_type     (x, ty) -> Ty.bind scope (x, ty)
          | T.CTh_operator (x, op) -> Op.bind scope (x, op)
          | T.CTh_modtype  (x, mt) -> ModType.bind scope (x, mt)

          | T.CTh_module me ->
            let mep = EcPath.pqname (path scope) me.me_name in
              if not (EcSection.is_local `Module mep locals) then
                Mod.bind scope false me
              else
                scope

          | T.CTh_axiom (x, ax) -> begin
            match ax.ax_kind with
            | `Axiom _ -> scope
            | `Lemma   ->
                let axp = EcPath.pqname (path scope) x in
                  if not (EcSection.is_local `Lemma axp locals) then
                    Ax.bind scope false
                      (x, { ax with ax_spec =
                              EcSection.generalize scenv locals ax.ax_spec })
                  else
                    scope
          end

          | T.CTh_export p ->
              { scope with sc_env = EcEnv.Theory.export p scope.sc_env }

          | T.CTh_theory (x, (th, thmode)) ->
              let scope = Theory.enter scope thmode x in
              let scope = List.fold_left bind1 scope th.EcTheory.cth_struct in
              let _, scope = Theory.exit scope in
                scope

          | T.CTh_typeclass (x, tc) -> Ty.bindclass scope (x, tc)

          | T.CTh_instance (p, cr) ->
              { scope with
                sc_env = EcEnv.TypeClass.add_instance p cr scope.sc_env }

          | T.CTh_baserw x ->
              { scope with sc_env = EcEnv.BaseRw.add x scope.sc_env }

          | T.CTh_addrw (p, l) ->
              { scope with sc_env = EcEnv.BaseRw.addto p l scope.sc_env }

          | T.CTh_reduction rule ->
              { scope with sc_env = EcEnv.Reduction.add rule scope.sc_env }

          | T.CTh_auto (local, level, base, ps) ->
              { scope with sc_env =
                  EcEnv.Auto.add ~local ~level ?base ps scope.sc_env }
        in

        List.fold_left bind1 scope oitems
end

(* -------------------------------------------------------------------- *)
module Reduction = struct
  let add_reduction scope (opts, reds) =
    check_state `InTop "hint simplify" scope;
    if EcSection.in_section scope.sc_section then
      hierror "cannot add reduction rule in a section";

    let opts = EcTheory.{
      ur_delta  = List.mem `Delta  opts;
      ur_eqtrue = List.mem `EqTrue opts;
    } in

    let rules =
      let for1 idx name =
        let idx      = odfl 0 idx in
        let lemma    = fst (EcEnv.Ax.lookup (unloc name) (env scope)) in
        let red_info = EcReduction.User.compile ~opts ~prio:idx (env scope) lemma in
        (lemma, opts, Some red_info) in

      let rules = List.map (fun (xs, idx) -> List.map (for1 idx) xs) reds in
      List.flatten rules

    in

    { scope with sc_env = EcEnv.Reduction.add rules (env scope) }
end

(* -------------------------------------------------------------------- *)
module Cloning = struct
  (* ------------------------------------------------------------------ *)
  open EcTheory
  open EcThCloning

  module C = EcThCloning
  module R = EcTheoryReplay

  (* ------------------------------------------------------------------ *)
  let onenv (tx : 'a -> EcEnv.env -> EcEnv.env) =
    fun sc x -> { sc with sc_env = tx x (env sc) }

  (* ------------------------------------------------------------------ *)
  let hooks : scope R.ovrhooks =
    let thenter sc mode x = Theory.enter sc mode x in
    let thexit  sc pempty = snd (Theory.exit ?clears:None ~pempty sc) in

    { R.henv     = (fun sc -> env sc);
      R.hty      = Ty     .bind;
      R.hop      = Op     .bind;
      R.hmodty   = ModType.bind;
      R.hmod     = Mod    .bind;
      R.hax      = Ax     .bind;
      R.hexport  = onenv EcEnv.Theory.export;
      R.hbaserw  = onenv EcEnv.BaseRw.add;
      R.haddrw   = onenv (curry EcEnv.BaseRw.addto);
      R.hauto    = onenv (fun (local, level, base, names) ->
                            EcEnv.Auto.add ~local ~level ?base names);
      R.husered  = onenv EcEnv.Reduction.add;
      R.htycl    = onenv (curry EcEnv.TypeClass.bind);
      R.hinst    = onenv (curry EcEnv.TypeClass.add_instance);
      R.hthenter = thenter;
      R.hthexit  = thexit;
      R.herr     = (fun ?loc -> hierror ?loc "%s"); }

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

    if EcSection.in_section scope.sc_section then begin
      let oname = unloc thcl.pthc_base in
      let oname = omap fst (EcEnv.Theory.lookup_opt oname scope.sc_env) in
      let tenv  = EcSection.topenv scope.sc_section in

      oname |> oiter (fun oname ->
        if EcUtils.is_none (EcEnv.Theory.by_path_opt oname tenv) then
          hierror "cannot clone a theory that has been defined in the active section")
    end else begin
      if thcl.pthc_local then
        hierror "cannot do a local clone outside of a section"
    end;

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

    let cpath = EcEnv.root scope.sc_env in
    let npath = if incl then cpath else EcPath.pqname cpath name in

    let (proofs, scope) =
      EcTheoryReplay.replay hooks
        ~abstract:opts.R.clo_abstract ~local:thcl.pthc_local ~incl
        ~clears:ntclr ~renames:rnms ~opath ~npath ovrds
        scope (name, (fst oth).cth_struct)
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

          let pucflags = { puc_nosmt = false; puc_local = false; } in
          let pucflags = (([], None), pucflags) in
          let check    = Check_mode.check scope.sc_options in

          let escope = { scope with sc_env = axc.C.axc_env; } in
          let escope = Ax.start_lemma escope pucflags check ~name:x (ax, None) in
          let escope = Tactics.proof escope mode true in
          let escope = snd (Tactics.process_r ~reloc:x false mode escope [t]) in
            ignore (Ax.save_r escope); None)
      proofs
    in

    let scope =
      thcl.pthc_import |> ofold (fun flag scope ->
        match flag with
        | `Import  -> { scope with sc_env = EcEnv.Theory.import npath scope.sc_env; }
        | `Export  -> { scope with sc_env = EcEnv.Theory.export npath scope.sc_env; }
        | `Include -> scope)
        scope

    in Ax.add_defer scope proofs

end

(* -------------------------------------------------------------------- *)
module Search = struct
  let search (scope : scope) qs =
    let paths =
      let do1 fp =
        match unloc fp with
        | PFident (q, None) -> begin
            match EcEnv.Op.all q.pl_desc scope.sc_env with
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
                    let tip = Tvar.subst tip in
                    let xs  = List.map (snd_map tip) nt.ont_args in
                    let bd  = EcFol.form_of_expr EcFol.mhr (EcTypes.e_mapty tip nt.ont_body) in
                    let fp  = EcFol.f_lambda (List.map (snd_map EcFol.gtty) xs) bd in

                    match fp.f_node with
                    | Fop (pf, _) -> (pf :: paths, pts)
                    | _ -> (paths, (ps, ue, fp) ::pts)
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
          let fp = EcTyping.trans_pattern scope.sc_env ps ue fp in
          `ByPattern ((ps, ue), fp)
      in List.map do1 qs in

    let relevant =
      let get_path r = function `ByPath s -> Sp.union r s | _ -> r in
      List.fold_left get_path Sp.empty paths in

    let axioms = EcSearch.search scope.sc_env paths in
    let axioms = EcSearch.sort relevant axioms in

    let buffer = Buffer.create 0 in
    let fmt    = Format.formatter_of_buffer buffer in
    let ppe    = EcPrinting.PPEnv.ofenv scope.sc_env in

    List.iter (fun ax ->
      Format.fprintf fmt "%a@." (EcPrinting.pp_axiom ~long:true ppe) ax)
      axioms;
    notify scope `Info "%s" (Buffer.contents buffer)
end
