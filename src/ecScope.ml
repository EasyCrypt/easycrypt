(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
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

module Sid  = EcIdent.Sid
module Mid  = EcIdent.Mid
module MSym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type action = {
  for_loading  : exn -> exn;
}

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
module type IOptions = sig
  type option

  val register          : action -> exn -> option
  val register_identity : exn -> option

  type options

  val init         : unit -> options
  val get          : options -> option -> exn
  val set          : options -> option -> exn -> options
  val for_loading  : options -> options
  val for_subscope : options -> options
end

(* -------------------------------------------------------------------- *)
module GenOptions : IOptions = struct
  type option = int

  type options = (action * exn) Mint.t

  let known_options : options ref = ref Mint.empty

  let identity = {
    for_loading = (fun x -> x);
  }

  let count = ref 0
  let initialized = ref false

  let register action exn =
    if !initialized then assert false;
    let opt = !count in
    incr count;
    known_options := Mint.add opt (action,exn) !known_options;
    opt

  let register_identity = register identity

  let init () =
    initialized := true;
    !known_options

  let get options opt =
    snd (Mint.find opt options)

  let set options opt exn =
    Mint.change
      (function None -> assert false | Some(act,_) -> Some (act, exn))
      opt options

  let for_loading options =
    Mint.map (fun (act, exn) -> act, act.for_loading exn) options

  let for_subscope options = options
end

(* -------------------------------------------------------------------- *)
module Check_mode = struct
  exception Full_check    (* Disable: checkproof off, i.e. check everything *)
  exception Check of bool (* true check proofs, false do not check *)

  let mode =
    let default = Check true in
    let for_loading = function
      | Check _ -> Check false
      | exn     -> exn
    in GenOptions.register { for_loading } default

  let check options =
    match GenOptions.get options mode with
    | Check b -> b
    | _       -> true

  let check_proof options b =
    match GenOptions.get options mode with
    | Check b' when b <> b' ->
        GenOptions.set options mode (Check b')
    | _ -> options

  let full_check options =
    GenOptions.set options mode Full_check
end

(* -------------------------------------------------------------------- *)
module Prover_info = struct
  exception PI of EcProvers.prover_infos

  let npi = GenOptions.register_identity (PI EcProvers.dft_prover_infos)

  let set options pi =
    GenOptions.set options npi (PI pi)

  let get options =
    match GenOptions.get options npi with
    | PI pi -> pi
    | _     -> assert false
end

(* -------------------------------------------------------------------- *)
module Implicits = struct
  exception Implicits of bool

  let implicits =
    let default = Implicits false in
    let for_loading = function
      | Implicits _ -> Implicits false
      | exn         -> exn
    in GenOptions.register { for_loading } default

  let set options value =
    GenOptions.set options implicits (Implicits value)

  let get options =
    match GenOptions.get options implicits with
    | Implicits value -> value
    | _ -> assert false
end

(* -------------------------------------------------------------------- *)
type proof_uc = {
  puc_active : proof_auc option;
  puc_cont   : proof_ctxt list * (EcEnv.env option);
}

and proof_auc = {
  puc_name   : string;
  puc_mode   : bool option;
  puc_jdg    : proof_state;
  puc_flags  : pucflags;
  puc_crt    : EcDecl.axiom;
}

and proof_ctxt = (symbol * EcDecl.axiom) * EcPath.path * EcEnv.env

and proof_state = PSNoCheck | PSCheck of EcCoreGoal.proof

and pucflags = {
  puc_nosmt : bool;
  puc_local : bool;
}

(* -------------------------------------------------------------------- *)
type scope = {
  sc_name     : symbol;
  sc_env      : EcEnv.env;
  sc_top      : scope option;
  sc_loaded   : (EcEnv.ctheory_w3 * symbol list) Msym.t;
  sc_required : symbol list;
  sc_pr_uc    : proof_uc option;
  sc_options  : GenOptions.options;
  sc_section  : EcSection.t;
}

(* -------------------------------------------------------------------- *)
let empty (gstate : EcGState.gstate) =
  let env = EcEnv.initial gstate in
  { sc_name       = EcPath.basename (EcEnv.root env);
    sc_env        = env;
    sc_top        = None;
    sc_loaded     = Msym.empty;
    sc_required   = [];
    sc_pr_uc      = None;
    sc_options    = GenOptions.init ();
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
let goal (scope : scope) =
  scope.sc_pr_uc |> obind (fun x -> x.puc_active)

(* -------------------------------------------------------------------- *)
let xgoal (scope : scope) =
  scope.sc_pr_uc

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
  let get_implicits scope =
    Implicits.get scope.sc_options

  let set_implicits scope value =
    { scope with sc_options = Implicits.set scope.sc_options value }
end

(* -------------------------------------------------------------------- *)
let for_loading (scope : scope) =
  let gstate = EcEnv.gstate scope.sc_env in
  let gstate = EcGState.copy gstate in

  EcGState.set_loglevel `Warning gstate;

  { (empty gstate) with
      sc_loaded  = scope.sc_loaded;
      sc_options = GenOptions.for_loading scope.sc_options; }

(* -------------------------------------------------------------------- *)
let subscope (scope : scope) (name : symbol) =
  let env = EcEnv.Theory.enter name scope.sc_env in

  { sc_name       = name;
    sc_env        = env;
    sc_top        = Some scope;
    sc_loaded     = scope.sc_loaded;
    sc_required   = scope.sc_required;
    sc_pr_uc      = None;
    sc_options    = GenOptions.for_subscope scope.sc_options;
    sc_section    = scope.sc_section;
  }

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
  exception Unknown_prover of string

  type options = {
    po_timeout   : int option;
    po_cpufactor : int option;
    po_nprovers  : int option;
    po_provers   : string list option;
  }

  let empty_options = {
    po_timeout   = None;
    po_cpufactor = None;
    po_nprovers  = None;
    po_provers   = None;
  }

  let pp_error fmt exn =
    match exn with
    | Unknown_prover s ->
        Format.fprintf fmt "Unknown prover %s" s
    | _ -> raise exn

  let _ = EcPException.register pp_error

  let check_prover_name { pl_desc = name; pl_loc = loc } =
    if not (EcProvers.is_prover_known name) then
      EcLocation.locate_error loc (Unknown_prover name);
    name

  let set_wrapper scope wrapper =
    let pi = Prover_info.get scope.sc_options in
    let pi = { pi with EcProvers.pr_wrapper = wrapper } in
      { scope with sc_options = Prover_info.set scope.sc_options pi; }

  let mk_prover_info scope options =
    let dft       = Prover_info.get scope.sc_options in
    let timeout   = max 0 (odfl dft.EcProvers.pr_timelimit options.po_timeout) in
    let cpufactor = max 0 (odfl dft.EcProvers.pr_cpufactor options.po_cpufactor) in
    let maxprocs  = odfl dft.EcProvers.pr_maxprocs options.po_nprovers in
    let provers   = odfl dft.EcProvers.pr_provers options.po_provers in
      { EcProvers.pr_maxprocs  = maxprocs;
        EcProvers.pr_provers   = provers;
        EcProvers.pr_timelimit = timeout;
        EcProvers.pr_cpufactor = cpufactor;
        EcProvers.pr_wrapper   = dft.EcProvers.pr_wrapper; }

  let set_prover_info scope options =
    let pi = mk_prover_info scope options in
    { scope with sc_options = Prover_info.set scope.sc_options pi }

  let set_all scope =
    let provers =
      List.map
        (fun p -> p.EcProvers.pr_name)
        (EcProvers.known ~evicted:false) in
    let options = { empty_options with po_provers = Some provers; } in
    set_prover_info scope options

  let set_default scope options =
    let provers =
      match options.po_provers with
      | None ->
         let provers = EcProvers.dft_prover_names in
         List.filter EcProvers.is_prover_known provers

      | Some provers ->
          List.iter
            (fun name ->
              if not (EcProvers.is_prover_known name) then
                raise (Unknown_prover name)) provers;
          provers
    in

    let options = { options with po_provers = Some provers } in
    set_prover_info scope options

  let process scope pi =
    let options = {
      po_timeout   = pi.pprov_timeout;
      po_cpufactor = pi.pprov_cpufactor;
      po_nprovers  = pi.pprov_max;
      po_provers   = pi.pprov_names |> omap (List.map check_prover_name);
    }

    in set_prover_info scope options

  let mk_prover_info scope pi =
    let options = {
      po_timeout   = pi.pprov_timeout;
      po_cpufactor = pi.pprov_cpufactor;
      po_nprovers  = pi.pprov_max;
      po_provers   = pi.pprov_names |> omap (List.map check_prover_name);
    }

    in mk_prover_info scope options

  let full_check scope =
    { scope with sc_options = Check_mode.full_check scope.sc_options }

  let check_proof scope b =
    { scope with sc_options = Check_mode.check_proof scope.sc_options b }
end

(* -------------------------------------------------------------------- *)
module Tactics = struct
  let pi scope pi = Prover.mk_prover_info scope pi

  let proof (scope : scope) mode (strict : bool) =
    check_state `InActiveProof "proof script" scope;

    match (oget scope.sc_pr_uc).puc_active with
    | None -> hierror "no active lemmas"
    | Some pac ->
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
        { scope with sc_pr_uc = Some { (oget scope.sc_pr_uc) with puc_active = Some pac; } }

  let process_r mark mode (scope : scope) (tac : ptactic list) =
    check_state `InProof "proof script" scope;

    let scope =
      match (oget scope.sc_pr_uc).puc_active with
      | None -> hierror "no active lemma"
      | Some pac ->
          if   mark && pac.puc_mode = None
          then proof scope mode true
          else scope
    in

    let puc = oget (scope.sc_pr_uc) in
    let pac = oget (puc).puc_active in

    match pac.puc_jdg with
    | PSNoCheck -> scope

    | PSCheck juc ->
        let module TTC = EcHiTacticals in

        let htmode =
          match pac.puc_mode, mode with
          | Some true , `WeakCheck -> `Admit
          | _         , `WeakCheck ->  hierror "cannot weak-check a non-strict proof script"
          | Some true , `Check     -> `Strict
          | Some false, `Check     -> `Standard
          | _         , `Check     -> `Strict
        in

        let ttenv = {
          EcHiGoal.tt_provers   = pi scope;
          EcHiGoal.tt_smtmode   = htmode;
          EcHiGoal.tt_implicits = Options.get_implicits scope; } in

        let juc   = TTC.process ttenv tac juc in
        let pac   = { pac with puc_jdg = PSCheck juc } in
          { scope with sc_pr_uc = Some { puc with puc_active = Some pac; } }

  let process_core mark mode (scope : scope) (ts : ptactic_core list) =
    let ts = List.map (fun t -> { pt_core = t; pt_intros = []; }) ts in
      process_r mark mode scope ts

  let process scope mode tac =
    process_r true mode scope tac
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  open EcParsetree
  open EcDecl

  module TT = EcTyping

  type mode = [`WeakCheck | `Check]

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
          let lvl2 = if ax.ax_kind = `Axiom then `Axiom else `Lemma in

          if lvl2 = `Axiom && ax.ax_tparams <> [] then
            hierror "axiom must be monomorphic in sections";

          let axpath = EcPath.pqname (path scope) x in
          let ec = EcSection.add_lemma axpath (lvl1, lvl2) scope.sc_section in
            { scope with sc_section = ec }
    in
      scope

  (* ------------------------------------------------------------------ *)
  let start_lemma scope (cont, axflags) check name axd =
    let puc =
      match check with
      | false -> PSNoCheck
      | true  ->
          let hyps  = EcEnv.LDecl.init scope.sc_env axd.ax_tparams in
          let proof = EcCoreGoal.start hyps (oget axd.ax_spec) in
          PSCheck proof
    in
    let puc =
      { puc_active = Some {
          puc_name  = name;
          puc_mode  = None;
          puc_jdg   = puc;
          puc_flags = axflags;
          puc_crt   = axd; };
        puc_cont = cont; }
    in
      { scope with sc_pr_uc = Some puc }

  (* ------------------------------------------------------------------ *)
  let rec add_r (scope : scope) mode (ax : paxiom located) =
    assert (scope.sc_pr_uc = None);

    let loc = ax.pl_loc and ax = ax.pl_desc in
    let ue  = TT.transtyvars scope.sc_env (loc, ax.pa_tyvars) in

    if ax.pa_local && not (EcSection.in_section scope.sc_section) then
      hierror "cannot declare a local lemma outside of a section";

    let (pconcl, tintro) =
      match ax.pa_vars with
      | None    -> (ax.pa_formula, [])
      | Some vs ->
          let pconcl = { pl_loc = loc; pl_desc = PFforall (vs, ax.pa_formula) } in
            (pconcl, List.flatten (List.map fst vs))
    in

    let tintro =
      List.map
        (fun x -> IPCore (mk_loc x.pl_loc (`NoRename x.pl_desc)))
        tintro in
    let tintro = mk_loc loc (Plogic (Pintro tintro)) in

    let concl = TT.trans_prop scope.sc_env ue pconcl in

    if not (EcUnify.UniEnv.closed ue) then
      hierror "the formula contains free type variables";

    let concl   = EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) concl in
    let tparams = EcUnify.UniEnv.tparams ue in

    let axd  =
      let kind = match ax.pa_kind with PAxiom _ -> `Axiom | _ -> `Lemma in
        { ax_tparams = tparams;
          ax_spec    = Some concl;
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
          if EcSection.form_use_local concl locals then
            hierror "this lemma uses local modules and must be declared as local"
    end;

    if ax.pa_local && ax.pa_kind = (PAxiom `Axiom) then
      hierror "an axiom cannot be local";

    match ax.pa_kind with
    | PILemma ->
        let scope = start_lemma scope pucflags check (unloc ax.pa_name) axd in
        let scope = Tactics.process_core false `Check scope [tintro] in
          None, scope

    | PLemma tc ->
        let scope = start_lemma scope pucflags check (unloc ax.pa_name) axd in
        let scope = Tactics.process_core false `Check scope [tintro] in
        let scope = Tactics.proof scope mode (if tc = None then true else false) in

        let tc =
          match tc with
          | Some tc -> tc
          | None    ->
              let dtc = Plogic (Psmt (None, empty_pprover)) in
              let dtc = { pl_loc = loc; pl_desc = dtc } in
              let dtc = { pt_core = dtc; pt_intros = []; } in
                dtc
        in

        let tc = { pl_loc = loc; pl_desc = Pby (Some [tc]) } in
        let tc = { pt_core = tc; pt_intros = []; } in

        let scope = Tactics.process_r false mode scope [tc] in
          save scope loc

    | PAxiom _ ->
          Some (unloc ax.pa_name),
          bind scope (snd pucflags).puc_local (unloc ax.pa_name, axd)

  (* ------------------------------------------------------------------ *)
  and add_for_cloning (scope : scope) proofs =
    match proofs with
    | [] -> scope
    | _  ->
        assert (scope.sc_pr_uc = None);
        let puc = { puc_active = None; puc_cont = (proofs, Some scope.sc_env); } in
          { scope with sc_pr_uc = Some puc; }

  (* ------------------------------------------------------------------ *)
  and save scope _loc =
    check_state `InProof "save" scope;

    let puc = oget scope.sc_pr_uc in
    let pac =
      match puc.puc_active with
      | None -> hierror "no active lemma"
      | Some pac -> begin
          match pac.puc_jdg with
          | PSNoCheck  -> ()
          | PSCheck pf -> begin
              if not (EcCoreGoal.closed pf) then
                hierror "cannot save an incomplete proof"
          end
      end; pac
    in

    let scope = { scope with sc_pr_uc = Some { puc with puc_active = None; } } in

    let scope =
      match fst puc.puc_cont with
      | [] -> { scope with sc_pr_uc = None; }
      | _  -> scope
    in

    let scope =
      match snd puc.puc_cont with
      | Some e -> { scope with sc_env = e }
      | None   -> bind scope pac.puc_flags.puc_local (pac.puc_name, pac.puc_crt)
    in

      (Some pac.puc_name, scope)

  (* ------------------------------------------------------------------ *)
  let add (scope : scope) mode (ax : paxiom located) =
    add_r scope mode ax

  (* ------------------------------------------------------------------ *)
  let activate (scope : scope) (qn : pqsymbol) =
    check_state `InProof "activate" scope;

    let qn = EcPath.fromqsymbol (unloc qn) in

    let puc = oget scope.sc_pr_uc in
    let _ =
      match puc.puc_active with
      | Some _ -> hierror "a lemma is already active"
      | None -> ()
    in

    let (((x, ax), _, axenv), proofs) =
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
    let scope = start_lemma scope pucflags check x ax in

      scope
end

(* -------------------------------------------------------------------- *)
module Op = struct
  open EcTypes
  open EcDecl

  module TT  = EcTyping
  module EHI = EcHiInductive

  let bind (scope : scope) ((x, op) : _ * operator) =
    assert (scope.sc_pr_uc = None);
    let scope = { scope with sc_env = EcEnv.Op.bind x op scope.sc_env } in
    let scope = maybe_add_to_section scope (EcTheory.CTh_operator (x, op)) in
      scope

  let add (scope : scope) (op : poperator located) =
    assert (scope.sc_pr_uc = None);
    let op = op.pl_desc and loc = op.pl_loc in
    let ue = TT.transtyvars scope.sc_env (loc, op.po_tyvars) in

    let (ty, body) =
      match op.po_def with
      | PO_abstr pty ->
          (TT.transty TT.tp_relax scope.sc_env ue pty, `Abstract)

      | PO_concr (bd, pty, pe) ->
          let env     = scope.sc_env in
          let codom   = TT.transty TT.tp_relax env ue pty in
          let env, xs = TT.transbinding env ue bd in
          let body    = TT.transexpcast env `InOp ue codom pe in
          let lam     = EcTypes.e_lam xs body in
            (lam.EcTypes.e_ty, `Plain lam)

      | PO_case (bd, pty, pbs) ->
          let name = { pl_loc = loc; pl_desc = unloc op.po_name } in
          match EHI.trans_matchfix (env scope) ue name (bd, pty, pbs) with
          | (ty, opinfo) -> (ty, `Fix opinfo)
    in

    if not (EcUnify.UniEnv.closed ue) then
      hierror ~loc "this operator type contains free type variables";

    let uni     = Tuni.offun (EcUnify.UniEnv.close ue) in
    let ty      = uni ty in
    let tparams = EcUnify.UniEnv.tparams ue in
    let body    =
      match body with
      | `Abstract -> None
      | `Plain e  -> Some (OP_Plain (e_mapty uni e))
      | `Fix opfx ->
          Some (OP_Fix {
            opf_args     = opfx.EHI.mf_args;
            opf_resty    = opfx.EHI.mf_codom;
            opf_struct   = (opfx.EHI.mf_recs, List.length opfx.EHI.mf_args);
            opf_branches = opfx.EHI.mf_branches;
          })

    in

    let tyop = EcDecl.mk_op tparams ty body in

    if op.po_nosmt && (is_none op.po_ax) then
      hierror ~loc "[nosmt] is only supported for axiomatized operators";

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
          | OB_oper (Some (OP_Plain bd)) ->
              let axbd = EcFol.form_of_expr EcFol.mhr bd in
              let axbd, axpm =
                let bdpm = List.map fst tyop.op_tparams in
                let axpm = List.map EcIdent.fresh bdpm in
                  (EcFol.Fsubst.subst_tvar
                     (EcTypes.Tvar.init bdpm (List.map tvar axpm))
                     axbd,
                   List.combine axpm (List.map snd tyop.op_tparams))
              in
  
              let axspec =
                EcFol.f_eq
                  (EcFol.f_op
                     (EcPath.pqname (path scope) (unloc op.po_name))
                     (List.map (tvar |- fst) axpm)
                     axbd.EcFol.f_ty)
                  axbd
              in
  
              let tyop = { tyop with op_kind = OB_oper None } in
              let axop = { ax_tparams = axpm;
                           ax_spec    = Some axspec;
                           ax_kind    = `Axiom;
                           ax_nosmt   = op.po_nosmt; } in
  
              let scope = bind scope (unloc op.po_name, tyop) in
                Ax.bind scope false (unloc ax, axop)
  
          | _ -> hierror ~loc "cannot axiomatized non-plain operators"
      end
    in

    let scope =
      if not (List.isempty op.po_aliases) then begin
        if not (EcUtils.is_none body) then
          hierror ~loc "multiple operator names are only allowed for abstract operators";
        let addnew scope name =
          let nparams = List.map (fst_map EcIdent.fresh) tparams in
          let subst = Tvar.init
            (List.map fst tparams)
            (List.map (tvar |- fst) nparams) in
          let op = EcDecl.mk_op nparams (Tvar.subst subst ty) None in
          bind scope (unloc name, op)
        in List.fold_left addnew scope op.po_aliases

      end else scope

    in scope
end

(* -------------------------------------------------------------------- *)
module Pred = struct
  module TT = EcTyping

  let add (scope : scope) (op : ppredicate located) =
    assert (scope.sc_pr_uc = None);
    let op = op.pl_desc and loc = op.pl_loc in
    let ue     = TT.transtyvars scope.sc_env (loc, op.pp_tyvars) in
    let tp     = TT.tp_relax in
    let dom, body =
      match op.pp_def with
      | PPabstr ptys ->
        List.map (TT.transty tp scope.sc_env ue) ptys, None
      | PPconcr(bd,pe) ->
        let env, xs = TT.transbinding scope.sc_env ue bd in
        let body = TT.trans_prop env ue pe in
        let dom = List.map snd xs in
        let xs = List.map (fun (x,ty) -> x, EcFol.GTty ty) xs in
        let lam = EcFol.f_lambda xs body in
          (dom, Some lam)
    in

    if not (EcUnify.UniEnv.closed ue) then
      hierror "this predicate type contains free type variables";

    let uni     = EcUnify.UniEnv.close ue in
    let body    = body |> omap (EcFol.Fsubst.uni uni) in
    let dom     = List.map (Tuni.offun uni) dom in
    let tparams = EcUnify.UniEnv.tparams ue in
    let tyop    = EcDecl.mk_pred tparams dom body in

      Op.bind scope (unloc op.pp_name, tyop)
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  module TT = EcTyping

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
        let env =
          match m.me_body with
          | ME_Alias _ | ME_Decl _ -> scope.sc_env
          | ME_Structure _ ->
            let env = scope.sc_env in
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
            EcEnv.Mod.add_restr_to_locals (rx,EcPath.Sm.empty) env in
        let ec = EcSection.add_local_mod mpath scope.sc_section in
        { scope with sc_section = ec; sc_env = env }
    in
      scope

  let add (scope : scope) (ptm : pmodule_def) =
    assert (scope.sc_pr_uc = None);

    if ptm.ptm_local && not (EcSection.in_section scope.sc_section) then
      hierror "cannot declare a local module outside of a section";

    let { ptm_name = name; ptm_body = m; } = ptm in
    let m = TT.transmod scope.sc_env ~attop:true (unloc name) m in

    if not ptm.ptm_local then begin
      match EcSection.olocals scope.sc_section with
      | None -> ()
      | Some locals ->
          if EcSection.module_use_local_or_abs m locals then
            hierror "this module use local/abstracts modules and must be declared as local";

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
                (EcPath.tostring (fst (proj3_1 op1)))
                (EcPath.tostring (fst (proj3_1 op2)))
          | [((p, _), _, _)] ->
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
        Sstr.empty axs
    in
      List.iter
        (fun (x, _) ->
           if not (Mstr.mem x symbs) then
             hierror "no proof for axiom `%s'" x)
        reqs;
      List.iter
        (fun (x, pt, f) ->
          let x  = "$" ^ x in
          let t  = { pt_core = pt; pt_intros = []; } in
          let t  = { pl_loc = pt.pl_loc; pl_desc = Pby (Some [t]) } in
          let t  = { pt_core = t; pt_intros = []; } in
          let ax = { ax_tparams = [];
                     ax_spec    = Some f;
                     ax_kind    = `Axiom;
                     ax_nosmt   = true; } in

          let pucflags = { puc_nosmt = false; puc_local = false; } in
          let pucflags = (([], None), pucflags) in
          let check    = Check_mode.check scope.sc_options in

          let escope = scope in
          let escope = Ax.start_lemma escope pucflags check x ax in
          let escope = Tactics.proof escope mode true in
          let escope = Tactics.process_r false mode escope [t] in
            ignore (Ax.save escope pt.pl_loc))
        axs

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
      check_tci_axioms scope mode tci.pti_axs axioms;
      { scope with sc_env =
          List.fold_left
            (fun env p -> EcEnv.TypeClass.add_instance ty (`General p) env)
            (EcEnv.Algebra.add_ring (snd ty) cr scope.sc_env)
            [p_zmod; p_ring; p_idomain] }

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
      check_tci_axioms scope mode tci.pti_axs axioms;
      { scope with sc_env =
          List.fold_left
            (fun env p -> EcEnv.TypeClass.add_instance ty (`General p) env)
            (EcEnv.Algebra.add_field (snd ty) cr scope.sc_env)
            [p_zmod; p_ring; p_idomain; p_field] }

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
            if odfl false (c |> omap (fun c -> c < 2)) then
              hierror "invalid coefficient modulus";
            if odfl false (p |> omap (fun p -> p < 2)) then
              hierror "invalid power modulus";
            if c = Some 2 && p = Some 2 then `Boolean else `Modulus (c, p)
      in addring  scope mode (kind, toptci)
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
  exception TopScope

  (* ------------------------------------------------------------------ *)
  let bind (scope : scope) ((x, cth) : _ * EcEnv.ctheory_w3) =
    assert (scope.sc_pr_uc = None);
    let scope =
      { scope with
          sc_env = EcEnv.Theory.bind x cth scope.sc_env; }
    in
      maybe_add_to_section scope
        (EcTheory.CTh_theory (x, EcEnv.ctheory_of_ctheory_w3 cth))

  (* ------------------------------------------------------------------ *)
  let required (scope : scope) (name : symbol) =
    assert (scope.sc_pr_uc = None);
    List.exists (fun x -> x = name) scope.sc_required

  (* ------------------------------------------------------------------ *)
  let enter (scope : scope) (name : symbol) =
    assert (scope.sc_pr_uc = None);
    subscope scope name

  (* ------------------------------------------------------------------ *)
  let rec require_loaded id scope =
    if required scope id then
      scope
    else
      match Msym.find_opt id scope.sc_loaded with
      | Some (rth, ids) ->
          let scope = List.fold_right require_loaded ids scope in
          let env   = EcEnv.Theory.require id rth scope.sc_env in
            { scope with
              sc_env = env;
              sc_required = id :: scope.sc_required; }

      | None -> assert false

  (* -------------------------------------------------------------------- *)
  let exit_r (scope : scope) =
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
        let cth      = EcEnv.Theory.close scope.sc_env in
        let loaded   = scope.sc_loaded in
        let section  = scope.sc_section in
        let required = scope.sc_required in
        let sup = { sup with sc_loaded = loaded; sc_section = section; } in
          ((cth, required), scope.sc_name, sup)

  (* ------------------------------------------------------------------ *)
  let exit (scope : scope) =
    assert (scope.sc_pr_uc = None);
    let ((cth, required), name, scope) = exit_r scope in
    let scope = List.fold_right require_loaded required scope in
      (name, bind scope (name, cth))

  (* ------------------------------------------------------------------ *)
  let import (scope : scope) (name : qsymbol) =
    assert (scope.sc_pr_uc = None);
    let path = fst (EcEnv.Theory.lookup name scope.sc_env) in
    { scope with
        sc_env = EcEnv.Theory.import path scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let export (scope : scope) (name : qsymbol) =
    assert (scope.sc_pr_uc = None);
    let path = fst (EcEnv.Theory.lookup name scope.sc_env) in
    { scope with
        sc_env = EcEnv.Theory.export path scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let check_end_required scope thname =
    if scope.sc_name <> thname then
      begin
        let msg =
          Printf.sprintf
            "end-of-file while processing external theory %s %s"
            scope.sc_name thname in
        failwith msg
      end;
    if scope.sc_pr_uc <> None then
      let msg =
        Printf.sprintf
          "end-of-file while processing proof %s" scope.sc_name
      in
        failwith msg

  (* -------------------------------------------------------------------- *)
  let require (scope : scope) (name : symbol) loader =
    assert (scope.sc_pr_uc = None);

    if required scope name then
      scope
    else
      match Msym.find_opt name scope.sc_loaded with
      | Some _ -> require_loaded name scope

      | None ->
          let imported = enter (for_loading scope) name in
          let thname   = imported.sc_name in
          let imported = loader imported in
          check_end_required imported thname;
          let cthr, name, imported = exit_r imported in
          let scope =
            { scope with
                sc_loaded = Msym.add name cthr imported.sc_loaded; }
          in
            require_loaded name scope

  (* ------------------------------------------------------------------ *)
  let clone (scope : scope) mode (thcl : theory_cloning) =
    let module C = EcThCloning in

    assert (scope.sc_pr_uc = None);

    if EcSection.in_section scope.sc_section then
      hierror "cannot clone a theory while a section is active";

    let (name, proofs, nth) = C.clone scope.sc_env thcl in

    let proofs = List.pmap (fun axc ->
      match axc.C.axc_tac with
      | None -> Some (axc.C.axc_axiom, axc.C.axc_path, axc.C.axc_env)
      | Some pt ->
          let t = { pt_core = pt; pt_intros = []; } in
          let t = { pl_loc = pt.pl_loc; pl_desc = Pby (Some [t]); } in
          let t = { pt_core = t; pt_intros = []; } in
          let (x, ax) = axc.C.axc_axiom in

          let pucflags = { puc_nosmt = false; puc_local = false; } in
          let pucflags = (([], None), pucflags) in
          let check    = Check_mode.check scope.sc_options in

          let escope = { scope with sc_env = axc.C.axc_env; } in
          let escope = Ax.start_lemma escope pucflags check x ax in
          let escope = Tactics.proof escope mode true in
          let escope = Tactics.process_r false mode escope [t] in
            ignore (Ax.save escope pt.pl_loc); None)
      proofs
    in

    let scope = bind scope (name, nth) in
    let scope = Ax.add_for_cloning scope proofs in

      (name, scope)

  (* ------------------------------------------------------------------ *)
  let import_w3 scope dir file renaming =
    assert (scope.sc_pr_uc = None);

    if EcSection.in_section scope.sc_section then
      hierror "cannot import a Why3 theory while a section is active";

    let mk_renaming (l,k,s) =
      let k =
        match k with
        | RNty -> EcWhy3.RDts
        | RNop -> EcWhy3.RDls
        | RNpr -> EcWhy3.RDpr
      in
        (l, k, s)
    in

    let renaming = List.map mk_renaming renaming in
    let env      = fst (EcEnv.import_w3_dir scope.sc_env dir file renaming) in
      { scope with sc_env = env }
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
            | `Axiom -> scope
            | `Lemma ->
                let axp = EcPath.pqname (path scope) x in
                  if not (EcSection.is_local `Lemma axp locals) then
                    Ax.bind scope false
                      (x, { ax with ax_spec =
                              ax.ax_spec |> omap (EcSection.generalize scenv locals) })
                  else
                    scope
          end

          | T.CTh_export p ->
              { scope with sc_env = EcEnv.Theory.export p scope.sc_env }

          | T.CTh_theory (x, th) ->
              let scope = Theory.enter scope x in
              let scope = List.fold_left bind1 scope th.EcTheory.cth_struct in
              let _, scope = Theory.exit scope in
                scope

          | T.CTh_typeclass (x, tc) -> Ty.bindclass scope (x, tc)

          | T.CTh_instance (p, cr) ->
              { scope with
                  sc_env = EcEnv.TypeClass.add_instance p cr scope.sc_env }
          | T.CTh_baserw x -> 
              { scope with 
                sc_env = EcEnv.BaseRw.bind x scope.sc_env }
          | T.CTh_addrw(p,l) ->
              { scope with
                sc_env = EcEnv.BaseRw.bind_addrw p l scope.sc_env }
        in

        List.fold_left bind1 scope oitems
end

(* -------------------------------------------------------------------- *)
module Extraction = struct
  let check_top scope =
    if not (scope.sc_top = None) then
      hierror "Extraction cannot be done inside a theory";
    if EcSection.in_section scope.sc_section then
      hierror "Extraction cannot be done inside a section"

  let process scope todo =
    check_top scope;
    EcExtraction.process_extraction (env scope) scope.sc_required todo;
    scope
end

(* -------------------------------------------------------------------- *)
module BaseRw = struct
  let process scope x = 
    { scope with 
      sc_env = EcEnv.BaseRw.bind x.pl_desc (env scope) }

  let process_addrw scope (x,l) = 
    let env = env scope in
    let env, base = 
      match EcEnv.BaseRw.lookup_opt x.pl_desc env with
      | None -> 
        let pre, base = x.pl_desc in 
        if pre <> [] then 
          hierror ~loc:x.pl_loc 
            "cannot create a hint rewrite base outside a theory";
        let p = EcPath.pqname (EcEnv.root env) base in
        begin match EcEnv.Ax.by_path_opt p env with
        | None -> ()
        | Some _ ->  
          hierror ~loc:x.pl_loc 
            "an axiom with the same name already exists";
        end;
        let env = EcEnv.BaseRw.bind base env in
        env, fst (EcEnv.BaseRw.lookup x.pl_desc env) 
      | Some (base, _) -> env, base in
    let l = List.map (fun l -> EcEnv.Ax.lookup_path l.pl_desc env) l in
    { scope with
      sc_env = EcEnv.BaseRw.bind_addrw base l env }
end
