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

module Mid  = EcIdent.Mid
module MSym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type action = {
  for_loading  : exn -> exn;
}

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
module Options : IOptions = struct
  type option = int

  type options = (action * exn) Mint.t

  let known_options : options ref = ref Mint.empty

  let identity = {
    for_loading  = (fun x -> x);
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
module Notifier = struct
  exception Verbose of [`ForLoading | `Verbose of bool]

  let for_loading = function
    | Verbose _ -> Verbose `ForLoading
    | exn -> exn

  let default = Verbose (`Verbose true)

  let mode = Options.register { for_loading } default

  let verbose options =
    match Options.get options mode with
    | Verbose b -> b
    | _ -> assert false

  let set options b =
    match Options.get options mode with
    | Verbose (`ForLoading) -> options
    | Verbose (`Verbose _)  -> Options.set options mode (Verbose (`Verbose b))
    | _ -> assert false
end

(* -------------------------------------------------------------------- *)
module Check_mode = struct
  exception Full_check    (* Disable: checkproof off, i.e. check everything *)
  exception Check of bool (* true check proofs, false do not check *)

  let for_loading = function
    | Check _ -> Check false
    | exn     -> exn

  let default = Check true

  let mode = Options.register { for_loading } default

  let check options =
    match Options.get options mode with
    | Check b -> b
    | _       -> true

  let check_proof options b =
    match Options.get options mode with
    | Check b' when b <> b' ->
        Options.set options mode (Check b')
    | _ -> options

  let full_check options =
    Options.set options mode Full_check
end

(* -------------------------------------------------------------------- *)
module Prover_info = struct
  exception PI of EcProvers.prover_infos

  let npi = Options.register_identity (PI EcProvers.dft_prover_infos)

  let set options pi =
    Options.set options npi (PI pi)

  let get options =
    match Options.get options npi with
    | PI pi -> pi
    | _     -> assert false
end

(* -------------------------------------------------------------------- *)
type proof_uc = {
  puc_name : string;
  puc_jdg :  EcBaseLogic.judgment_uc;
}

(* -------------------------------------------------------------------- *)
type scope = {
  sc_name       : symbol;
  sc_env        : EcEnv.env;
  sc_top        : scope option;
  sc_loaded     : (EcEnv.ctheory_w3 * symbol list) Msym.t;
  sc_required   : symbol list;
  sc_pr_uc      : proof_uc list;
  sc_options    : Options.options ref;
}

(* -------------------------------------------------------------------- *)
let empty =
  let env = EcEnv.initial in
    { sc_name       = EcPath.basename (EcEnv.root env);
      sc_env        = EcEnv.initial;
      sc_top        = None;
      sc_loaded     = Msym.empty;
      sc_required   = [];
      sc_pr_uc      = [];
      sc_options    = ref (Options.init ());
    }

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
  scope.sc_pr_uc

(* -------------------------------------------------------------------- *)
let verbose (scope : scope) =
  match Notifier.verbose !(scope.sc_options) with
  | `ForLoading -> false
  | `Verbose b  -> b

(* -------------------------------------------------------------------- *)
let set_verbose (scope : scope) (b : bool) =
  scope.sc_options := Notifier.set !(scope.sc_options) b;
  scope

(* -------------------------------------------------------------------- *)
let for_loading (scope : scope) =
  { empty with
      sc_loaded  = scope.sc_loaded;
      sc_options = ref (Options.for_loading !(scope.sc_options)); }

(* -------------------------------------------------------------------- *)
let subscope (scope : scope) (name : symbol) =
  let env = EcEnv.Theory.enter name scope.sc_env in

  { sc_name       = name;
    sc_env        = env;
    sc_top        = Some scope;
    sc_loaded     = scope.sc_loaded;
    sc_required   = scope.sc_required;
    sc_pr_uc      = [];
    sc_options    = ref (Options.for_subscope !(scope.sc_options));
  }

(* -------------------------------------------------------------------- *)
module Prover = struct
  exception Unknown_prover of string

  let pp_error fmt exn =
    match exn with
    | Unknown_prover s ->
        Format.fprintf fmt "Unknown prover %s" s
    | _ -> raise exn

  let _ = EcPException.register pp_error

  let check_prover_name name =
    let s = unloc name in
    if not (EcProvers.check_prover_name s) then
      EcLocation.locate_error name.pl_loc (Unknown_prover s);
    s

  let mk_prover_info scope max time ns =
    let dft = Prover_info.get !(scope.sc_options) in
    let time = odfl dft.EcProvers.prover_timelimit time in
    let time = if time < 1 then 1 else time in
    let provers = odfl dft.EcProvers.prover_names ns in
    let provers = List.filter (fun s -> s <> "Yices")
        (Array.to_list provers) in
    let max     = odfl dft.EcProvers.prover_max_run max in
    { EcProvers.prover_max_run   = max;
      EcProvers.prover_names     = Array.of_list provers;
      EcProvers.prover_timelimit = time }

  let set_prover_info scope max time ns =
    let pi = mk_prover_info scope max time ns in
      scope.sc_options := Prover_info.set !(scope.sc_options) pi;
      scope

  let set_all scope =
    let provers = Array.of_list (EcProvers.known_provers ()) in
    set_prover_info scope None None (Some provers)

  let set_default scope max provers =
    let provers =
      match provers with
      | None -> List.filter EcProvers.check_prover_name ["Alt-Ergo";"Z3";"Vampire";"Eprover";"Yices"]
      | Some ps -> List.iter (fun s -> if not (EcProvers.check_prover_name s) then raise (Unknown_prover s)) ps;ps
    in
    let provers = Array.of_list provers in
    let time = 3 in
      set_prover_info scope (Some max) (Some time) (Some provers)

  let process scope pi =
    let max  = pi.pprov_max in
    let time = pi.pprov_time in
    let ns   = pi.pprov_names in
    let ns   = omap ns (List.map check_prover_name) in
    let ns   = omap ns Array.of_list in
    set_prover_info scope max time ns

  let mk_prover_info scope pi =
    let max  = pi.pprov_max in
    let time = pi.pprov_time in
    let ns   = pi.pprov_names in
    let ns   = omap ns (List.map check_prover_name) in
    let ns   = omap ns Array.of_list in
    mk_prover_info scope max time ns

  let full_check scope =
    scope.sc_options := Check_mode.full_check !(scope.sc_options);
    scope

  let check_proof scope b =
    scope.sc_options := Check_mode.check_proof !(scope.sc_options) b;
    scope
end

(* -------------------------------------------------------------------- *)
module Tactics = struct
  open EcBaseLogic
  open EcHiLogic
  open EcHiTactics

  let pi scope pi = Prover.mk_prover_info scope pi

  let process_logic scope env juc loc tacs =
    let (juc,n) =
      try get_first_goal juc
      with _ -> error loc NoCurrentGoal
    in
      EcBaseLogic.upd_done
        (fst (process_logic_tacs (pi scope) env tacs (juc,[n])))

  let process scope tac =
    if Check_mode.check !(scope.sc_options) then
      let loc = match tac with | [] -> assert false | t::_ -> t.pl_loc in
      match scope.sc_pr_uc with
      | [] -> error loc NoCurrentGoal
      | puc :: pucs ->
          let juc =
            process_logic scope scope.sc_env puc.puc_jdg loc tac
          in
            { scope with
                sc_pr_uc = { puc with puc_jdg = juc } :: pucs }
    else scope
end

(* -------------------------------------------------------------------- *)
module Op = struct
  open EcTypes
  open EcDecl
  open EcEnv

  module TT = EcTyping

  let bind (scope : scope) ((x, op) : _ * operator) =
    { scope with
        sc_env = EcEnv.Op.bind x op scope.sc_env; }

  let add (scope : scope) (op : poperator located) =
    let op = op.pl_desc and loc = op.pl_loc in
    let ue = TT.ue_for_decl scope.sc_env (loc, op.po_tyvars) in
    let tp = TT.tp_relax in

    let (ty, body) =
      match op.po_def with
      | POabstr pty ->
          TT.transty tp scope.sc_env ue pty, None

      | POconcr (bd, pty, pe) ->
          let env     = scope.sc_env in
          let codom   = TT.transty tp env ue pty in 
          let env, xs = TT.transbinding env ue bd in
          let body    = TT.transexpcast env ue codom pe in
          let lam     = EcTypes.e_lam xs body in
            lam.EcTypes.e_ty, Some lam
    in

    let uni     = Tuni.subst (EcUnify.UniEnv.close ue) in
    let body    = omap body (e_mapty uni) in
    let ty      = uni ty in
    let tparams = EcUnify.UniEnv.tparams ue in
    let tyop    = EcDecl.mk_op tparams ty body in

      bind scope (unloc op.po_name, tyop)
end

(* -------------------------------------------------------------------- *)
module Pred = struct
  module TT = EcTyping

  let add (scope : scope) (op : ppredicate located) =
    let op = op.pl_desc and loc = op.pl_loc in
    let ue     = TT.ue_for_decl scope.sc_env (loc, op.pp_tyvars) in
    let tp     = TT.tp_relax in
    let dom, body = 
      match op.pp_def with
      | PPabstr ptys -> 
        List.map (TT.transty tp scope.sc_env ue) ptys, None
      | PPconcr(bd,pe) ->
        let env, xs = TT.transbinding scope.sc_env ue bd in
        let body = TT.transformula env ue pe in
        let dom = List.map snd xs in
        let xs = List.map (fun (x,ty) -> x, EcFol.GTty ty) xs in
        let lam = EcFol.f_lambda xs body in
        dom, Some lam in
    let uni     = EcUnify.UniEnv.close ue in
    let body    = omap body (EcFol.Fsubst.uni uni) in
    let dom     = List.map (Tuni.subst uni) dom in
    let tparams = EcUnify.UniEnv.tparams ue in
    let tyop    = EcDecl.mk_pred tparams dom body in

      Op.bind scope (unloc op.pp_name, tyop)

end

(* -------------------------------------------------------------------- *)
module Ty = struct
  open EcDecl
  open EcTyping

  let bind (scope : scope) ((x, tydecl) : (_ * tydecl)) =
    { scope with
        sc_env = EcEnv.Ty.bind x tydecl scope.sc_env; }

  let add (scope : scope) info =
    let (args, name) = info.pl_desc and loc = info.pl_loc in
    let ue     = ue_for_decl scope.sc_env (loc, Some args) in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = None;
    } in
      bind scope (unloc name, tydecl)

  let define (scope : scope) info body =
    let (args, name) = info.pl_desc and loc = info.pl_loc in
    let ue     = ue_for_decl scope.sc_env (loc, Some args) in
    let body   = transty tp_tydecl scope.sc_env ue body in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = Some body;
    } in
      bind scope (unloc name, tydecl)
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  let bind (scope : scope) (m : module_expr) =
    { scope with
        sc_env = EcEnv.Mod.bind m.me_name m scope.sc_env; }

  let add (scope : scope) (name : symbol) m =
    let m = EcTyping.transmod scope.sc_env name m in
    bind scope m
end

(* -------------------------------------------------------------------- *)
module ModType = struct
  let bind (scope : scope) ((x, tysig) : _ * module_sig) =
    { scope with
        sc_env = EcEnv.ModTy.bind x tysig scope.sc_env; }

  let add (scope : scope) (name : symbol) (i : pmodule_sig) =
    let tysig = EcTyping.transmodsig scope.sc_env name i in
      bind scope (name, tysig)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  open EcTheory

  exception TopScope

  (* ------------------------------------------------------------------ *)
  let bind (scope : scope) ((x, cth) : _ * EcEnv.ctheory_w3) =
    { scope with
        sc_env = EcEnv.Theory.bind x cth scope.sc_env; }

  (* ------------------------------------------------------------------ *)
  let required (scope : scope) (name : symbol) =
    List.exists (fun x -> x = name) scope.sc_required

  (* ------------------------------------------------------------------ *)
  let enter (scope : scope) (name : symbol) =
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
        let cth    = EcEnv.Theory.close scope.sc_env in
        let loaded = scope.sc_loaded in
        let required = scope.sc_required in
        let sup = { sup with sc_loaded = loaded } in
          ((cth, required), scope.sc_name, sup)

  (* ------------------------------------------------------------------ *)
  let exit (scope : scope) =
    let ((cth, required), name, scope) = exit_r scope in
    let scope = List.fold_right require_loaded required scope in
      (name, bind scope (name, cth))

  (* ------------------------------------------------------------------ *)
  let import (scope : scope) (name : qsymbol) =
    let path = fst (EcEnv.Theory.lookup name scope.sc_env) in
    { scope with
        sc_env = EcEnv.Theory.import path scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let export (scope : scope) (name : qsymbol) =
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
    if scope.sc_pr_uc <> [] then
      let msg =
        Printf.sprintf
          "end-of-file while processing proof %s" scope.sc_name
      in
        failwith msg

  (* -------------------------------------------------------------------- *)
  let require (scope : scope) (name : symbol) loader =
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
  let clone (scope : scope) (thcl : theory_cloning) =
    let (name, nth) = EcThCloning.clone scope.sc_env thcl in
      { scope with
          sc_env =
            EcEnv.Theory.bind name nth scope.sc_env; }

  (* ------------------------------------------------------------------ *)
  let import_w3 scope dir file renaming =
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
module Ax = struct
  open EcParsetree
  open EcTypes
  open EcDecl

  module TT = EcTyping

  let bind (scope : scope) ((x, ax) : _ * axiom) =
   let res =
    { scope with
        sc_env  = EcEnv.Ax.bind x ax scope.sc_env; }
      in
   res

  let start_lemma scope name tparams concl =
    let hyps = { EcBaseLogic.h_tvar = tparams;
                 EcBaseLogic.h_local = []; } in
    let puc = {
      puc_name = name ;
      puc_jdg = EcBaseLogic.open_juc (hyps, concl) } in
    { scope with
      sc_pr_uc = puc :: scope.sc_pr_uc }

  let save scope loc =
    if Check_mode.check !(scope.sc_options) then
      match scope.sc_pr_uc with
      | [] -> EcHiLogic.error loc EcHiLogic.NoCurrentGoal
      | { puc_name = name; puc_jdg = juc } :: pucs ->
          let pr = EcBaseLogic.close_juc juc in
          let hyps,concl = (EcBaseLogic.get_goal (juc,0)).EcBaseLogic.pj_decl in
          let tparams = hyps.EcBaseLogic.h_tvar in
          assert (hyps.EcBaseLogic.h_local = []);
          let axd = { ax_tparams = tparams;
                      ax_spec = Some concl;
                      ax_kind = Lemma (Some pr) } in
          let scope = { scope with sc_pr_uc = pucs } in
          Some name, bind scope (name, axd)
    else None, scope

  let add (scope : scope) (ax : paxiom located) =
    let loc = ax.pl_loc and ax = ax.pl_desc in
    let ue = TT.ue_for_decl scope.sc_env (loc, ax.pa_tyvars) in
    let pconcl, tintro = 
      match ax.pa_vars with
      | None -> 
        ax.pa_formula, { pl_loc = loc; pl_desc = Pidtac None } 
      | Some vs -> 
        let pconcl = { pl_loc = loc; pl_desc = PFforall(vs, ax.pa_formula) } in
        let vs = List.map (fun (ids,_) -> 
          List.map (fun x -> {pl_desc = Some x.pl_desc; pl_loc = x.pl_loc}) ids)
          vs in
        pconcl, { pl_loc=loc; pl_desc = Plogic (Pintro (List.flatten vs)) } in
    let concl = TT.transformula scope.sc_env ue pconcl in
    let concl =
      EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) concl in
    let tparams = EcUnify.UniEnv.tparams ue in
    let check = Check_mode.check !(scope.sc_options) in
    match ax.pa_kind with
    | PILemma when check ->
      let scope = start_lemma scope (unloc ax.pa_name) tparams concl in
      let scope = Tactics.process scope [tintro] in
      None, scope
    | PLemma when check ->
        let scope = start_lemma scope (unloc ax.pa_name) tparams concl in
        let scope =
          Tactics.process scope
            [tintro; { pl_loc = loc; pl_desc = Plogic (Ptrivial empty_pprover) }] in
        let name, scope = save scope loc in
        name, scope
    | _ ->
        let axd = { ax_tparams = tparams;
                    ax_spec = Some concl;
                    ax_kind = Axiom } in
        Some (unloc ax.pa_name), bind scope (unloc ax.pa_name, axd)
end
