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
exception HiScopeError of EcLocation.t option * string

let pp_hi_scope_error fmt exn =
  match exn with
  | HiScopeError (None  , s) ->
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
  puc_name   : string;
  puc_jdg    : proof_state;
  puc_flags  : pucflags
}

and proof_state =
| PSCheck   of (EcLogic.judgment_uc * int list)
| PSNoCheck of (EcIdent.t list * EcFol.form)

and pucflags = {
  puc_nosmt : bool;
  puc_local : bool;
}

(* -------------------------------------------------------------------- *)
module CoreSection : sig
  open EcFol

  type locals

  val env_of_locals   : locals -> EcEnv.env
  val items_of_locals : locals -> EcTheory.ctheory_item list

  val is_local : [`Lemma | `Module] -> path -> locals -> bool
  val is_mp_local : mpath -> locals -> bool

  val use_local_instr  : instr -> locals -> bool
  val use_local_stmt   : stmt  -> locals -> bool
  val use_local_form   : form  -> locals -> bool
  val use_local_module : module_expr -> locals -> bool

  type t

  exception NoSectionOpened

  val initial : t

  val in_section : t -> bool

  val enter : EcEnv.env -> t -> t
  val exit  : t -> locals * t

  val path  : t -> path
  val opath : t -> path option

  val locals  : t -> locals
  val olocals : t -> locals option

  val addlocal : [`Lemma | `Module] -> path -> t -> t
  val additem  : EcTheory.ctheory_item -> t -> t
end = struct
  exception NoSectionOpened

  type locals = {
    lc_env     : EcEnv.env;
    lc_lemmas  : Sp.t;
    lc_modules : Sp.t;
    lc_items   : EcTheory.ctheory_item list;
  }

  let env_of_locals (lc : locals) = lc.lc_env

  let items_of_locals (lc : locals) = lc.lc_items

  let is_local who p (lc : locals) =
    let set =
      match who with
      | `Lemma  -> lc.lc_lemmas
      | `Module -> lc.lc_modules
    in
      Sp.mem p set

  let rec is_mp_local mp (lc : locals) =
    let toplocal =
      match mp.m_top with
      | `Abstract _ -> false
      | `Concrete (p, _) -> is_local `Module p lc
    in
      toplocal || (List.exists (is_mp_local^~ lc) mp.m_args)

  let is_mp_set_local mp (lc : locals) =
    Sm.exists (is_mp_local^~ lc) mp

  let rec use_local_ty (ty : ty) (lc : locals) =
    match ty.ty_node with
    | Tunivar _        -> false
    | Tvar    _        -> false
    | Tglob mp         -> is_mp_local mp lc
    | Ttuple tys       -> List.exists (use_local_ty^~ lc) tys
    | Tconstr (_, tys) -> List.exists (use_local_ty^~ lc) tys
    | Tfun (ty1, ty2)  -> List.exists (use_local_ty^~ lc) [ty1; ty2]

  let use_local_pv (pv : prog_var) (lc : locals) =
    is_mp_local pv.pv_name.x_top lc

  let use_local_lp (lp : lpattern) (lc : locals) =
    match lp with
    | LSymbol (_, ty) -> use_local_ty ty lc
    | LTuple  xs      -> List.exists (fun (_, ty) -> use_local_ty ty lc) xs

  let rec use_local_expr (e : expr) (lc : locals) =
    let uselc = use_local_expr^~ lc in

    let fornode () =
      match e.e_node with
      | Eint   _            -> false
      | Elocal _            -> false
      | Evar   _            -> false
      | Elam   (xs, e)      -> List.exists (fun (_, ty) -> use_local_ty ty lc) xs || uselc e
      | Eop    (_, tys)     -> List.exists (use_local_ty^~ lc) tys
      | Eapp   (e, es)      -> List.exists uselc (e :: es)
      | Elet   (lp, e1, e2) -> use_local_lp lp lc || List.exists uselc [e1; e2]
      | Etuple es           -> List.exists uselc es
      | Eif    (e1, e2, e3) -> List.exists uselc [e1; e2; e3]
    in
      use_local_ty e.e_ty lc || fornode ()

  let use_local_lv (lv : lvalue) (lc : locals) =
    let for1 (pv, ty) = use_local_pv pv lc && use_local_ty ty lc in

      match lv with
      | LvVar   pv  -> for1 pv
      | LvTuple pvs -> List.exists for1 pvs

      | LvMap ((_, pty), pv, e, ty) ->
            List.exists (use_local_ty^~ lc) pty
         || use_local_ty    ty lc
         || use_local_pv    pv lc
         || use_local_expr   e lc

  let rec use_local_instr (i : instr) (lc : locals) =
    match i.i_node with
    | Sasgn   _ -> false
    | Srnd    _ -> false
    | Sassert _ -> false

    | Scall (_, f, _) -> is_mp_local f.x_top lc
    | Sif (_, s1, s2) -> List.exists (use_local_stmt^~ lc) [s1; s2]
    | Swhile (_, s)   -> use_local_stmt s lc

  and use_local_stmt (s : stmt) (lc : locals) =
    List.exists (use_local_instr^~ lc) s.s_node

  let use_local_lcmem m lc =
       is_mp_local (EcMemory.lmt_xpath m).x_top lc
    || Msym.exists (fun _ ty -> use_local_ty ty lc) (EcMemory.lmt_bindings m)

  let use_local_memenv (m : EcMemory.memenv) (lc : locals) =
    match snd m with
    | None    -> false
    | Some lm -> use_local_lcmem lm lc

  let rec use_local_modty mty lc =
       List.exists (fun (_, mty) -> use_local_modty mty lc) mty.mt_params
    || List.exists (is_mp_local^~ lc) mty.mt_args

  let use_local_binding b (lc : locals) =
    match b with
    | EcFol.GTty    ty        -> use_local_ty ty lc
    | EcFol.GTmodty (mty, sm) -> use_local_modty mty lc || is_mp_set_local sm lc
    | EcFol.GTmem   None      -> false
    | EcFol.GTmem   (Some m)  -> use_local_lcmem m lc

  let use_local_bindings b lc =
    List.exists (fun (_, b) -> use_local_binding b lc) b

  let rec use_local_form (f : EcFol.form) (lc : locals) =
    let uselc = use_local_form^~ lc in

    let rec fornode () =
      match f.EcFol.f_node with
      | EcFol.Fint      _            -> false
      | EcFol.Flocal    _            -> false
      | EcFol.Fquant    (_, b, f)    -> use_local_bindings b lc || uselc f
      | EcFol.Fif       (f1, f2, f3) -> List.exists uselc [f1; f2; f3]
      | EcFol.Flet      (_, f1, f2)  -> List.exists uselc [f1; f2]
      | EcFol.Fop       (_, ty)      -> List.exists (use_local_ty^~ lc) ty
      | EcFol.Fapp      (f, fs)      -> List.exists uselc (f :: fs)
      | EcFol.Ftuple    fs           -> List.exists uselc fs
      | EcFol.Fpvar     (pv, _)      -> use_local_pv  pv  lc
      | EcFol.Fglob     (mp, _)      -> is_mp_local   mp  lc
      | EcFol.FhoareF   hf           -> use_local_hf  hf  lc
      | EcFol.FhoareS   hs           -> use_local_hs  hs  lc
      | EcFol.FequivF   ef           -> use_local_ef  ef  lc
      | EcFol.FequivS   es           -> use_local_es  es  lc
      | EcFol.FbdHoareS bhs          -> use_local_bhs bhs lc
      | EcFol.FbdHoareF bhf          -> use_local_bhf bhf lc
      | EcFol.Fpr       pr           -> use_local_pr  pr  lc

    and use_local_hf hf lc =
         use_local_form hf.EcFol.hf_pr lc
      || use_local_form hf.EcFol.hf_po lc
      || is_mp_local hf.EcFol.hf_f.x_top lc

    and use_local_hs hs lc =
         use_local_form hs.EcFol.hs_pr lc
      || use_local_form hs.EcFol.hs_po lc
      || use_local_stmt hs.EcFol.hs_s lc
      || use_local_memenv hs.EcFol.hs_m lc

    and use_local_ef ef lc =
         use_local_form ef.EcFol.ef_pr lc
      || use_local_form ef.EcFol.ef_po lc
      || is_mp_local ef.EcFol.ef_fl.x_top lc
      || is_mp_local ef.EcFol.ef_fr.x_top lc

    and use_local_es es lc =
         use_local_form es.EcFol.es_pr lc
      || use_local_form es.EcFol.es_po lc
      || use_local_stmt es.EcFol.es_sl lc
      || use_local_stmt es.EcFol.es_sr lc
      || use_local_memenv es.EcFol.es_ml lc
      || use_local_memenv es.EcFol.es_mr lc

    and use_local_bhf bhf lc =
         use_local_form bhf.EcFol.bhf_pr lc
      || use_local_form bhf.EcFol.bhf_po lc
      || use_local_form bhf.EcFol.bhf_bd lc
      || is_mp_local bhf.EcFol.bhf_f.x_top lc

    and use_local_bhs bhs lc =
         use_local_form bhs.EcFol.bhs_pr lc
      || use_local_form bhs.EcFol.bhs_po lc
      || use_local_form bhs.EcFol.bhs_bd lc
      || use_local_stmt bhs.EcFol.bhs_s lc
      || use_local_memenv bhs.EcFol.bhs_m lc

    and use_local_pr (_, xp, fs, f) lc =
         is_mp_local xp.x_top lc
      || List.exists (use_local_form^~ lc) (f :: fs)

    in
      use_local_ty f.EcFol.f_ty lc || fornode ()

  let rec use_local_module (me : module_expr) (lc : locals) =
    match me.me_body with
    | ME_Alias     mp   -> is_mp_local       mp lc
    | ME_Structure st   -> use_local_mstruct st lc
    | ME_Decl (mty, sm) -> use_local_mdecl (mty, sm) lc

  and use_local_mdecl dc lc =
       use_local_modty (fst dc) lc
    || Sm.exists (is_mp_local^~ lc) (snd dc)

  and use_local_mstruct st lc =
    List.exists (use_local_mstruct1^~ lc) st.ms_body

  and use_local_mstruct1 item lc =
    match item with
    | MI_Module   me -> use_local_module me lc
    | MI_Variable x  -> use_local_ty x.v_type lc
    | MI_Function f  -> use_local_fun f lc

  and use_local_fun fun_ lc =
       use_local_fun_sig  fun_.f_sig lc
    || use_local_fun_body fun_.f_def lc

  and use_local_fun_sig fsig lc =
       List.exists (fun v -> use_local_ty v.v_type lc) fsig.fs_params
    || use_local_ty fsig.fs_ret lc

  and use_local_fun_body fbody lc =
    match fbody with
    | FBdef fdef -> use_local_fun_def fdef lc
    | FBabs oi   -> use_local_fun_oi  oi   lc

  and use_local_fun_def fdef lc =
       List.exists (fun v -> use_local_ty v.v_type lc) fdef.f_locals
    || use_local_stmt fdef.f_body lc
    || odfl false (omap fdef.f_ret (use_local_expr^~ lc))
    || use_local_uses fdef.f_uses lc

  and use_local_uses uses lc =
       List.exists (fun x -> is_mp_local x.x_top lc) uses.us_calls
    || Sx.exists (fun x -> is_mp_local x.x_top lc) uses.us_reads
    || Sx.exists (fun x -> is_mp_local x.x_top lc) uses.us_writes

  and use_local_fun_oi oi lc =
    List.exists (fun x -> is_mp_local x.x_top lc) oi.oi_calls

  let elocals (env : EcEnv.env) : locals =
    { lc_env     = env;
      lc_lemmas  = Sp.empty;
      lc_modules = Sp.empty;
      lc_items   = []; }

  type t = locals list

  let initial : t = []

  let in_section (cs : t) =
    match cs with [] -> false | _ -> true

  let enter (env : EcEnv.env) (cs : t) : t =
    match List.ohead cs with
    | None   -> [elocals env]
    | Some x -> {x with lc_env = env; lc_items = []; } :: cs

  let exit (cs : t) =
    match cs with
    | [] -> raise NoSectionOpened
    | ec :: cs -> ({ ec with lc_items = List.rev ec.lc_items }, cs)

  let path (cs : t) : path =
    match cs with
    | [] -> raise NoSectionOpened
    | ec :: _ -> EcEnv.root ec.lc_env

  let opath (cs : t) =
    try Some (path cs) with NoSectionOpened -> None

  let locals (cs : t) : locals =
    match cs with
    | [] -> raise NoSectionOpened
    | ec :: _ -> ec

  let olocals (cs : t) =
    try Some (locals cs) with NoSectionOpened -> None

  let onactive (f : locals -> locals) (cs : t) =
    match cs with
    | []      -> raise NoSectionOpened
    | c :: cs -> (f c) :: cs

  let addlocal who (p : path) (cs : t) : t =
    let doit ec =
      match who with
      | `Lemma  -> { ec with lc_lemmas  = Sp.add p ec.lc_lemmas  }
      | `Module -> { ec with lc_modules = Sp.add p ec.lc_modules }
    in
      onactive doit cs

  let additem item (cs : t) : t =
    let doit ec = { ec with lc_items = item :: ec.lc_items } in
      onactive doit cs
end

(* -------------------------------------------------------------------- *)
type scope = {
  sc_name     : symbol;
  sc_env      : EcEnv.env;
  sc_top      : scope option;
  sc_loaded   : (EcEnv.ctheory_w3 * symbol list) Msym.t;
  sc_required : symbol list;
  sc_pr_uc    : (bool option * proof_uc) option;
  sc_options  : Options.options;
  sc_section  : CoreSection.t;
}

(* -------------------------------------------------------------------- *)
let empty =
  let env = EcEnv.initial in
    { sc_name       = EcPath.basename (EcEnv.root env);
      sc_env        = EcEnv.initial;
      sc_top        = None;
      sc_loaded     = Msym.empty;
      sc_required   = [];
      sc_pr_uc      = None;
      sc_options    = Options.init ();
      sc_section    = CoreSection.initial;
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
  omap scope.sc_pr_uc snd

(* -------------------------------------------------------------------- *)
let xgoal (scope : scope) =
  scope.sc_pr_uc

(* -------------------------------------------------------------------- *)
let check_state mode action (scope : scope) =
  match mode with
  | `InProof when scope.sc_pr_uc = None ->
      hierror "cannot process [%s] outside a proof script" action

  | `InTop when scope.sc_pr_uc <> None ->
      hierror "cannot process [%s] inside a proof script" action

  | _ -> ()

(* -------------------------------------------------------------------- *)
let verbose (scope : scope) =
  match Notifier.verbose scope.sc_options with
  | `ForLoading -> false
  | `Verbose b  -> b

(* -------------------------------------------------------------------- *)
let set_verbose (scope : scope) (b : bool) =
  { scope with sc_options = Notifier.set scope.sc_options b }

(* -------------------------------------------------------------------- *)
let for_loading (scope : scope) =
  { empty with
      sc_loaded  = scope.sc_loaded;
      sc_options = Options.for_loading scope.sc_options; }

(* -------------------------------------------------------------------- *)
let subscope (scope : scope) (name : symbol) =
  let env = EcEnv.Theory.enter name scope.sc_env in

  { sc_name       = name;
    sc_env        = env;
    sc_top        = Some scope;
    sc_loaded     = scope.sc_loaded;
    sc_required   = scope.sc_required;
    sc_pr_uc      = None;
    sc_options    = Options.for_subscope scope.sc_options;
    sc_section    = scope.sc_section;
  }

(* -------------------------------------------------------------------- *)
let maybe_add_to_section scope item =
  match CoreSection.opath scope.sc_section with
  | None    -> scope
  | Some sp -> begin
      match EcPath.p_equal sp (EcEnv.root scope.sc_env) with
      | false -> scope
      | true  ->
        let ec = CoreSection.additem item scope.sc_section in
          { scope with sc_section = ec }
  end

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
    let dft = Prover_info.get scope.sc_options in
    let time = odfl dft.EcProvers.prover_timelimit time in
    let time = if time < 1 then 1 else time in
    let provers = odfl dft.EcProvers.prover_names ns in
    let provers = Array.to_list provers in
    let max     = odfl dft.EcProvers.prover_max_run max in
    { EcProvers.prover_max_run   = max;
      EcProvers.prover_names     = Array.of_list provers;
      EcProvers.prover_timelimit = time }

  let set_prover_info scope max time ns =
    let pi = mk_prover_info scope max time ns in
      { scope with sc_options = Prover_info.set scope.sc_options pi }

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
    { scope with sc_options = Check_mode.full_check scope.sc_options }

  let check_proof scope b =
    { scope with sc_options = Check_mode.check_proof scope.sc_options b }
end

(* -------------------------------------------------------------------- *)
module Tactics = struct
  open EcLogic
  open EcHiLogic
  open EcHiTactics

  let pi scope pi = Prover.mk_prover_info scope pi

  let proof (scope : scope) mode (strict : bool) =
    check_state `InProof "proof script" scope;

    let (m, puc) = oget scope.sc_pr_uc in
    let (m, puc) =
      match m with
      | None when not strict && mode = `WeakCheck -> begin
          match puc.puc_jdg with
          | PSNoCheck _ -> (false, puc)
          | PSCheck (juc, _) ->
              let hyps, concl = (EcLogic.get_pj (juc, 0)).EcLogic.pj_decl in
              let hyps    = EcEnv.LDecl.tohyps hyps in
              let tparams = hyps.EcBaseLogic.h_tvar in
              let puc     = { puc with puc_jdg = PSNoCheck (tparams, concl) } in
                (false, puc)
      end
  
      | None   -> (strict, puc)
      | Some _ -> hierror "[proof] can only be used at beginning of a proof script"
    in
      { scope with sc_pr_uc = Some (Some m, puc) }

  let process_tactic_on_goal hitenv (juc, ns) loc tacs =
    match ns with
    | []      -> error loc NoCurrentGoal
    | n :: ns ->
      let juc = process_tactics hitenv tacs (juc, [n]) in
      let juc = fst_map EcLogic.upd_done juc in
      let juc = (fst juc, (snd juc) @ ns) in

      snd_map (List.filter (List.mem^~ (snd (find_all_goals (fst juc))))) juc

  let process_r mark mode (scope : scope) (tac : ptactic list) =
    check_state `InProof "proof script" scope;

    let scope =
      if   mark && fst (oget scope.sc_pr_uc) = None
      then proof scope mode false
      else scope
    in

    let (m, puc) = oget scope.sc_pr_uc in

    match puc.puc_jdg with
    | PSNoCheck _ -> scope
    | PSCheck juc ->
        let loc = (oget (List.ohead tac)).pt_core.pl_loc in

        let htmode =
          match m, mode with
          | Some true , `WeakCheck -> `Admit
          | _         , `WeakCheck ->  hierror "cannot weak-check a non-strict proof script"
          | Some true , `Check     -> `Strict
          | Some false, `Check     -> `Standard
          | _         , `Check     -> `Strict
        in

        let hitenv = { hte_provers = pi scope; hte_smtmode = htmode; } in

        let juc = process_tactic_on_goal hitenv juc loc tac in
        let puc = { puc with puc_jdg = PSCheck juc; } in
          { scope with sc_pr_uc = Some (m, puc); }

  let process_core mark mode (scope : scope) (ts : ptactic_core list) =
    let ts = List.map (fun t -> { pt_core = t; pt_intros = []; }) ts in
      process_r mark mode scope ts

  let process scope mode tac =
    process_r true mode scope tac
end

(* -------------------------------------------------------------------- *)
module Op = struct
  open EcTypes
  open EcDecl
  open EcEnv

  module TT = EcTyping

  let bind (scope : scope) ((x, op) : _ * operator) =
    assert (scope.sc_pr_uc = None);
    let scope = { scope with sc_env = EcEnv.Op.bind x op scope.sc_env } in
    let scope = maybe_add_to_section scope (EcTheory.CTh_operator (x, op)) in
      scope

  let add (scope : scope) (op : poperator located) =
    assert (scope.sc_pr_uc = None);
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

    if op.po_kind = `Const then begin
      let tue, ty, _ = EcUnify.UniEnv.freshen ue tparams None ty in
      let tdom = EcUnify.UniEnv.fresh_uid tue in
      let tcom = EcUnify.UniEnv.fresh_uid tue in
      let tfun = EcTypes.tfun tdom tcom in

        try
          EcUnify.unify (env scope) tue ty tfun;
          let msg = "this operator type is (unifiable) to an function type" in
            hierror ~loc "%s" msg
        with EcUnify.UnificationFailure _ -> ()
    end;

    bind scope (unloc op.po_name, tyop)
end

(* -------------------------------------------------------------------- *)
module Pred = struct
  module TT = EcTyping

  let add (scope : scope) (op : ppredicate located) =
    assert (scope.sc_pr_uc = None);
    let op = op.pl_desc and loc = op.pl_loc in
    let ue     = TT.ue_for_decl scope.sc_env (loc, op.pp_tyvars) in
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
    assert (scope.sc_pr_uc = None);
    let scope = { scope with sc_env = EcEnv.Ty.bind x tydecl scope.sc_env; } in
    let scope = maybe_add_to_section scope (EcTheory.CTh_type (x, tydecl)) in
      scope

  let add (scope : scope) info =
    assert (scope.sc_pr_uc = None);
    let (args, name) = info.pl_desc and loc = info.pl_loc in
    let ue     = ue_for_decl scope.sc_env (loc, Some args) in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = None;
    } in
      bind scope (unloc name, tydecl)

  let define (scope : scope) info body =
    assert (scope.sc_pr_uc = None);
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
        let ec = CoreSection.addlocal `Module mpath scope.sc_section in
          { scope with sc_section = ec }
    in
      scope

  let add (scope : scope) (ptm : ptopmodule) =
    assert (scope.sc_pr_uc = None);

    if ptm.ptm_local && not (CoreSection.in_section scope.sc_section) then
      hierror "cannot declare a local module outside of a section";

    let (name, m) = ptm.ptm_def in
    let m = EcTyping.transmod scope.sc_env (unloc name) m in

    if not ptm.ptm_local then begin
      match CoreSection.olocals scope.sc_section with
      | None -> ()
      | Some locals ->
          if CoreSection.use_local_module m locals then
            hierror "this module use local modules and must be declared as local"
    end;

      bind scope ptm.ptm_local m
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
module Theory = struct
  open EcTheory

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
          match CoreSection.opath scope.sc_section with
          | None -> ()
          | Some sp ->
              if p_equal sp (EcEnv.root scope.sc_env) then
                hierror "cannot close a theory with active sessions";
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
  let clone (scope : scope) (thcl : theory_cloning) =
    assert (scope.sc_pr_uc = None);

    if CoreSection.in_section scope.sc_section then
      hierror "cannot clone a theory while a section is active";

    let (name, nth) = EcThCloning.clone scope.sc_env thcl in
    let scope = { scope with sc_env = EcEnv.Theory.bind name nth scope.sc_env; } in
      (name, scope)

  (* ------------------------------------------------------------------ *)
  let import_w3 scope dir file renaming =
    assert (scope.sc_pr_uc = None);

    if CoreSection.in_section scope.sc_section then
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
module Ax = struct
  open EcParsetree
  open EcTypes
  open EcDecl

  module TT = EcTyping

  type mode = [`WeakCheck | `Check]

  (* ------------------------------------------------------------------ *)
  let bind (scope : scope) local ((x, ax) : _ * axiom) =
    assert (scope.sc_pr_uc = None);
    let scope = { scope with sc_env = EcEnv.Ax.bind x ax scope.sc_env; } in
    let scope = maybe_add_to_section scope (EcTheory.CTh_axiom (x, ax)) in
    let scope =
      match local with
      | false -> scope
      | true  ->
        let axpath = EcPath.pqname (path scope) x in
        let ec = CoreSection.addlocal `Lemma axpath scope.sc_section in
          { scope with sc_section = ec }
    in
      scope

  (* ------------------------------------------------------------------ *)
  let start_lemma scope axflags check name tparams concl =
    let puc =
      match check with
      | false -> PSNoCheck (tparams, concl)
      | true  ->
          let hyps = EcEnv.LDecl.init scope.sc_env tparams in
            PSCheck (EcLogic.open_juc (hyps, concl), [0])
    in 
    let puc = { puc_name = name; puc_jdg = puc; puc_flags = axflags; } in
      { scope with sc_pr_uc = Some (None, puc) }

  (* ------------------------------------------------------------------ *)
  let save scope _loc =
    check_state `InProof "save" scope;

    let (_, puc) = oget scope.sc_pr_uc in
    let (tparams, concl, kind) =
      match puc.puc_jdg with
      | PSCheck (juc, _) ->
          ignore (EcLogic.close_juc juc);
          let hyps, concl = (EcLogic.get_pj (juc, 0)).EcLogic.pj_decl in
          let hyps = EcEnv.LDecl.tohyps hyps in
          let tparams = hyps.EcBaseLogic.h_tvar in
            assert (hyps.EcBaseLogic.h_local = []);
            (tparams, concl, `Lemma)

      | PSNoCheck (tparams, concl) ->
          (tparams, concl, `Axiom)
    in
    let axd = { ax_tparams = tparams;
                ax_spec    = Some concl;
                ax_kind    = kind;
                ax_nosmt   = puc.puc_flags.puc_nosmt; }
    in
    let scope = { scope with sc_pr_uc = None } in
    let scope = bind scope puc.puc_flags.puc_local (puc.puc_name, axd) in
      (Some puc.puc_name, scope)

  (* ------------------------------------------------------------------ *)
  let add (scope : scope) mode (ax : paxiom located) =
    assert (scope.sc_pr_uc = None);

    let loc = ax.pl_loc and ax = ax.pl_desc in
    let ue  = TT.ue_for_decl scope.sc_env (loc, ax.pa_tyvars) in

    if ax.pa_local && not (CoreSection.in_section scope.sc_section) then
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
        (fun x -> IPCore (mk_loc x.pl_loc (`noRename x.pl_desc)))
        tintro in
    let tintro = mk_loc loc (Plogic (Pintro tintro)) in

    let concl    = TT.trans_prop scope.sc_env ue pconcl in
    let concl    = EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) concl in
    let tparams  = EcUnify.UniEnv.tparams ue in
    let check    = Check_mode.check scope.sc_options in
    let pucflags = { puc_nosmt = ax.pa_nosmt; puc_local = ax.pa_local; } in

    if not ax.pa_local then begin
      match CoreSection.olocals scope.sc_section with
      | None -> ()
      | Some locals ->
          if CoreSection.use_local_form concl locals then
            hierror "this lemma uses local modules and must be declared as local"
    end;

    match ax.pa_kind with
    | PILemma ->
        let scope = start_lemma scope pucflags check (unloc ax.pa_name) tparams concl in
        let scope = Tactics.process_core false `Check scope [tintro] in
          None, scope

    | PLemma tc ->
        let scope = start_lemma scope pucflags check (unloc ax.pa_name) tparams concl in
        let scope = Tactics.process_core false `Check scope [tintro] in
        let scope = Tactics.proof scope mode (if tc = None then true else false) in

        let tc =
          match tc with
          | Some tc -> [tc]
          | None    ->
              let dtc = Plogic (Psmt empty_pprover) in
              let dtc = [{ pl_loc = loc; pl_desc = dtc }] in
              let dtc = List.map (fun t -> { pt_core = t; pt_intros = []; }) dtc in
                dtc
        in

        let scope = Tactics.process_r false mode scope tc in
          save scope loc

    | PAxiom ->
        let axd = { ax_tparams = tparams;
                    ax_spec    = Some concl;
                    ax_kind    = `Axiom;
                    ax_nosmt   = ax.pa_nosmt; }
        in
          Some (unloc ax.pa_name),
          bind scope pucflags.puc_local (unloc ax.pa_name, axd)
end

(* -------------------------------------------------------------------- *)
module Section = struct
  module T = EcTheory

  let enter (scope : scope) =
    assert (scope.sc_pr_uc = None);
    { scope with
        sc_section = CoreSection.enter scope.sc_env scope.sc_section }

  let exit (scope : scope) =
    match CoreSection.opath scope.sc_section with
    | None -> hierror "no section to close"
    | Some sp ->
        if not (p_equal sp (EcEnv.root (scope.sc_env))) then
          hierror "cannot close a section containing pending theories";
        let (locals, osc) = CoreSection.exit scope.sc_section in
        let oenv   = CoreSection.env_of_locals locals in
        let oitems = CoreSection.items_of_locals locals in
        let scope  = { scope with sc_env = oenv; sc_section = osc; } in

        let rec bind1 scope item =
          match item with
          | T.CTh_type     (x, ty) -> Ty.bind scope (x, ty)
          | T.CTh_operator (x, op) -> Op.bind scope (x, op)
          | T.CTh_modtype  (x, mt) -> ModType.bind scope (x, mt)

          | T.CTh_module me ->
            let mep = EcPath.pqname (path scope) me.me_name in
              if not (CoreSection.is_local `Module mep locals) then
                Mod.bind scope false me
              else
                scope

          | T.CTh_axiom (x, ax) ->
            let axp = EcPath.pqname (path scope) x in
              if not (CoreSection.is_local `Lemma axp locals) then
                Ax.bind scope false (x, ax)
              else
                scope

          | T.CTh_export p ->
              { scope with sc_env = EcEnv.Theory.export p scope.sc_env }

          | T.CTh_theory (x, th) ->
              let scope = Theory.enter scope x in
              let scope = List.fold_left bind1 scope th.EcTheory.cth_struct in
              let _, scope = Theory.exit scope in
                scope
        in

        List.fold_left bind1 scope oitems
end
