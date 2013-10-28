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

and proof_state =
| PSCheck   of (EcLogic.judgment_uc * int list)
| PSNoCheck

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

  val form_use_local : form  -> locals -> bool
  val module_use_local_or_abs : module_expr -> locals -> bool

  val abstracts : locals -> (EcIdent.t * (module_type * mod_restr)) list * Sid.t

  val generalize : EcEnv.env -> locals -> form -> form

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

  type lvl = [`Local | `Global] * [`Axiom | `Lemma]

  val add_local_mod : path -> t -> t
  val add_lemma     : path -> lvl -> t -> t
  val add_item      : EcTheory.ctheory_item -> t -> t
  val add_abstract  : EcIdent.t -> (module_type * mod_restr) -> t -> t
end = struct
  exception NoSectionOpened

  type lvl = [`Local | `Global] * [`Axiom | `Lemma]

  type locals = {
    lc_env       : EcEnv.env;
    lc_lemmas    : (path * lvl) list * lvl Mp.t;
    lc_modules   : Sp.t;
    lc_abstracts : (EcIdent.t * (module_type * mod_restr)) list * Sid.t;
    lc_items     : EcTheory.ctheory_item list;
  }

  let env_of_locals (lc : locals) = lc.lc_env

  let items_of_locals (lc : locals) = lc.lc_items

  let is_local who p (lc : locals) =
    match who with
    | `Lemma  -> Mp.find_opt p (snd lc.lc_lemmas) |> omap fst = Some `Local
    | `Module -> Sp.mem p lc.lc_modules

  let rec is_mp_local mp (lc : locals) =
    let toplocal =
      match mp.m_top with
      | `Local _ -> false
      | `Concrete (p, _) -> is_local `Module p lc
    in
      toplocal || (List.exists (is_mp_local^~ lc) mp.m_args)

  let rec is_mp_abstract mp (lc : locals) =
    let toplocal =
      match mp.m_top with
      | `Concrete _ -> false
      | `Local i -> Sid.mem i (snd lc.lc_abstracts)
    in
      toplocal || (List.exists (is_mp_abstract^~ lc) mp.m_args)

  let rec on_mpath_ty cb (ty : ty) =
    match ty.ty_node with
    | Tunivar _        -> ()
    | Tvar    _        -> ()
    | Tglob mp         -> cb mp
    | Ttuple tys       -> List.iter (on_mpath_ty cb) tys
    | Tconstr (_, tys) -> List.iter (on_mpath_ty cb) tys
    | Tfun (ty1, ty2)  -> List.iter (on_mpath_ty cb) [ty1; ty2]

  let on_mpath_pv cb (pv : prog_var)=
    cb pv.pv_name.x_top

  let on_mpath_lp cb (lp : lpattern) =
    match lp with
    | LSymbol (_, ty) -> on_mpath_ty cb ty
    | LTuple  xs      -> List.iter (fun (_, ty) -> on_mpath_ty cb ty) xs

  let rec on_mpath_expr cb (e : expr) =
    let cbrec = on_mpath_expr cb in

    let fornode () =
      match e.e_node with
      | Eint   _            -> ()
      | Elocal _            -> ()
      | Evar   _            -> ()
      | Eop    (_, tys)     -> List.iter (on_mpath_ty cb) tys
      | Eapp   (e, es)      -> List.iter cbrec (e :: es)
      | Elet   (lp, e1, e2) -> on_mpath_lp cb lp; List.iter cbrec [e1; e2]
      | Etuple es           -> List.iter cbrec es
      | Eif    (e1, e2, e3) -> List.iter cbrec [e1; e2; e3]
      | Elam   (xs, e)      ->
          List.iter (fun (_, ty) -> on_mpath_ty cb ty) xs;
          cbrec e
    in
      on_mpath_ty cb e.e_ty;  fornode ()

  let on_mpath_lv cb (lv : lvalue) =
    let for1 (pv, ty) = on_mpath_pv cb pv; on_mpath_ty cb ty in

      match lv with
      | LvVar   pv  -> for1 pv
      | LvTuple pvs -> List.iter for1 pvs

      | LvMap ((_, pty), pv, e, ty) ->
          List.iter (on_mpath_ty cb) pty;
          on_mpath_ty   cb ty;
          on_mpath_pv   cb pv;
          on_mpath_expr cb e

  let rec on_mpath_instr cb (i : instr)=
    match i.i_node with
    | Sasgn   _ -> ()
    | Srnd    _ -> ()
    | Sassert _ -> ()
    | Sabstract _ -> ()

    | Scall (_, f, _) -> cb f.x_top
    | Sif (_, s1, s2) -> List.iter (on_mpath_stmt cb) [s1; s2]
    | Swhile (_, s)   -> on_mpath_stmt cb s


  and on_mpath_stmt cb (s : stmt) =
    List.iter (on_mpath_instr cb) s.s_node

  let on_mpath_lcmem cb m =
      cb (EcMemory.lmt_xpath m).x_top;
      Msym.iter (fun _ ty -> on_mpath_ty cb ty) (EcMemory.lmt_bindings m)

  let on_mpath_memenv cb (m : EcMemory.memenv) =
    match snd m with
    | None    -> ()
    | Some lm -> on_mpath_lcmem cb lm

  let rec on_mpath_modty cb mty =
    List.iter (fun (_, mty) -> on_mpath_modty cb mty) mty.mt_params;
    List.iter cb mty.mt_args

  let on_mpath_binding cb b =
    match b with
    | EcFol.GTty    ty        -> on_mpath_ty cb ty
    | EcFol.GTmodty (mty, (rx,r)) -> 
      on_mpath_modty cb mty; 
      Sx.iter (fun x -> cb x.x_top) rx; 
      Sm.iter cb r
    | EcFol.GTmem   None      -> ()
    | EcFol.GTmem   (Some m)  -> on_mpath_lcmem cb m

  let on_mpath_bindings cb b =
    List.iter (fun (_, b) -> on_mpath_binding cb b) b

  let rec on_mpath_form cb (f : EcFol.form) =
    let cbrec = on_mpath_form cb in

    let rec fornode () =
      match f.EcFol.f_node with
      | EcFol.Fint      _            -> ()
      | EcFol.Flocal    _            -> ()
      | EcFol.Fquant    (_, b, f)    -> on_mpath_bindings cb b; cbrec f
      | EcFol.Fif       (f1, f2, f3) -> List.iter cbrec [f1; f2; f3]
      | EcFol.Flet      (_, f1, f2)  -> List.iter cbrec [f1; f2]
      | EcFol.Fop       (_, ty)      -> List.iter (on_mpath_ty cb) ty
      | EcFol.Fapp      (f, fs)      -> List.iter cbrec (f :: fs)
      | EcFol.Ftuple    fs           -> List.iter cbrec fs
      | EcFol.Fpvar     (pv, _)      -> on_mpath_pv  cb pv
      | EcFol.Fglob     (mp, _)      -> cb mp
      | EcFol.FhoareF   hf           -> on_mpath_hf  cb hf
      | EcFol.FhoareS   hs           -> on_mpath_hs  cb hs
      | EcFol.FequivF   ef           -> on_mpath_ef  cb ef
      | EcFol.FequivS   es           -> on_mpath_es  cb es
      | EcFol.FeagerF   eg           -> on_mpath_eg  cb eg
      | EcFol.FbdHoareS bhs          -> on_mpath_bhs cb bhs
      | EcFol.FbdHoareF bhf          -> on_mpath_bhf cb bhf
      | EcFol.Fpr       pr           -> on_mpath_pr  cb pr

    and on_mpath_hf cb hf =
      on_mpath_form cb hf.EcFol.hf_pr;
      on_mpath_form cb hf.EcFol.hf_po;
      cb hf.EcFol.hf_f.x_top

    and on_mpath_hs cb hs =
      on_mpath_form cb hs.EcFol.hs_pr;
      on_mpath_form cb hs.EcFol.hs_po;
      on_mpath_stmt cb hs.EcFol.hs_s;
      on_mpath_memenv cb hs.EcFol.hs_m

    and on_mpath_ef cb ef =
      on_mpath_form cb ef.EcFol.ef_pr;
      on_mpath_form cb ef.EcFol.ef_po;
      cb ef.EcFol.ef_fl.x_top;
      cb ef.EcFol.ef_fr.x_top

    and on_mpath_es cb es =
      on_mpath_form cb es.EcFol.es_pr;
      on_mpath_form cb es.EcFol.es_po;
      on_mpath_stmt cb es.EcFol.es_sl;
      on_mpath_stmt cb es.EcFol.es_sr;
      on_mpath_memenv cb es.EcFol.es_ml;
      on_mpath_memenv cb es.EcFol.es_mr

    and on_mpath_eg cb eg =
      on_mpath_form cb eg.EcFol.eg_pr;
      on_mpath_form cb eg.EcFol.eg_po;
      cb eg.EcFol.eg_fl.x_top;
      cb eg.EcFol.eg_fr.x_top;
      on_mpath_stmt cb eg.EcFol.eg_sl;
      on_mpath_stmt cb eg.EcFol.eg_sr;

    and on_mpath_bhf cb bhf =
      on_mpath_form cb bhf.EcFol.bhf_pr;
      on_mpath_form cb bhf.EcFol.bhf_po;
      on_mpath_form cb bhf.EcFol.bhf_bd;
      cb bhf.EcFol.bhf_f.x_top

    and on_mpath_bhs cb bhs =
      on_mpath_form cb bhs.EcFol.bhs_pr;
      on_mpath_form cb bhs.EcFol.bhs_po;
      on_mpath_form cb bhs.EcFol.bhs_bd;
      on_mpath_stmt cb bhs.EcFol.bhs_s;
      on_mpath_memenv cb bhs.EcFol.bhs_m

    and on_mpath_pr cb (_, xp, fs, f) =
      cb xp.x_top;
      List.iter (on_mpath_form cb) (f :: fs)

    in
      on_mpath_ty cb f.EcFol.f_ty; fornode ()

  let rec on_mpath_module cb (me : module_expr) =
    match me.me_body with
    | ME_Alias     mp   -> cb mp
    | ME_Structure st   -> on_mpath_mstruct cb st
    | ME_Decl (mty, sm) -> on_mpath_mdecl cb (mty, sm)

  and on_mpath_mdecl cb (mty,(rx,r)) =
    on_mpath_modty cb mty; 
    Sx.iter (fun x -> cb x.x_top) rx; 
    Sm.iter cb r
  
  and on_mpath_mstruct cb st =
    List.iter (on_mpath_mstruct1 cb) st.ms_body

  and on_mpath_mstruct1 cb item =
    match item with
    | MI_Module   me -> on_mpath_module cb me
    | MI_Variable x  -> on_mpath_ty cb x.v_type
    | MI_Function f  -> on_mpath_fun cb f

  and on_mpath_fun cb fun_ =
    on_mpath_fun_sig  cb fun_.f_sig;
    on_mpath_fun_body cb fun_.f_def

  and on_mpath_fun_sig cb fsig =
    List.iter (fun v -> on_mpath_ty cb v.v_type) fsig.fs_params;
    on_mpath_ty cb fsig.fs_ret

  and on_mpath_fun_body cb fbody =
    match fbody with
    | FBdef fdef -> on_mpath_fun_def cb fdef
    | FBabs oi   -> on_mpath_fun_oi  cb oi

  and on_mpath_fun_def cb fdef =
    List.iter (fun v -> on_mpath_ty cb v.v_type) fdef.f_locals;
    on_mpath_stmt cb fdef.f_body;
    fdef.f_ret |> oiter (on_mpath_expr cb);
    on_mpath_uses cb fdef.f_uses

  and on_mpath_uses cb uses =
    List.iter (fun x -> cb x.x_top) uses.us_calls;
    Sx.iter   (fun x -> cb x.x_top) uses.us_reads;
    Sx.iter   (fun x -> cb x.x_top) uses.us_writes

  and on_mpath_fun_oi cb oi =
    List.iter (fun x -> cb x.x_top) oi.oi_calls

  exception UseLocal

  let check_use_local lc mp =
    if is_mp_local mp lc then
      raise UseLocal

  let check_use_local_or_abs lc mp =
    if is_mp_local mp lc || is_mp_abstract mp lc then
      raise UseLocal

  let form_use_local f lc =
    try  on_mpath_form (check_use_local lc) f; false
    with UseLocal -> true

  let module_use_local_or_abs m lc =
    try  on_mpath_module (check_use_local_or_abs lc) m; false
    with UseLocal -> true

  let abstracts lc = lc.lc_abstracts

  let generalize env lc (f : EcFol.form) =
    let axioms =
      List.pmap
        (fun (p, lvl) ->
           match lvl with `Global, `Axiom -> Some p | _ -> None)
        (fst lc.lc_lemmas)
    in

    match axioms with
    | [] ->
      let mods = Sid.of_list (List.map fst (fst lc.lc_abstracts)) in
        if   Mid.set_disjoint mods f.EcFol.f_fv
        then f
        else begin
          List.fold_right
            (fun (x, (mty, rt)) f ->
               match Mid.mem x f.EcFol.f_fv with
               | false -> f
               | true  -> EcFol.f_forall [(x, EcFol.GTmodty (mty, rt))] f)
            (fst lc.lc_abstracts) f
        end

    | _ ->
      let f =
        let do1 p f =
          let ax = EcEnv.Ax.by_path p env in
            EcFol.f_imp (oget ax.ax_spec) f
        in
            List.fold_right do1 axioms f in
      let f =
        let do1 (x, (mty, rt)) f =
          EcFol.f_forall [(x, EcFol.GTmodty (mty, rt))] f
        in
          List.fold_right do1 (fst lc.lc_abstracts) f
      in
        f

  let elocals (env : EcEnv.env) : locals =
    { lc_env       = env;
      lc_lemmas    = ([], Mp.empty);
      lc_modules   = Sp.empty;
      lc_abstracts = ([], Sid.empty);
      lc_items     = []; }

  type t = locals list

  let initial : t = []

  let in_section (cs : t) =
    match cs with [] -> false | _ -> true

  let enter (env : EcEnv.env) (cs : t) : t =
    match List.ohead cs with
    | None    -> [elocals env]
    | Some ec ->
      let ec =
        { ec with
            lc_items = [];
            lc_abstracts = ([], snd ec.lc_abstracts);
            lc_env = env; }
      in
        ec :: cs

  let exit (cs : t) =
    match cs with
    | [] -> raise NoSectionOpened
    | ec :: cs ->
        ({ ec with lc_items     = List.rev ec.lc_items;
                   lc_abstracts = fst_map List.rev ec.lc_abstracts;
                   lc_lemmas    = fst_map List.rev ec.lc_lemmas},
         cs)

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

  let add_local_mod (p : path) (cs : t) : t =
    onactive (fun ec -> { ec with lc_modules = Sp.add p ec.lc_modules }) cs

  let add_lemma (p : path) (lvl : lvl) (cs : t) : t =
    onactive (fun ec ->
      let (axs, map) = ec.lc_lemmas in
        { ec with lc_lemmas = ((p, lvl) :: axs, Mp.add p lvl map) })
      cs

  let add_item item (cs : t) : t =
    let doit ec = { ec with lc_items = item :: ec.lc_items } in
      onactive doit cs

  let add_abstract id mt (cs : t) : t =
    let doit ec =
      match Sid.mem id (snd ec.lc_abstracts) with
      | true  -> assert false
      | false ->
          let (ids, set) = ec.lc_abstracts in
          let (ids, set) = ((id, mt) :: ids, Sid.add id set) in
            { ec with lc_abstracts = (ids, set) }
    in
      onactive doit cs
end

(* -------------------------------------------------------------------- *)
type scope = {
  sc_name     : symbol;
  sc_env      : EcEnv.env;
  sc_top      : scope option;
  sc_loaded   : (EcEnv.ctheory_w3 * symbol list) Msym.t;
  sc_required : symbol list;
  sc_pr_uc    : proof_uc option;
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
  scope.sc_pr_uc |> obind (fun x -> x.puc_active)

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
        let ec = CoreSection.add_item item scope.sc_section in
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

  let check_prover_name { pl_desc = name; pl_loc = loc } =
    if not (EcProvers.is_prover_known name) then
      EcLocation.locate_error loc (Unknown_prover name);
    name

  let set_wrapper scope wrapper =
    let pi = Prover_info.get scope.sc_options in
    let pi = { pi with EcProvers.pr_wrapper = wrapper } in
      { scope with sc_options = Prover_info.set scope.sc_options pi; }

  let mk_prover_info scope maxprocs time ns =
    let dft      = Prover_info.get scope.sc_options in
    let time     = max 1 (odfl dft.EcProvers.pr_timelimit time) in
    let provers  = odfl dft.EcProvers.pr_provers ns in
    let maxprocs = odfl dft.EcProvers.pr_maxprocs maxprocs in
      { EcProvers.pr_maxprocs  = maxprocs;
        EcProvers.pr_provers   = provers;
        EcProvers.pr_timelimit = time;
        EcProvers.pr_wrapper   = dft.EcProvers.pr_wrapper; }

  let set_prover_info scope max time ns =
    let pi = mk_prover_info scope max time ns in
      { scope with sc_options = Prover_info.set scope.sc_options pi }

  let set_all scope =
    let provers = EcProvers.known_provers () in
      set_prover_info scope None None (Some provers)

  let set_default scope max provers =
    let provers =
      match provers with
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
      set_prover_info scope (Some max) (Some 3) (Some provers)

  let process scope pi =
    let max  = pi.pprov_max in
    let time = pi.pprov_time in
    let ns   = pi.pprov_names in
    let ns   = ns |> omap (List.map check_prover_name) in
      set_prover_info scope max time ns

  let mk_prover_info scope pi =
    let max  = pi.pprov_max in
    let time = pi.pprov_time in
    let ns   = pi.pprov_names in
    let ns   = ns |> omap (List.map check_prover_name) in
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
      match (oget scope.sc_pr_uc).puc_active with
      | None -> hierror "no active lemma"
      | Some pac -> 
          if   mark && pac.puc_mode = None
          then proof scope mode false
          else scope
    in

    let puc = oget (scope.sc_pr_uc) in
    let pac = oget (puc).puc_active in

    match pac.puc_jdg with
    | PSNoCheck -> scope
    | PSCheck juc ->
        let loc = (oget (List.ohead tac)).pt_core.pl_loc in

        let htmode =
          match pac.puc_mode, mode with
          | Some true , `WeakCheck -> `Admit
          | _         , `WeakCheck ->  hierror "cannot weak-check a non-strict proof script"
          | Some true , `Check     -> `Strict
          | Some false, `Check     -> `Standard
          | _         , `Check     -> `Strict
        in

        let hitenv = { hte_provers = pi scope; hte_smtmode = htmode; } in

        let juc = process_tactic_on_goal hitenv juc loc tac in
        let pac = { pac with puc_jdg = PSCheck juc; } in
          { scope with sc_pr_uc = Some { puc with puc_active = Some pac; } }

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
    let ue = TT.transtyvars scope.sc_env (loc, op.po_tyvars) in
    let tp = TT.tp_relax in

    let (ty, body) =
      match op.po_def with
      | PO_abstr pty ->
          (TT.transty tp scope.sc_env ue pty, `Abstract)

      | PO_concr (bd, pty, pe) ->
          let env     = scope.sc_env in
          let codom   = TT.transty tp env ue pty in 
          let env, xs = TT.transbinding env ue bd in
          let body    = TT.transexpcast env ue codom pe in
          let lam     = EcTypes.e_lam xs body in
            (lam.EcTypes.e_ty, `Plain lam)

      | PO_case (bd, pty, pbs) ->
          (* FIXME: move this to a dedicated module *)

          let env       = scope.sc_env in
          let codom     = TT.transty tp env ue pty in
          let env, args = TT.transbinding env ue bd in
          let ty        = EcTypes.toarrow (List.map snd args) codom in
          let opname    = EcIdent.create (unloc op.po_name) in
          let env       = EcEnv.Var.bind_local opname ty env in
          let mpname, mpty =
              let names = Ssym.of_list (List.map (fun pop -> unloc pop.pop_name) pbs) in
              let name1 =
                try  Ssym.choose names
                with Not_found ->
                  hierror ~loc "this pattern matching has no branches"
              in
                if not (Ssym.is_empty (Ssym.remove name1 names)) then
                  hierror ~loc "this pattern matching matches on different parameters";
                match List.findopt (fun (x, _) -> EcIdent.name x = name1) (List.rev args) with
                | None   -> hierror ~loc "this pattern matching matches an unbound parameter";
                | Some x -> x
          in

          let branches =
            let pbs =
              let trans1 pb =
                let filter = fun op -> EcDecl.is_ctor op in
                let cname  = fst pb.pop_pattern in
                let tvi    = pb.pop_tvi |> omap (TT.transtvi env ue) in
                let cts    = EcUnify.select_op ~filter tvi env (unloc cname) ue [] in
  
                match cts with
                | [] -> hierror ~loc:cname.pl_loc "unknown constructor name"
                | _ :: _ :: _ -> hierror ~loc:cname.pl_loc "ambiguous constructor name"
  
                | [(cp, tvi), opty, subue] ->
                    let ctor = oget (EcEnv.Op.by_path_opt cp env) in
                    let (indp, ctoridx) = EcDecl.operator_as_ctor ctor in
                    let indty = oget (EcEnv.Ty.by_path_opt indp env) in
                    let ind = snd (EcDecl.tydecl_as_datatype indty) in
                    let ctorsym, ctorty = List.nth ind ctoridx in

                    let args_exp = List.length ctorty in
                    let args_got = List.length (snd pb.pop_pattern) in

                    if args_exp <> args_got then
                      hierror ~loc:cname.pl_loc
                        "this constructor takes %d argument(s), got %d" args_exp args_got;

                    if not (List.uniq (List.map unloc (snd pb.pop_pattern))) then
                      hierror ~loc:cname.pl_loc "this pattern is non-linear";

                    EcUnify.UniEnv.restore ~src:subue ~dst:ue;

                    let ctorty =
                      let tvi = Some (EcUnify.TVIunamed tvi) in
                        fst (EcUnify.UniEnv.opentys ue indty.tyd_params tvi ctorty) in
                    let pty = EcUnify.UniEnv.fresh ue in

                    (try  EcUnify.unify env ue (toarrow ctorty pty) opty
                     with EcUnify.UnificationFailure _ -> assert false);
                    TT.unify_or_fail env ue pb.pop_name.pl_loc pty mpty;

                    let pvars = List.map (EcIdent.create |- unloc) (snd pb.pop_pattern) in
                    let pvars = List.combine pvars ctorty in

                    let be =
                      let env = EcEnv.Var.bind_locals pvars env in
                        TT.transexpcast env ue codom pb.pop_body
                    in
                      (pb, (indp, ind, (ctorsym, ctoridx)), (pvars, be))

              in
                List.map trans1 pbs
            in

            let (_, (_, ind, _), _) = oget (List.ohead pbs) in
            let bmap = Array.create (List.length ind) None in

            List.iter
              (fun ((_, (_, _, (cname, ctor)), _) as ct) ->
                if bmap.(ctor) <> None then
                  hierror ~loc "duplicated branch for constructor `%s'" cname;
                bmap.(ctor) <- Some ct)
              pbs;

            Parray.of_array (Array.mapi
              (fun i v ->
                let cname = fst (List.nth ind i) in
                  match v with
                  | None -> hierror ~loc "missing branch for constructor `%s'" cname
                  | Some (_, _, branch) -> ((cname, i), branch))
              bmap)
          in

            (ty, (`Fix ((opname, codom), (args, mpname), branches)))
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
      | `Fix ((opname, codom), (args, mpname), bs) ->
          let codom   = uni codom in
          let opexpr  = EcPath.pqname (path scope) (unloc op.po_name) in
          let opexpr  = e_op opexpr (List.map (tvar |- fst) tparams) codom in
          let ebsubst = { e_subst_id with es_freshen = false; es_ty = uni; } in
          let ebsubst = { ebsubst with es_loc = Mid.add opname opexpr ebsubst.es_loc; } in
          let args    = List.map (fun (x, xty) -> (x, uni xty)) args in
          let structi =
            oget (List.findex (fun (x, _) -> EcIdent.id_equal x mpname) args) in
          let bs =
            Parray.map
              (fun ((cname, i), (pvars, be)) ->
                { opf1_ctor   = (EcPath.pqname (path scope) cname, i);
                  opf1_locals = List.map (fun (x, xty) -> (x, uni xty)) pvars;
                  opf1_body   = e_subst ebsubst be; })
              bs
          in
            Some (OP_Fix { opf_args     = args;
                           opf_resty    = codom;
                           opf_struct   = (structi, List.length args);
                           opf_branches = bs; })
    in

    let tyop = EcDecl.mk_op tparams ty body in

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

    bind scope (unloc op.po_name, tyop)
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
              Mx.fold add use.EcEnv.NormMp.us_pv EcPath.Sx.empty in
            EcEnv.Mod.add_restr_to_locals (rx,EcPath.Sm.empty) env in
        let ec = CoreSection.add_local_mod mpath scope.sc_section in
        { scope with sc_section = ec; sc_env = env }
    in
      scope

  let add (scope : scope) (ptm : ptopmodule) =
    assert (scope.sc_pr_uc = None);

    if ptm.ptm_local && not (CoreSection.in_section scope.sc_section) then
      hierror "cannot declare a local module outside of a section";

    let (name, m) = ptm.ptm_def in
    let m = TT.transmod scope.sc_env ~internal:false (unloc name) m in

    if not ptm.ptm_local then begin
      match CoreSection.olocals scope.sc_section with
      | None -> ()
      | Some locals ->
          if CoreSection.module_use_local_or_abs m locals then
            hierror "this module use local/abstracts modules and must be declared as local";
          
    end;

      bind scope ptm.ptm_local m

  let declare (scope : scope) m =
    if not (CoreSection.in_section scope.sc_section) then
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
          sc_section = CoreSection.add_abstract
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
      match CoreSection.opath scope.sc_section with
      | None -> scope
      | Some _ ->
          let lvl1 = if local then `Local else `Global in
          let lvl2 = if ax.ax_kind = `Axiom then `Axiom else `Lemma in

          if lvl2 = `Axiom && ax.ax_tparams <> [] then
            hierror "axiom must be monomorphic in sections";

          let axpath = EcPath.pqname (path scope) x in
          let ec = CoreSection.add_lemma axpath (lvl1, lvl2) scope.sc_section in
            { scope with sc_section = ec }
    in
      scope

  (* ------------------------------------------------------------------ *)
  let start_lemma scope (cont, axflags) check name axd =
    let puc =
      match check with
      | false -> PSNoCheck
      | true  ->
          (* FIXME: TC HOOK *)
          let hyps = EcEnv.LDecl.init scope.sc_env (List.map fst axd.ax_tparams) in
            PSCheck (EcLogic.open_juc (hyps, oget axd.ax_spec), [0])
    in 
    let puc = { puc_active = Some {
                  puc_name  = name;
                  puc_mode  = None;
                  puc_jdg   = puc;
                  puc_flags = axflags;
                  puc_crt   = axd;
                };
                puc_cont = cont; }
    in
      { scope with sc_pr_uc = Some puc }

  (* ------------------------------------------------------------------ *)
  let rec add_r (scope : scope) mode (ax : paxiom located) =
    assert (scope.sc_pr_uc = None);

    let loc = ax.pl_loc and ax = ax.pl_desc in
    let ue  = TT.transtyvars scope.sc_env (loc, ax.pa_tyvars) in

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
        (fun x -> IPCore (mk_loc x.pl_loc (`NoRename x.pl_desc)))
        tintro in
    let tintro = mk_loc loc (Plogic (Pintro tintro)) in

    let concl = TT.trans_prop scope.sc_env ue pconcl in

    if not (EcUnify.UniEnv.closed ue) then
      hierror "the formula contains free type variables";

    let concl   = EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) concl in
    let tparams = EcUnify.UniEnv.tparams ue in

    let axd  =
      let kind = match ax.pa_kind with PAxiom -> `Axiom | _ -> `Lemma in
        { ax_tparams = tparams;
          ax_spec    = Some concl;
          ax_kind    = kind;
          ax_nosmt   = ax.pa_nosmt; }
    in

    let check    = Check_mode.check scope.sc_options in
    let pucflags = { puc_nosmt = ax.pa_nosmt; puc_local = ax.pa_local; } in
    let pucflags = (([], None), pucflags) in

    if not ax.pa_local then begin
      match CoreSection.olocals scope.sc_section with
      | None -> ()
      | Some locals ->
          if CoreSection.form_use_local concl locals then
            hierror "this lemma uses local modules and must be declared as local"
    end;

    if ax.pa_local && ax.pa_kind = PAxiom then
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

        let tc = { pl_loc = loc; pl_desc = Pby [tc] } in
        let tc = { pt_core = tc; pt_intros = []; } in

        let scope = Tactics.process_r false mode scope [tc] in
          save scope loc

    | PAxiom ->
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
          | PSCheck gs ->
              try  ignore (EcLogic.close_juc (fst gs))
              with EcBaseLogic.StillOpenGoal _ ->
                hierror "cannot save an incomplete proof"
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
module Ty = struct
  open EcDecl
  open EcTyping
  open EcAlgebra

  module TT = EcTyping

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
  let add (scope : scope) info =
    assert (scope.sc_pr_uc = None);
    let (args, name) = info.pl_desc and loc = info.pl_loc in
    let ue = TT.transtyvars scope.sc_env (loc, Some args) in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = `Abstract Sp.empty;
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
  let bindclass (scope : scope) (x, (tc : unit)) =
    assert (scope.sc_pr_uc = None);
    let scope = { scope with sc_env = EcEnv.TypeClass.bind x tc scope.sc_env; } in
    let scope = maybe_add_to_section scope (EcTheory.CTh_typeclass x) in
      scope

  (* ------------------------------------------------------------------ *)
  let add_class (scope : scope) { pl_desc = tcd } =
    assert (scope.sc_pr_uc = None);

    let name  = unloc tcd.ptc_name in
    let scenv = (env scope) in

    check_name_available scope tcd.ptc_name;

    let _tclass =

      let uptc =
        tcd.ptc_inth |> omap
          (fun { pl_loc = uploc; pl_desc = uptc } ->
            match EcEnv.TypeClass.lookup_opt uptc scenv with
            | None -> hierror ~loc:uploc "unknown type-class: `%s'"
                        (string_of_qsymbol uptc)
            | Some (p, _) -> p)
      in

      let asty  =
        let body = ofold (fun p tc -> Sp.add p tc) Sp.empty uptc in
          { tyd_params = []; tyd_type = `Abstract body; } in
      let scenv = EcEnv.Ty.bind name asty scenv in

      (* Check for duplicated field names *)
      Msym.odup unloc (List.map fst tcd.ptc_ops)
        |> oiter (fun (x, y) -> hierror ~loc:y.pl_loc
                    "duplicated field name: `%s'" x.pl_desc);
    
      (* Check operators types *)
      let operators =
        let check1 (x, ty) =
          let ue = EcUnify.UniEnv.create (Some []) in
            (EcIdent.create (unloc x), transty tp_tydecl scenv ue ty)
        in
          tcd.ptc_ops |> List.map check1 in
    
      (* Check axioms *)
      let axioms =
        let scenv = EcEnv.Var.bind_locals operators scenv in
        let check1 ax =
          let ue = EcUnify.UniEnv.create (Some []) in
            trans_prop scenv ue ax
        in
          tcd.ptc_axs |> List.map check1 in
    
      (* Construct actual type-class *)
      { tc_ops = operators; tc_axs = axioms; }
    in
      bindclass scope (name, ())

  (* ------------------------------------------------------------------ *)
  let check_tci_operators env ops reqs =
    let rmap = Mstr.of_list reqs in
    let ops =
      List.fold_left
        (fun m (x, op) ->
          if not (Mstr.mem (unloc x) rmap) then
            hierror ~loc:x.pl_loc "invalid operator name: `%s'" (unloc x);
          let op =
            let filter op = match op.op_kind with OB_oper _ -> true | _ -> false in
            match EcEnv.Op.all filter (unloc op) env with
            | []      -> hierror ~loc:op.pl_loc "unknown operator"
            | _::_::_ -> hierror ~loc:op.pl_loc "ambiguous operator"
            | [op]    -> op
          in
            Mstr.change
              (function
               | None   -> Some (x.pl_loc, op)
               | Some _ -> hierror ~loc:(x.pl_loc)
                             "duplicated operator name: `%s'" (unloc x))
              (unloc x) m)
        Mstr.empty ops
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
           | Some (loc, (p, op)) ->
               if not (EcReduction.equal_type env ty (op_ty op)) then
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
          let t  = { pt_core = pt; pt_intros = []; } in
          let t  = { pl_loc = pt.pl_loc; pl_desc = Pby [t] } in
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
  let ring_of_symmap ty symbols =
    { r_type  = ty;
      r_zero  = oget (Mstr.find_opt "rzero" symbols);
      r_one   = oget (Mstr.find_opt "rone"  symbols);
      r_add   = oget (Mstr.find_opt "add"   symbols);
      r_opp   = oget (Mstr.find_opt "opp"   symbols);
      r_mul   = oget (Mstr.find_opt "mul"   symbols);
      r_exp   = oget (Mstr.find_opt "expr"  symbols);
      r_sub   = Mstr.find_opt "sub" symbols;
      r_embed =
        match Mstr.find_opt "ofint" symbols with
        | None   -> `Direct
        | Some p -> `Embed p }

  let addring (scope : scope) mode { pl_desc = tci; pl_loc = loc } =
    if not (EcAlgTactic.is_module_loaded scope.sc_env) then
      hierror "load AlgTactic first";

    let (ty, p) =
      let ue = TT.transtyvars scope.sc_env (loc, Some []) in
      let ty = mk_loc tci.pti_type.pl_loc (PTnamed tci.pti_type) in
      let ty = transty tp_tydecl scope.sc_env ue ty in
        match (EcEnv.Ty.hnorm ty scope.sc_env).ty_node with
        | Tconstr (p, []) -> (ty,  p)
        | _ -> assert false
    in
    let symbols = EcAlgTactic.ring_symbols scope.sc_env ty in
    let symbols = check_tci_operators scope.sc_env tci.pti_ops symbols in
    let cr      = ring_of_symmap ty symbols in
    let axioms  = EcAlgTactic.ring_axioms scope.sc_env cr in
      check_tci_axioms scope mode tci.pti_axs axioms;
      { scope with sc_env = EcEnv.Algebra.add_ring p cr scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let field_of_symmap ty symbols =
    { f_ring = ring_of_symmap ty symbols;
      f_inv  = oget (Mstr.find_opt "inv" symbols);
      f_div  = Mstr.find_opt "div" symbols; }

  let addfield (scope : scope) mode { pl_desc = tci; pl_loc = loc } =
    if not (EcAlgTactic.is_module_loaded scope.sc_env) then
      hierror "load AlgTactic first";

    let (ty, p) =
      let ue = TT.transtyvars scope.sc_env (loc, Some []) in
      let ty = mk_loc tci.pti_type.pl_loc (PTnamed tci.pti_type) in
      let ty = transty tp_tydecl scope.sc_env ue ty in
        match (EcEnv.Ty.hnorm ty scope.sc_env).ty_node with
        | Tconstr (p, []) -> (ty, p)
        | _ -> assert false
    in
    let symbols = EcAlgTactic.field_symbols scope.sc_env ty in
    let symbols = check_tci_operators scope.sc_env tci.pti_ops symbols in
    let cr      = field_of_symmap ty symbols in
    let axioms  = EcAlgTactic.field_axioms scope.sc_env cr in
      check_tci_axioms scope mode tci.pti_axs axioms;
      { scope with sc_env = EcEnv.Algebra.add_field p cr scope.sc_env }

  (* ------------------------------------------------------------------ *)
  (* We currently only deal with [ring] and [field] *)
  let add_instance (scope : scope) mode ({ pl_desc = tci } as toptci) =
    match unloc tci.pti_name with
    | ([], "ring" ) -> addring  scope  mode toptci
    | ([], "field") -> addfield scope  mode toptci
    | _ -> hierror "unknown type class"

  (* ------------------------------------------------------------------ *)
  (* FIXME: Check for positivity *)
  let add_datatype (scope : scope) { pl_loc = loc; pl_desc = dt; } =
    check_name_available scope dt.ptd_name;

    (* Check type-parameters / env0 is the env. augmented with an
     * abstract type representing the currently processed datatype. *)
    let ue    = TT.transtyvars scope.sc_env (loc, Some dt.ptd_tyvars) in
    let tpath = EcPath.pqname (path scope) (unloc dt.ptd_name) in
    let env0  =
      let myself = {
        tyd_params = EcUnify.UniEnv.tparams ue;
        tyd_type   = `Abstract Sp.empty;
      } in
        EcEnv.Ty.bind (unloc dt.ptd_name) myself scope.sc_env
    in

    (* Check for duplicated constructor names *)
    Msym.odup unloc (List.map fst dt.ptd_ctors)
      |> oiter (fun (x, y) -> hierror ~loc:y.pl_loc
                  "duplicated constructor name: `%s'" x.pl_desc);

    (* Type-check constructor types *)
    let ctors =
      let for1 (cname, cty) =
        let ue  = EcUnify.UniEnv.copy ue in
        let cty = cty |> List.map (TT.transty TT.tp_tydecl env0 ue) in
          (unloc cname, cty)
      in
        dt.ptd_ctors |> List.map for1
    in

    let tparams = EcUnify.UniEnv.tparams ue in

    (* Check for the positivity condition / emptyness *)
    let scheme =
      let module E = struct exception Fail end in

      let rec scheme1 p (pred, fac) ty =
        let ty = EcEnv.Ty.hnorm ty env0 in
          match ty.ty_node with
          | Tglob   _ -> assert false
          | Tunivar _ -> assert false
          | Tvar    _ -> None

          | Ttuple tys -> begin
              let xs  = List.map (fun xty -> (fresh_id_of_ty xty, xty)) tys in
              let sc1 = fun (x, xty) -> scheme1 p (pred, EcFol.f_local x xty) xty in
                match List.pmap sc1 xs with
                | []  -> None
                | scs -> Some (EcFol.f_let (LTuple xs) fac (EcFol.f_ands scs))
          end

          | Tconstr (p', ts)  ->
              if List.exists (occurs p) ts then raise E.Fail;
              if not (EcPath.p_equal p p') then None else
                Some (EcFol.f_app pred [fac] tbool)

          | Tfun (ty1, ty2) ->
              if occurs p ty1 then raise E.Fail;
              let x = fresh_id_of_ty ty1 in
                scheme1 p (pred, EcFol.f_app fac [EcFol.f_local x ty1] ty2) ty2
                  |> omap (EcFol.f_forall [x, EcFol.GTty ty1])

      and schemec (targs, p) pred (ctor, tys) =
        let indty = tconstr p (List.map tvar targs) in
        let ctor  = EcPath.pqname (path scope) ctor in
        let ctor  = EcFol.f_op ctor (List.map tvar targs) indty in
        let xs    = List.map (fun xty -> (fresh_id_of_ty xty, xty)) tys in
        let cargs = List.map (fun (x, xty) -> EcFol.f_local x xty) xs in
        let sc1   = fun (x, xty) -> scheme1 p (pred, EcFol.f_local x xty) xty in
        let scs   = List.pmap sc1 xs in
        let form  = EcFol.f_app pred [EcFol.f_app ctor cargs indty] tbool in
        let form  = EcFol.f_imps scs form in
        let form  =
          let bds = List.map (fun (x, xty) -> (x, EcFol.GTty xty)) xs in
            EcFol.f_forall bds form
        in
          form

      and scheme (targs, p) ctors =
        let indty  = tconstr p (List.map tvar targs) in
        let indx   = fresh_id_of_ty indty in
        let indfm  = EcFol.f_local indx indty in
        let predty = tfun indty tbool in
        let predx  = EcIdent.create "P" in
        let pred   = EcFol.f_local predx predty in
        let scs    = List.map (schemec (targs, p) pred) ctors in
        let form   = EcFol.f_app pred [indfm] tbool in
        let form   = EcFol.f_forall [indx, EcFol.GTty indty] form in
        let form   = EcFol.f_imps scs form in
        let form   = EcFol.f_forall [predx, EcFol.GTty predty] form in
          form

      and occurs p t =
        let t = EcEnv.Ty.hnorm t env0 in
          match t.ty_node with
          | Tconstr (p', _) when EcPath.p_equal p p' -> true
          | _ -> EcTypes.ty_sub_exists (occurs p) t

      in
        let scheme =
          try  scheme (List.map fst tparams, tpath) ctors
          with E.Fail ->
            hierror ~loc "the datatype does not respect the positivity condition"
        in
          if List.for_all (fun (_, cty) -> List.exists (occurs tpath) cty) ctors then
            hierror ~loc "this datatype is empty";
          scheme
    in

    (* Add final datatype to environment *)
    let tydecl = {
      tyd_params = tparams;
      tyd_type   = `Datatype (scheme, ctors);
    } in
      bind scope (unloc dt.ptd_name, tydecl)
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

    if CoreSection.in_section scope.sc_section then
      hierror "cannot clone a theory while a section is active";

    let (name, proofs, nth) = C.clone scope.sc_env thcl in

    let proofs = List.pmap (fun axc ->
      match axc.C.axc_tac with
      | None -> Some (axc.C.axc_axiom, axc.C.axc_path, axc.C.axc_env)
      | Some pt ->
          let t = { pt_core = pt; pt_intros = []; } in
          let t = { pl_loc = pt.pl_loc; pl_desc = Pby [t]; } in
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
        let scenv  = scope.sc_env in
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

          | T.CTh_axiom (x, ax) -> begin
            match ax.ax_kind with
            | `Axiom -> scope
            | `Lemma ->
                let axp = EcPath.pqname (path scope) x in
                  if not (CoreSection.is_local `Lemma axp locals) then
                    Ax.bind scope false
                      (x, { ax with ax_spec =
                              ax.ax_spec |> omap (CoreSection.generalize scenv locals) })
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

          | T.CTh_typeclass x -> Ty.bindclass scope (x, ())

          | T.CTh_instance (p, cr) -> begin
              match cr with
              | `Ring    cr -> { scope with sc_env = EcEnv.Algebra.add_ring  p cr scope.sc_env }
              | `Field   cr -> { scope with sc_env = EcEnv.Algebra.add_field p cr scope.sc_env }
              | `General _  -> scope    (* FIXME: TC HOOK *)
          end
        in

        List.fold_left bind1 scope oitems
end

module Extraction = struct
    
  let check_top scope = 
    if not (scope.sc_top = None) then 
      hierror "Extraction can not be done inside a theory";
    if CoreSection.in_section scope.sc_section then
      hierror "Extraction can not be done inside a section"
    
  let process scope todo =
    check_top scope;
    EcExtraction.process_extraction (env scope) scope.sc_required todo;
    scope 
    
end
