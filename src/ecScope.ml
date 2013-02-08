(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcPath
open EcParsetree
open EcTypes
open EcTypesmod

module IM = EcIdent.Map

(* -------------------------------------------------------------------- *)
module Context = struct
  module SM = EcMaps.Mstr

  module V : sig
    type 'a t

    val empty  : unit -> 'a t
    val push   : 'a -> 'a t -> 'a t
    val iter   : ('a -> unit) -> 'a t -> unit
    val fold   : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
    val tolist : 'a t -> 'a list
  end = struct
    type 'a data = {
      v_front : 'a list;
      v_back  : 'a list;
    }

    type 'a t = ('a data) ref

    let normalize =
      let normalize (v : 'a data) = {
        v_front = List.rev_append (List.rev v.v_front) v.v_back;
        v_back  = [];
      } in
        fun v ->
          if !v.v_back <> [] then v := normalize !v; !v

    let empty () =
      ref { v_front = []; v_back = []; }

    let push (x : 'a) (v : 'a t) =
      ref { v_front = !v.v_front; v_back = x :: !v.v_back }

    let iter (f : 'a -> unit) (v : 'a t) =
      List.iter f (normalize v).v_front

    let fold (f : 'b -> 'a -> 'b) (state : 'b) (v : 'a t) =
      List.fold_left f state (normalize v).v_front

    let tolist (v : 'a t) = (normalize v).v_front
  end

  type symbol = string

  type 'a context = {
    ct_map   : 'a SM.t;
    ct_order : (string * 'a) V.t;
  }

  exception DuplicatedNameInContext of string
  exception UnboundName of string

  let empty () = { ct_map = SM.empty; ct_order = V.empty (); }

  let bind (x : symbol) (v : 'a) (m : 'a context) =
    if SM.mem x m.ct_map then
      raise (DuplicatedNameInContext x);
    { ct_map   = SM.add x v m.ct_map;
      ct_order = V.push (x, v) m.ct_order; }

  let rebind (x : symbol) (v : 'a) (m : 'a context) =
    if not (SM.mem x m.ct_map) then
      raise (UnboundName x);
    { ct_map   = SM.add x v m.ct_map;
      ct_order = m.ct_order; }

  let exists (x : symbol) (m : 'a context) =
    SM.mem x m.ct_map

  let lookup (x : symbol) (m : 'a context) =
    try  Some (SM.find x m.ct_map)
    with Not_found -> None

  let iter (f : symbol -> 'a -> unit) (m : 'a context) =
    V.iter (fun (x, v) -> f x v) m.ct_order

  let fold (f : 'b -> symbol -> 'a -> 'b) (state : 'b) (m : 'a context) =
    V.fold (fun st (x, v) -> f st x v) state m.ct_order

  let tolist (m : 'a context) =
    V.tolist m.ct_order
end

type action = { 
    for_loading  : exn -> exn;
(*    for_subscope : exn -> exn; *)
  } 

module type IOptions = sig
  type option 

  val register          : action -> exn -> option
  val register_identity : exn -> option

  type options 

  val init  : unit -> options
  val get   : options -> option -> exn
  val set   : options -> option -> exn -> options
  val for_loading  : options -> options
  val for_subscope : options -> options

end

module Options : IOptions = struct
  type option = int
       
  type options = (action * exn) Mint.t

  let known_options : options ref = ref Mint.empty

  let identity = {
    for_loading  = (fun x -> x);
  (*  for_subscope = fun x -> x; *)
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
    Mint.change (function None -> assert false | Some(act,_) -> Some (act, exn))
      opt options

  let for_loading options = 
    Mint.map (fun (act, exn) -> act, act.for_loading exn) options

  let for_subscope options = options

end 

module Check_mode = struct 
  
  exception Full_check (* Disable : checkproof off, i.e. check every think *)
  exception Check of bool  (* true check proofs,  false do not check *)
      
  let for_loading = function 
    | Check _ -> Check false
    | exn     -> exn 

  let default = Check true

  let mode = Options.register { for_loading = for_loading } default  

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

module Prover_info = struct

  exception PI of EcWhy3.prover_infos

  let npi = Options.register_identity (PI EcWhy3.dft_prover_infos)

  let set options pi = 
    Options.set options npi (PI pi)

  let get options = 
    match Options.get options npi with
    | PI pi -> pi
    | _     -> assert false

end
      
(* -------------------------------------------------------------------- *)

type proof_uc_kind = 
  | PUCK_logic of EcLogic.judgment_uc 

type proof_uc = {
    puc_name : string;
    puc_kind : proof_uc_kind;
  }

  
type scope = {
  sc_name       : EcIdent.t;
  sc_types      : EcDecl.tydecl          Context.context;
  sc_operators  : EcDecl.operator        Context.context;
  sc_axioms     : EcDecl.axiom           Context.context;
  sc_modules    : EcTypesmod.module_expr Context.context;
  sc_modtypes   : EcTypesmod.module_sig  Context.context;
  sc_theories   : EcTypesmod.ctheory     Context.context;
  sc_env        : EcEnv.env;
  sc_top        : scope option;
  sc_loaded     : (EcEnv.ctheory_w3 * EcIdent.t list) IM.t;
  sc_required   : EcIdent.t list;
  sc_pr_uc      : proof_uc list; 
  sc_options    : Options.options;
}

(* -------------------------------------------------------------------- *)
let empty =
  let env    = EcEnv.initial in

    { sc_name       = EcPath.basename env.EcEnv.env_scope;
      sc_types      = Context.empty ();
      sc_operators  = Context.empty ();
      sc_axioms     = Context.empty ();
      sc_modtypes   = Context.empty ();
      sc_modules    = Context.empty ();
      sc_theories   = Context.empty ();
      sc_env        = EcEnv.initial;
      sc_top        = None;
      sc_loaded     = IM.empty;
      sc_required   = [];
      sc_pr_uc      = [];
      sc_options    = Options.init ();
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
let for_loading (scope : scope) =
  { empty with sc_loaded = scope.sc_loaded;
    sc_options = Options.for_loading scope.sc_options;
  }

(* -------------------------------------------------------------------- *)
let subscope (scope : scope) (name : symbol) =
  let (name, env) = EcEnv.Theory.enter name scope.sc_env in

  { sc_name       = name;
    sc_types      = Context.empty ();
    sc_operators  = Context.empty ();
    sc_axioms     = Context.empty ();
    sc_modtypes   = Context.empty ();
    sc_modules    = Context.empty ();
    sc_theories   = Context.empty ();
    sc_env        = env;
    sc_top        = Some scope;
    sc_loaded     = scope.sc_loaded;
    sc_required   = [];
    sc_pr_uc      = [];
    sc_options    = Options.for_subscope scope.sc_options;
  }

(* -------------------------------------------------------------------- *)

let init_unienv tparams = 
  let build tparams = 
    let l = ref [] in
    let check ps = 
      let s = unloc ps in
      if List.mem s !l then 
        EcTypedtree.tyerror ps.pl_loc (EcTypedtree.DuplicatedLocals (Some ps)) 
      else (l:= s::!l;EcIdent.create s) in
    List.map check tparams in
  let tparams = omap tparams build in 
  EcUnify.UniEnv.create tparams

module Op = struct
  open EcTypes
  open EcDecl
  open EcEnv

  module TT = EcTypedtree

  let bind (scope : scope) ((x, op) : _ * operator) =
    { scope with
        sc_operators = Context.bind (EcIdent.name x) op scope.sc_operators;
        sc_env       = EcEnv.Op.bind x op scope.sc_env; }

  let add (scope : scope) (op : poperator) =
    let ue = init_unienv op.po_tyvars in
    let tp =  TT.tp_relax in
    let dom  = TT.transtys tp scope.sc_env ue (odfl [] op.po_dom) in
    let codom  = TT.transty tp scope.sc_env ue op.po_codom in
    let body =
      match op.po_body with
      | None -> None
      | Some(xs, body) ->
          let xs = List.map EcIdent.create (unlocs xs) in
          let env =
            EcEnv.Var.bindall (List.combine xs dom) None scope.sc_env
          in
          let body = TT.transexpcast env ue codom body in
          Some (xs, body) in
    let uni = Tuni.subst (EcUnify.UniEnv.close ue) in
    let body = omap body (fun (ids,body) -> ids, Esubst.mapty uni body) in
    let (dom,codom) = List.map uni dom, uni codom in
    let tparams = EcUnify.UniEnv.tparams ue in 
    let tyop = EcDecl.mk_op tparams dom codom body in
    bind scope (EcIdent.create (unloc op.po_name), tyop)
end

(* -------------------------------------------------------------------- *)
module Pred = struct
  module TT = EcTypedtree

  let add (scope : scope) (op : ppredicate) =
    let ue = init_unienv op.pp_tyvars in
    let tp =  TT.tp_relax in 
    let dom  = TT.transtys tp scope.sc_env ue (odfl [] op.pp_dom) in
    let body =
      match op.pp_body with
      | None -> None
      | Some(xs, body) ->
          let xs = List.map EcIdent.create (unlocs xs) in
          let env = TT.Fenv.mono_fenv scope.sc_env in
          let env = TT.Fenv.bind_locals env xs dom in 
          let body = TT.transformula env ue body in
          Some(xs, body) in
    let uni = Tuni.subst (EcUnify.UniEnv.close ue) in
    let body = omap body (fun (ids,body) -> ids, EcFol.Fsubst.mapty uni body) in
    let dom = List.map uni dom in
    let tparams = EcUnify.UniEnv.tparams ue in
    let tyop = EcDecl.mk_pred tparams dom body in
    Op.bind scope (EcIdent.create (unloc op.pp_name), tyop)

end

(* -------------------------------------------------------------------- *)
module Ty = struct
  open EcDecl
  open EcTypedtree

  let bind (scope : scope) ((x, tydecl) : _ * tydecl) =
    { scope with
        sc_types = Context.bind (EcIdent.name x) tydecl scope.sc_types;
        sc_env   = EcEnv.Ty.bind x tydecl scope.sc_env; }

  let alias (scope : scope) name ty =
    (* FIXME : check that ty is closed, or close it *)
    let tydecl = {tyd_params = []; tyd_type = Some ty } in
      bind scope (EcIdent.create name, tydecl)

  let add (scope : scope) (args, name) = 
    let ue = init_unienv (Some args) in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = None;
    } in
    bind scope (EcIdent.create (unloc name), tydecl)

  let define (scope : scope) (args, name) body = 
    let ue = init_unienv (Some args) in
    let body = transty tp_tydecl scope.sc_env ue body in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = Some body;
    } in
    bind scope (EcIdent.create (unloc name), tydecl)
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  let bind (scope : scope) (m : module_expr) =
    { scope with
        sc_modules = Context.bind (EcIdent.name m.me_name) m scope.sc_modules;
        sc_env     = EcEnv.Mod.bind m.me_name m scope.sc_env; }

  let add (scope : scope) (name : symbol) m =
    let name = EcIdent.create name in
    let m = EcTypedtree.transmod scope.sc_env name m in
      bind scope m
end

(* -------------------------------------------------------------------- *)
module ModType = struct
  let bind (scope : scope) ((x, tysig) : _ * module_sig) =
    { scope with
        sc_modtypes = Context.bind (EcIdent.name x) tysig scope.sc_modtypes;
        sc_env = EcEnv.ModTy.bind x tysig scope.sc_env; }

  let add (scope : scope) (name : symbol) (i : pmodule_sig) =
    let tysig = EcTypedtree.transmodsig scope.sc_env i in
      bind scope (EcIdent.create name, tysig)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  exception TopScope

  (* ------------------------------------------------------------------ *)
  let bind (scope : scope) ((x, cth) : _ * EcEnv.ctheory_w3) =
    let theory = EcEnv.ctheory_of_ctheory_w3 cth in
      { scope with
          sc_theories = Context.bind (EcIdent.name x) theory scope.sc_theories;
          sc_env      = EcEnv.Theory.bind x cth scope.sc_env; }

  (* ------------------------------------------------------------------ *)
  
  let required (scope : scope) (name : symbol) =
    List.exists (fun x -> EcIdent.name x = name) scope.sc_required

  (* ------------------------------------------------------------------ *)
  let enter (scope : scope) (name : symbol) =
    subscope scope name

  (* ------------------------------------------------------------------ *)

   let rec require_loaded id scope = 
     if required scope (EcIdent.name id) then scope
     else 
       match IM.byident id scope.sc_loaded with
       | Some (rth,ids) -> 
           let scope = List.fold_right require_loaded ids scope in
           let env  = EcEnv.Theory.require id rth scope.sc_env in
           { scope with 
             sc_env = env;
             sc_required = id :: scope.sc_required } 
       | None -> assert false 
             
  let exit_r (scope : scope) =
    match scope.sc_top with
    | None     -> raise TopScope
    | Some sup ->
        let cth    = EcEnv.Theory.close scope.sc_env in
        let loaded = scope.sc_loaded in
        let required = scope.sc_required in 
        let sup = { sup with
                    sc_loaded = loaded } in
        ((cth,required), scope.sc_name, sup) 

  (* ------------------------------------------------------------------ *)
  let exit (scope : scope) =
    let ((cth,required), name, scope) = exit_r scope in
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
            (EcIdent.name scope.sc_name) (EcIdent.name thname) in
        failwith msg
      end;
    if scope.sc_pr_uc <> [] then
      let msg = 
        Printf.sprintf 
          "end-of-file while processing proof %s" (EcIdent.name scope.sc_name) in
      failwith msg
  
  let require (scope : scope) (name : symbol) loader =
    if required scope name then scope
    else
      match IM.byname name scope.sc_loaded with
      | Some (id,_) -> require_loaded id scope 

      | None -> 
          let imported = enter (for_loading scope) name in
          let thname   = imported.sc_name in
          let imported = loader imported in
          check_end_required imported thname;
          let cthr, name, imported = exit_r imported in 
          let scope = 
            { scope with
              sc_loaded = IM.add name cthr imported.sc_loaded; } in
          require_loaded name scope 


  (* ------------------------------------------------------------------ *)
  let clone (scope : scope) (_thcl : theory_cloning) =
    scope                               (* FIXME *)

  (* ------------------------------------------------------------------ *)
  let import_w3 scope dir file renaming = 
    let mk_renaming (l,k,s) = 
      let k = 
        match k with 
        | RNty -> EcWhy3.RDts 
        | RNop -> EcWhy3.RDls 
        | RNpr -> EcWhy3.RDpr in
      let s = EcIdent.create s in
      (l,k,s) in
    let renaming = List.map mk_renaming renaming in
    let env, lth = EcEnv.import_w3_dir scope.sc_env dir file renaming in
    let bind id = Context.bind (EcIdent.name id) in
    let add scope = function
      | CTh_type     (id,ty) ->
          { scope with sc_types = bind id ty scope.sc_types }
      | CTh_operator (id,op) ->
          { scope with sc_operators = bind id op scope.sc_operators }
      | CTh_axiom    (id,ax) -> 
          { scope with sc_axioms = bind id ax scope.sc_axioms } 
      | CTh_theory   (id,th) ->
          { scope with sc_theories = bind id th scope.sc_theories }
      | _ -> assert false in
    List.fold_left add { scope with sc_env = env } lth
end

module Prover = struct

  exception Unknown_prover of string 

  let pp_error fmt exn = 
    match exn with
    | Unknown_prover s ->
        Format.fprintf fmt "Unknown prover %s" s 
    | _ -> raise exn

  let _ = EcPexception.register pp_error 
      
  let check_prover_name name = 
    let s = unloc name in
    if not (EcWhy3.check_prover_name s) then 
      EcLocation.locate_error name.pl_loc (Unknown_prover s); 
    s

  let mk_prover_info scope time ns = 
    let dft = Prover_info.get scope.sc_options in
    let time = odfl dft.EcWhy3.prover_timelimit time in
    let time = if time < 1 then 1 else time in
    let provers = odfl dft.EcWhy3.prover_names ns in
    assert (provers <> []); (* FIXME ERROR message *)
    { EcWhy3.prover_names = provers;
      EcWhy3.prover_timelimit = time } 

  let set_prover_info scope time ns = 
    let pi = mk_prover_info scope time ns in
    { scope with sc_options = Prover_info.set scope.sc_options pi }

  let set_all scope = 
    let provers = EcWhy3.known_provers () in
    set_prover_info scope None (Some provers)

  let set_default scope = 
(*
    let provers = List.filter EcWhy3.check_prover_name ["Alt-Ergo";"Z3"] in
    let time = 3 in
    set_prover_info scope (Some time) (Some provers) *)
    set_all scope

  let process scope pi = 
    let ns = omap (snd pi) (List.map check_prover_name) in 
    set_prover_info scope (fst pi) ns

  let mk_prover_info scope pi =
    let ns = omap (snd pi) (List.map check_prover_name) in 
    mk_prover_info scope (fst pi) ns

  let full_check scope = 
    { scope with 
      sc_options = Check_mode.full_check scope.sc_options } 

  let check_proof scope b = 
    { scope with
      sc_options = Check_mode.check_proof scope.sc_options b}

end

module Tactic = struct

  open EcFol
  open EcLogic
  module TT = EcTypedtree
  module UE = EcUnify.UniEnv

  type tac_error = 
    | UnknownAxiom of qsymbol
    | BadTyinstance 
    | NothingToIntro
    | FormulaExcepted 
    | ElimDoNotWhatToDo 
    | NoCurrentGoal

  exception TacError of tac_error

  let pp_tac_error fmt = 
    function 
      | UnknownAxiom qs -> 
          Format.fprintf fmt "Unknown axioms or hypothesisvariable: %a" 
           pp_qsymbol qs
      | BadTyinstance -> 
          Format.fprintf fmt "Invalid type instance"
      | NothingToIntro ->
          Format.fprintf fmt "Nothing to introduce"
      | FormulaExcepted ->
          Format.fprintf fmt "formula excepted"
      | ElimDoNotWhatToDo ->
          Format.fprintf fmt "Elim : do not known what to do"
      | NoCurrentGoal ->
          Format.fprintf fmt "No current goal"

  let _ = EcPexception.register (fun fmt exn ->
    match exn with
    | TacError e -> pp_tac_error fmt e 
    | _ -> raise exn)

  let error loc e = EcLocation.locate_error loc (TacError e)

  let set_loc loc tac g = 
    try tac g 
    with e -> EcLocation.locate_error loc e 
    
  let process_tyargs env hyps tvi = 
    let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
    TT.transtvi env ue tvi 

  let process_instanciate env hyps ({pl_desc = pq; pl_loc = loc} ,tvi) = 
    let p,ax = 
      try EcEnv.Ax.lookup pq env
      with _ -> error loc (UnknownAxiom pq) in
    let args = process_tyargs env hyps tvi in
    let args = 
      match ax.EcDecl.ax_params, args with
      | [], None -> []
      | [], Some _ -> error loc BadTyinstance
      | ltv, Some (UE.TVIunamed l) ->
          if not (List.length ltv = List.length l) then error loc BadTyinstance;
          l 
      | ltv, Some (UE.TVInamed l) ->
          let get id = 
            try List.assoc (EcIdent.name id) l 
            with _ -> error loc BadTyinstance in
          List.map get ltv 
      | _, None -> error loc BadTyinstance in
    p,args 
    
  let process_global loc env tvi g = 
    let hyps = get_hyps g in
    let p, tyargs = process_instanciate env hyps tvi in
    set_loc loc t_glob env p tyargs g 

  let process_assumption loc env (pq,tvi) g = 
    let hyps,concl = get_goal g in
    match pq with
    | None -> 
        if (tvi <> None) then error loc BadTyinstance; 
        let h  = 
          try find_in_hyps env concl hyps 
          with _ -> assert false in
        t_hyp env h g
    | Some pq ->
        match unloc pq with
        | ([],ps) when LDecl.has_hyp ps hyps ->
            if (tvi <> None) then error pq.pl_loc BadTyinstance; 
            set_loc loc (t_hyp env (fst (LDecl.lookup_hyp ps hyps))) g
        | _ -> process_global loc env (pq,tvi) g

  let check_name hyps pi = 
    let s = odfl "_" (unloc pi) in
    let id = EcIdent.create s in
    try 
      LDecl.check_id id hyps; id
    with e -> EcLocation.locate_error pi.pl_loc e

  let process_intro pi g = 
    let hyps,concl = get_goal g in
    try 
      let id = check_name hyps pi in
      if is_forall concl then t_forall_intro id g
      else if is_imp concl then t_imp_intro id g
      else error pi.pl_loc NothingToIntro
    with e -> EcLocation.locate_error pi.pl_loc e

  let process_intros pis = t_lseq (List.map process_intro pis)

  let process_form env g pf ty =
    let hyps = get_hyps g in
    let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
    let ff = TT.transform (TT.Fenv.fenv_hyps env hyps) ue pf ty in
    EcFol.Fsubst.mapty (Tuni.subst (EcUnify.UniEnv.close ue)) ff

  let process_formula env g pf = 
    process_form env g pf tbool

  let process_exists1 env pf g =  
    let f = process_formula env g pf in
    t_exists_intro env f g 

  let process_exists env pfs = t_lseq (List.map (process_exists1 env) pfs)

  let process_elim env f ot g =
    match ot with
    | None -> t_imp_elim f g
    | Some pf ->
        let _,ty,_ = EcFol.destr_forall1 f in
        let ft = process_form env g pf ty in
        t_forall_elim env f ft g

  let process_intro_elim env ot g =
    let id = EcIdent.create "_" in
    let ff = fst(destr_imp (get_concl g)) in
    let seq = 
      if ot = None then [t_hyp env id; t_clear id; t_clear id]
      else [t_hyp env id; t_clear id] in
    t_seq (t_imp_intro id)
      (t_seq_subgoal (process_elim env ff ot) seq) g

  let rec process_intro_elims env ots g = 
    match ots with
    | [] -> t_id g
    | ot::ots -> 
        t_on_last (process_intro_elim env ot g)
          (process_intro_elims env ots) 
    
  let process_elim_kind env g k = 
    let hyps = get_hyps g in
    match k with
    | ElimHyp (pq,tvi) ->
        begin match unloc pq with 
        | ([],ps) when LDecl.has_hyp ps hyps ->
            (* FIXME warning if tvi is not None *)
            let id,ff = LDecl.lookup_hyp ps hyps in
            t_hyp env id, ff
        | _ -> 
            let p,args = process_instanciate env hyps (pq,tvi) in
            let ff = EcEnv.Ax.instanciate p args env in
            t_glob env p args, ff
        end
    | ElimForm pf ->
        let ff = process_formula env g pf in
        t_id, ff 

  let process_elims loc only_app env pe g =       
    let tac, ff = process_elim_kind env g pe.elim_kind in
    if is_forall ff || is_imp ff then
      begin match pe.elim_args with
      | [] -> error loc FormulaExcepted 
      | ot::ots -> 
          let seq = 
            if ot = None then [tac;t_id; process_intro_elims env ots]
            else [tac; process_intro_elims env ots] in
          t_seq_subgoal (process_elim env ff ot) seq g
      end
    else if only_app then error loc ElimDoNotWhatToDo (* FIXME *)
    else if is_and ff then t_on_first (t_and_elim ff g) tac
    else if is_or ff then t_on_first (t_or_elim ff g) tac
    else if is_exists ff then t_on_first (t_exists_elim ff g) tac 
    else  error loc ElimDoNotWhatToDo

  let process_apply loc env pe g = 
    let id = EcIdent.create "_" in
    t_on_last (process_elims loc true env pe g) 
      (t_seq (t_imp_intro id) (t_hyp env id))

  let process_trivial scope pi env g =
    let pi = Prover.mk_prover_info scope pi in
    t_trivial pi env g

  let rec process_logic_tacs scope env (tacs:ptactics) (gs:goals) : goals = 
    match tacs with
    | [] -> gs
    | {pl_desc = Psubgoal tacs1; pl_loc = loc } :: tacs2 ->  
        let gs = 
          set_loc loc 
            (t_subgoal (List.map (process_logic_tac scope env) tacs1)) gs in
        process_logic_tacs scope env tacs2 gs
    | tac1 :: tacs2 ->
        let gs = t_on_goals (process_logic_tac scope env tac1) gs in
        process_logic_tacs scope env tacs2 gs 
        
  and process_logic_tac scope env (tac:ptactic) (g:goal) : goals = 
    let loc = tac.pl_loc in
    let tac = 
      match unloc tac with
      | Pidtac         -> t_id 
      | Passumption pq -> process_assumption loc env pq
      | Ptrivial pi    -> process_trivial scope pi env 
      | Pintro pi      -> process_intros pi 
      | Psplit         -> t_and_intro 
      | Pexists fs     -> process_exists env fs
      | Pleft          -> t_or_intro true
      | Pright         -> t_or_intro false
      | Pelim pe       -> process_elims loc false env pe
      | Papply pe      -> process_apply loc env pe
      | Pseq tacs      -> 
          fun (juc,n) -> process_logic_tacs scope env tacs (juc,[n])
      | Psubgoal _     -> assert false in
    set_loc loc tac g

  let process_logic scope env juc loc tacs = 
    let (juc,n) = 
      try get_first_goal juc 
      with _ -> error loc NoCurrentGoal in
    upd_done (fst (process_logic_tacs scope env tacs (juc,[n])))
    
  let process scope tac =
    if Check_mode.check scope.sc_options then
      let loc = match tac with | [] -> assert false | t::_ -> t.pl_loc in  
      match scope.sc_pr_uc with
      | [] -> error loc NoCurrentGoal
      | puc :: pucs ->
          match puc.puc_kind with
          | PUCK_logic juc -> 
              let juc = process_logic scope scope.sc_env juc loc tac in
              { scope with 
                sc_pr_uc = { puc with puc_kind = PUCK_logic juc } :: pucs }
    else scope

  let out_goal scope = 
    match scope.sc_pr_uc with
    | [] -> Pprint.empty
    | puc :: _ ->
        match puc.puc_kind with
        | PUCK_logic juc ->
            try 
              let g = get_goal (get_first_goal juc) in
              EcPrinting.EcPP.pr_lgoal (EcPrinting.EcPP.mono scope.sc_env) g
            with EcBaseLogic.NotAnOpenGoal _ -> Pprint.text "No more goals"
    
end 

module Ax = struct
  open EcParsetree
  open EcTypes
  open EcDecl

  module TT = EcTypedtree

  let bind (scope : scope) ((x, ax) : _ * axiom) =
    { scope with
        sc_axioms = Context.bind (EcIdent.name x) ax scope.sc_axioms;
        sc_env    = EcEnv.Ax.bind x ax scope.sc_env; }

  let start_lemma scope name tparams concl = 
    let hyps = { EcFol.h_tvar = tparams;
                 EcFol.h_local = []; } in
    let puc = {
      puc_name = name ;
      puc_kind = PUCK_logic (EcLogic.open_juc hyps concl) } in
    { scope with 
      sc_pr_uc = puc :: scope.sc_pr_uc }
    

  let save scope loc = 
    if Check_mode.check scope.sc_options then
      match scope.sc_pr_uc with
      | [] -> Tactic.error loc Tactic.NoCurrentGoal
      |  { puc_name = name; puc_kind = PUCK_logic juc } :: pucs ->
          let pr = EcLogic.close_juc juc in
          let hyps,concl = pr.EcBaseLogic.j_decl in
          let tparams = hyps.EcFol.h_tvar in
          assert (hyps.EcFol.h_local = []);
          let axd = { ax_params = tparams;
                      ax_spec = Some concl;
                      ax_kind = Lemma (Some pr) } in
          let scope = { scope with sc_pr_uc = pucs } in
          Some name, bind scope (EcIdent.create name, axd)
    else None, scope

  let add (scope : scope) (ax : paxiom) =
    let ue = EcUnify.UniEnv.create None in
    let concl = 
      TT.transformula (TT.Fenv.mono_fenv scope.sc_env) ue ax.pa_formula in
    let concl = 
      EcFol.Fsubst.mapty (Tuni.subst (EcUnify.UniEnv.close ue)) concl in
    let tparams = EcUnify.UniEnv.tparams ue in 
    let check = Check_mode.check scope.sc_options in
    let loc = ax.pa_name.pl_loc in
    match ax.pa_kind with
    | PILemma when check -> 
        None, start_lemma scope (unloc ax.pa_name) tparams concl 
    | PLemma when check -> 
        let scope = start_lemma scope (unloc ax.pa_name) tparams concl in
        let scope = 
          Tactic.process scope
            [{ pl_loc = loc; pl_desc = Ptrivial (None,None) }] in
        let name, scope = save scope loc in
        name, scope
    | _ -> 
        let axd = { ax_params = tparams;
                    ax_spec = Some concl;
                    ax_kind = Axiom } in
        Some (unloc ax.pa_name), bind scope (EcIdent.create (unloc ax.pa_name), axd)
          
end

