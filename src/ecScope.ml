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

(* -------------------------------------------------------------------- *)
type loader = {
  ld_loaded   : EcEnv.ctheory_w3 IM.t;
  ld_required : EcIdent.t list;
}

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
  sc_modtypes   : EcTypesmod.tymod       Context.context;
  sc_theories   : EcTypesmod.ctheory     Context.context;
  sc_env        : EcEnv.env;
  sc_top        : scope option;
  sc_loader     : loader;
  sc_pr_uc      : proof_uc list; 
}

(* -------------------------------------------------------------------- *)
let empty =
  let env    = EcEnv.initial
  and loader = { ld_loaded = IM.empty; ld_required = []; } in

    { sc_name       = EcPath.basename env.EcEnv.env_scope;
      sc_types      = Context.empty ();
      sc_operators  = Context.empty ();
      sc_axioms     = Context.empty ();
      sc_modtypes   = Context.empty ();
      sc_modules    = Context.empty ();
      sc_theories   = Context.empty ();
      sc_env        = EcEnv.initial;
      sc_top        = None;
      sc_loader     = loader;
      sc_pr_uc      = []; }

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
  let loader = {
    ld_loaded   = scope.sc_loader.ld_loaded;
    ld_required = [];
  }
  in
    { empty with sc_loader = loader }

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
    sc_loader     = { scope.sc_loader with ld_required = []; };
    sc_pr_uc    = [];
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
    let policy = { TT.epl_prob = op.po_prob } in
    let body =
      match op.po_body with
      | None -> None
      | Some(xs, body) ->
          let xs = List.map EcIdent.create (unlocs xs) in
          let env =
            EcEnv.Var.bindall (List.combine xs dom) None scope.sc_env
          in
          let body = TT.transexpcast env policy ue codom body in
          Some (xs, body) in
    let uni = Tuni.subst (EcUnify.UniEnv.close ue) in
    let body = omap body (fun (ids,body) -> ids, Esubst.mapty uni body) in
    let (dom,codom) = List.map uni dom, uni codom in
    let tparams = EcUnify.UniEnv.tparams ue in 
    let tyop = EcDecl.mk_op tparams dom codom body op.po_prob in
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

  let add (scope : scope) (name : symbol) (m : pmodule_expr) =
    let name = EcIdent.create name in
    let m    = EcTypedtree.transmod scope.sc_env name m in
      bind scope m
end

(* -------------------------------------------------------------------- *)
module ModType = struct
  let bind (scope : scope) ((x, tymod) : _ * tymod) =
    { scope with
        sc_modtypes = Context.bind (EcIdent.name x) tymod scope.sc_modtypes;
        sc_env      = EcEnv.ModTy.bind x tymod scope.sc_env; }

  let add (scope : scope) (name : symbol) (i : pmodule_type) =
    let tymod = EcTypedtree.transtymod scope.sc_env i in
      bind scope (EcIdent.create name, tymod)
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
  let loaded (scope : scope) (name : symbol) =
    IM.byname name scope.sc_loader.ld_loaded <> None

  (* ------------------------------------------------------------------ *)
  let required (scope : scope) (name : symbol) =
    List.exists
      (fun x -> EcIdent.name x = name)
      scope.sc_loader.ld_required

  (* ------------------------------------------------------------------ *)
  let enter (scope : scope) (name : symbol) =
    subscope scope name

  (* ------------------------------------------------------------------ *)
  let exit_r (scope : scope) =
    match scope.sc_top with
    | None     -> raise TopScope
    | Some sup ->
        let cth    = EcEnv.Theory.close scope.sc_env in
        let loaded = scope.sc_loader.ld_loaded in
        let sup    =
          let env, reqs =
            List.fold_right
              (fun rname (env, reqs) ->
                if not (required sup (EcIdent.name rname)) then
                  match IM.byident rname loaded with
                  | None     -> assert false
                  | Some rth ->
                      let env  = EcEnv.Theory.require rname rth env
                      and reqs = rname :: reqs in
                        (env, reqs)
                else
                  (env, reqs))
              scope.sc_loader.ld_required
              (sup.sc_env, sup.sc_loader.ld_required)
          in
            { sup with
                sc_env    = env;
                sc_loader = { ld_loaded   = loaded;
                              ld_required = reqs; }
            }
        in
          (cth, scope.sc_name, bind sup (scope.sc_name, cth))

  (* ------------------------------------------------------------------ *)
  let exit (scope : scope) =
    let (_, name, scope) = exit_r scope in
      (name, scope)

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
  let require (scope : scope) (name : symbol) loader =
    if required scope name then
      scope
    else
      match IM.byname name scope.sc_loader.ld_loaded with
      | Some _ -> scope

      | None -> begin
          let imported = enter (for_loading scope) name in
          let thname   = imported.sc_name in
          let imported = loader imported in
 
            if imported.sc_name <> thname then
              failwith "end-of-file while processing external theory";
 
          let ctheory, _, imported = exit_r imported in
          let loaded = IM.add thname ctheory imported.sc_loader.ld_loaded in

          let env, reqs =
            List.fold_right
              (fun rname (env, reqs) ->
                if not (required scope (EcIdent.name rname)) then
                  match IM.byident rname loaded with
                  | None     -> assert false
                  | Some rth ->
                      let env  = EcEnv.Theory.require rname rth env
                      and reqs = rname :: reqs in
                        (env, reqs)
                else
                  (env, reqs))
              (thname :: imported.sc_loader.ld_required)
              (scope.sc_env, scope.sc_loader.ld_required)
          in
            { scope with
                sc_env    = env;
                sc_loader = { ld_loaded   = loaded;
                              ld_required = reqs; }
            }
      end

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

module Tactic = struct

  open EcFol
  open EcLogic
  module TT = EcTypedtree

  let process_tyargs env hyps args = 
    let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
    List.map (TT.transty TT.tp_tydecl env ue) args 

  let process_instanciate env hyps (pq,tyargs) = 
    let p = 
      try fst (EcEnv.Ax.lookup (unloc pq) env)
      with _ -> assert false (* FIXME error message *) in
    let args = process_tyargs env hyps tyargs in
    p,args 
    
  let process_global env arg g = 
    let hyps = get_hyps g in
    let p, tyargs = process_instanciate env hyps arg in
    t_glob env p tyargs g 

  let process_assumption env (pq,args) g = 
    let hyps,concl = get_goal g in
    match pq with
    | None -> 
        assert (args = []); (* FIXME error message *)
        let h  = 
          try find_in_hyps env concl hyps 
          with _ -> assert false in
        t_hyp env h g
    | Some pq ->
        match unloc pq, args with
        | ([],ps), [] when LDecl.has_hyp ps hyps ->
            t_hyp env (fst (LDecl.lookup_hyp ps hyps)) g
        | _, _ -> process_global env (pq,args) g

  let check_name hyps pi = 
    let s = odfl "_" (unloc pi) in
    let id = EcIdent.create s in
    try LDecl.check_id id hyps; id
    with _ -> assert false (* FIXME error message *)

  let process_intro pi g = 
    let hyps,concl = get_goal g in
    let id = check_name hyps pi in
    if is_forall concl then t_forall_intro id g
    else if is_imp concl then t_imp_intro id g
    else assert false (* FIXME error message *)

  let process_intros pis = t_lseq (List.map process_intro pis)

  let process_formula env g pf =
    let hyps = get_hyps g in
    let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
    let ff = TT.transformula (TT.Fenv.fenv_hyps env hyps) ue pf in
    EcFol.Fsubst.mapty (Tuni.subst (EcUnify.UniEnv.close ue)) ff

  let process_exists1 env pf g =  
    let f = process_formula env g pf in
    t_exists_intro env f g 

  let process_exists env pfs = t_lseq (List.map (process_exists1 env) pfs)

  let process_elim env f ot g =
    (* FIXME error message *)
    match ot with
    | None -> t_imp_elim f g
    | Some pf ->
       let ft = process_formula env g pf in
       t_forall_elim env f ft g

  let process_intro_elim env ot g =
    let id = EcIdent.create "_" in
    let ff = fst(destr_imp (get_concl g)) in
    t_seq_subgoal (t_seq (t_imp_intro id) (process_elim env ff ot))
      [ t_hyp env id;
        t_clear id] g

  let rec process_intro_elims env ots g = 
    match ots with
    | [] -> t_id g
    | ot::ots -> 
        t_on_last (process_intro_elim env ot g)
          (process_intro_elims env ots) 
    
  let process_elim_kind env g k = 
    let hyps = get_hyps g in
    match k with
    | ElimHyp (pq,args) ->
        begin match unloc pq, args with 
        | ([],ps), [] when LDecl.has_hyp ps hyps ->
            let id,ff = LDecl.lookup_hyp ps hyps in
            t_hyp env id, ff
        | _, _ -> 
            let p,args = process_instanciate env hyps (pq,args) in
            let ff = EcEnv.Ax.instanciate p args env in
            t_glob env p args, ff
        end
    | ElimForm pf ->
        let ff = process_formula env g pf in
        t_id, ff

  let process_elims env pe g =       
    let tac, ff = process_elim_kind env g pe.elim_kind in
    if is_and ff then t_on_first (t_and_elim ff g) tac
    else if is_or ff then t_on_first (t_or_elim ff g) tac
    else if is_exists ff then t_on_first (t_exists_elim ff g) tac 
    else if is_forall ff || is_imp ff then
      begin match pe.elim_args with
      | [] -> assert false (* FIXME error message *)
      | ot::ots -> 
          t_seq_subgoal (process_elim env ff ot)
             [tac;process_intro_elims env ots] g
      end
    else assert false (* FIXME error message *)

  let rec process_logic_tacs env (tacs:ptactics) (gs:goals) : goals = 
    match tacs with
    | [] -> gs
    | {pl_desc = Psubgoal tacs1} :: tacs2 ->  
        let gs = t_subgoal (List.map (process_logic_tac env) tacs1) gs in
        process_logic_tacs env tacs2 gs
    | tac1 :: tacs2 ->
        let gs = t_on_goals (process_logic_tac env tac1) gs in
        process_logic_tacs env tacs2 gs 
        
  and process_logic_tac env (tac:ptactic) (g:goal) : goals = 
    match unloc tac with
    | Pidtac         -> t_id g 
    | Passumption pq -> process_assumption env pq g 
    | Ptrivial       -> t_trivial env g
    | Pintro pi      -> process_intros pi g
    | Psplit         -> t_and_intro g
    | Pexists fs     -> process_exists env fs g
    | Pleft          -> t_or_intro true g
    | Pright         -> t_or_intro false g
    | Pelim pe       -> process_elims env pe g
    | Pseq tacs      -> 
        let (juc,n) = g in
        process_logic_tacs env tacs (juc,[n])
    | Psubgoal _     -> assert false 

  let process_logic env juc tacs = 
    let (juc,n) = get_first_goal juc in
    fst (process_logic_tacs env tacs (juc,[n]))
    
  let process scope tac =
    match scope.sc_pr_uc with
    | [] -> assert false (* FIXME error message *)
    | puc :: pucs ->
        match puc.puc_kind with
        | PUCK_logic juc -> 
            let juc = process_logic scope.sc_env juc tac in
            { scope with 
              sc_pr_uc = { puc with puc_kind = PUCK_logic juc } :: pucs }


    
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
    

  let save scope = 
    match scope.sc_pr_uc with
    | [] -> assert false (* FIXME error message *)
    |  { puc_name = name; puc_kind = PUCK_logic juc } :: pucs ->
        let pr = EcLogic.close_juc juc in
        let hyps,concl = pr.EcBaseLogic.j_decl in
        let tparams = hyps.EcFol.h_tvar in
        assert (hyps.EcFol.h_local = []);
        let axd = { ax_params = tparams;
                    ax_spec = Some concl;
                    ax_kind = Lemma (Some pr) } in
        let scope = { scope with sc_pr_uc = pucs } in
        bind scope (EcIdent.create name, axd)
          
  let add (scope : scope) (ax : paxiom) =
    let ue = EcUnify.UniEnv.create None in
    let concl = 
      TT.transformula (TT.Fenv.mono_fenv scope.sc_env) ue ax.pa_formula in
    let concl = 
      EcFol.Fsubst.mapty (Tuni.subst (EcUnify.UniEnv.close ue)) concl in
    let tparams = EcUnify.UniEnv.tparams ue in 
    match ax.pa_kind with
    | PAxiom -> 
        let axd = { ax_params = tparams;
                    ax_spec = Some concl;
                    ax_kind = Axiom } in
        bind scope (EcIdent.create (unloc ax.pa_name), axd)
    | PILemma -> start_lemma scope (unloc ax.pa_name) tparams concl 
    | PLemma -> 
        let scope = start_lemma scope (unloc ax.pa_name) tparams concl in
        let scope = 
          Tactic.process scope
            [{ pl_loc = Location.dummy; pl_desc = Ptrivial }] in
        save scope
        
end
