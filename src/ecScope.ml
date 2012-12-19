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
  ld_loaded   : EcEnv.comp_th IM.t;
  ld_required : EcIdent.t list;
}

type scope = {
  sc_name       : EcIdent.t;
  sc_types      : EcDecl.tydecl          Context.context;
  sc_operators  : EcDecl.operator        Context.context;
  sc_axioms     : EcDecl.axiom           Context.context;
  sc_modules    : EcTypesmod.module_expr Context.context;
  sc_modtypes   : EcTypesmod.tymod       Context.context;
  sc_theories   : EcTypesmod.theory      Context.context;
  sc_env        : EcEnv.env;
  sc_top        : scope option;
  sc_loader     : loader;
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
      sc_loader     = loader; }

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
    sc_loader     = { scope.sc_loader with ld_required = []; }
  }

(* -------------------------------------------------------------------- *)
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
    let tp = TT.TyPolicy.init (omap op.po_tyvars unlocs) in
    let dom,   tp  = TT.transtys scope.sc_env tp (odfl [] op.po_dom) in
    let codom, tp  = TT.transty  scope.sc_env tp op.po_codom in
    let policy = { TT.epl_prob = op.po_prob } in
    let body, ue =
      let ue = EcUnify.UniEnv.create () in
      let body = 
        match op.po_body with
        | None -> None
        | Some(xs, body) ->
            let xs = List.map EcIdent.create (unlocs xs) in
            let env =
              EcEnv.Var.bindall ~local:true (List.combine xs dom) scope.sc_env
            in
            let body = TT.transexpcast env policy ue codom body in
              EcTypes.Dump.ex_dump EcDebug.initial body;
              Some (xs, Esubst.uni (EcUnify.UniEnv.asmap ue) body) in
      body, ue in
    let uni = Subst.uni (EcUnify.UniEnv.asmap ue) in

      EcUnify.UniEnv.dump EcDebug.initial ue;

    let dom, codom = List.map uni dom, uni codom in
    let dom = if op.po_dom = None then None else Some dom in
    let tyop =
      EcDecl.mk_op (TT.TyPolicy.decl tp) dom codom
        body op.po_prob
    in
      bind scope (EcIdent.create (unloc op.po_name), tyop)
end

(* -------------------------------------------------------------------- *)
module Pred = struct
  module TT = EcTypedtree

  let add (scope : scope) (op : ppredicate) =
    let tp  = TT.TyPolicy.init (omap op.pp_tyvars unlocs) in
    let dom,   tp  = TT.transtys scope.sc_env tp (odfl [] op.pp_dom) in
    let body, ue =
      let body, ue = 
        let ue = EcUnify.UniEnv.create () in
        match op.pp_body with
        | None -> None, ue
        | Some(xs,body) ->
            let xs = List.map EcIdent.create (unlocs xs) in
            let env = TT.Fenv.mono_fenv scope.sc_env in
            let env = TT.Fenv.bind_locals env xs dom in 
            let body,ue = TT.transformula env tp ue body in
            Some(xs, body), ue in
      body, ue in
    let uni = Subst.uni (EcUnify.UniEnv.asmap ue) in 
    let dom = List.map uni dom in
    let dom = if op.pp_dom = None then None else Some dom in
    let tyop =
      EcDecl.mk_pred (TT.TyPolicy.decl tp) dom body
    in
      Op.bind scope (EcIdent.create (unloc op.pp_name), tyop)
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  open EcParsetree
  open EcTypes
  open EcDecl

  module TT = EcTypedtree

  let transform_kind = function
    | PAxiom -> Axiom
    | PLemma -> Lemma 

  let bind (scope : scope) ((x, ax) : _ * axiom) =
    { scope with
        sc_axioms = Context.bind (EcIdent.name x) ax scope.sc_axioms;
        sc_env    = EcEnv.Ax.bind x ax scope.sc_env; }

  let add (scope : scope) (ax : paxiom) =
    let form, _ = 
      TT.transformula (TT.Fenv.mono_fenv scope.sc_env) 
        TT.TyPolicy.empty (EcUnify.UniEnv.create()) ax.pa_formula
    in

    let axd = { ax_spec = form;
                ax_kind = transform_kind ax.pa_kind }
    in
      
      bind scope (EcIdent.create (unloc ax.pa_name), axd)
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
    let tp = TyPolicy.init (Some (unlocs args)) in
    let tydecl = {
      tyd_params = TyPolicy.decl tp;
      tyd_type   = None;
    } in
      bind scope (EcIdent.create (unloc name), tydecl)

  let define (scope : scope) (args, name) body = 
    let tp = TyPolicy.init (Some (unlocs args)) in
    let body, tp = transty scope.sc_env tp body in
    let tydecl = {
      tyd_params = TyPolicy.decl tp;
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

  let bind (scope : scope) ((x, cth) : _ * EcEnv.comp_th) =
    let theory = EcEnv.theory_of_comp_th cth in
      { scope with
          sc_theories = Context.bind (EcIdent.name x) theory scope.sc_theories;
          sc_env      = EcEnv.Theory.bind x cth scope.sc_env; }

  let loaded (scope : scope) (name : symbol) =
    IM.byname name scope.sc_loader.ld_loaded <> None

  let required (scope : scope) (name : symbol) =
    List.exists
      (fun x -> EcIdent.name x = name)
      scope.sc_loader.ld_required

  let enter (scope : scope) (name : symbol) =
    subscope scope name

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
          EcFormat.pp_err EcPrinting.pp_env scope.sc_env;
          (cth, scope.sc_name, bind sup (scope.sc_name, cth))

  let exit (scope : scope) =
    let (_, name, scope) = exit_r scope in
      (name, scope)

  let import (scope : scope) (name : qsymbol) =
    let path = fst (EcEnv.Theory.lookup name scope.sc_env) in
      { scope with
          sc_env = EcEnv.Theory.import path scope.sc_env }

  let export (scope : scope) (name : qsymbol) =
    let path = fst (EcEnv.Theory.lookup name scope.sc_env) in
      { scope with
          sc_env = EcEnv.Theory.export path scope.sc_env }

  let require (scope : scope) (name : symbol) loader =
    if required scope name then
      scope
    else
      match IM.byname name scope.sc_loader.ld_loaded with
      | Some (name, theory) -> scope

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
      | Th_type     (id,ty) ->
          { scope with sc_types = bind id ty scope.sc_types }
      | Th_operator (id,op) ->
          { scope with sc_operators = bind id op scope.sc_operators }
      | Th_axiom    (id,ax) -> 
          { scope with sc_axioms = bind id ax scope.sc_axioms } 
      | _ -> assert false in
    List.fold_left add { scope with sc_env = env } lth
end
