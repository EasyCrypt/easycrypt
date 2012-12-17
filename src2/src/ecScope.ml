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
  sc_initial    : scope option;
  sc_required   : EcTypesmod.theory IM.t;
}

(* -------------------------------------------------------------------- *)
let empty =
  let scope =
    let env  = EcEnv.initial in
    let name = EcPath.basename env.EcEnv.env_scope in
      { sc_name       = name;
        sc_types      = Context.empty ();
        sc_operators  = Context.empty ();
        sc_axioms     = Context.empty ();
        sc_modtypes   = Context.empty ();
        sc_modules    = Context.empty ();
        sc_theories   = Context.empty ();
        sc_env        = env;
        sc_top        = None;
        sc_required   = IM.empty;
        sc_initial    = None; }
  in
    { scope with sc_initial = Some scope }

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
let root (scope : scope) =
  match scope.sc_initial with
  | None -> assert false
  | Some scope -> scope

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
    sc_initial    = scope.sc_initial;
    sc_required   = IM.empty; }

(* -------------------------------------------------------------------- *)
module Op = struct
  open EcTypes
  open EcDecl

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
            let env = EcEnv.Var.bindall (List.combine xs dom) scope.sc_env in
            let body = TT.transexpcast env policy ue codom body in
            Some(xs, Esubst.uni (EcUnify.UniEnv.asmap ue) body) in
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
    IM.byname name scope.sc_required <> None

  let enter (scope : scope) (name : symbol) =
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
        sc_initial    = scope.sc_initial;
        sc_required   = scope.sc_required; }

  let exit (scope : scope) =
    match scope.sc_top with
    | None     -> raise TopScope
    | Some sup ->
        let cth = EcEnv.Theory.close scope.sc_env in
          (scope.sc_name, bind sup (scope.sc_name, cth))

  let import (scope : scope) (name : qsymbol) =
    let path = fst (EcEnv.Theory.lookup name scope.sc_env) in
      { scope with
          sc_env = EcEnv.Theory.import path scope.sc_env }

  let export (scope : scope) (name : qsymbol) =
    let path = fst (EcEnv.Theory.lookup name scope.sc_env) in
      { scope with
          sc_env = EcEnv.Theory.export path scope.sc_env }

  let require (scope : scope) (name : symbol) loader =
    if loaded scope name then
      scope
    else begin
      let imported = enter (root scope) name in
      let thname   = imported.sc_name in
      let imported = loader imported in
        if imported.sc_name <> thname then
          failwith "end-of-theory in required library";

      let imported = snd (exit imported) in
      let path     = EcPath.Pqname (path imported, thname) in
      let theory   = EcEnv.Theory.lookup_by_path path imported.sc_env in

        { scope with
            sc_env      = EcEnv.Theory.require thname theory scope.sc_env;
            sc_required = IM.add thname theory scope.sc_required; }
    end
end

