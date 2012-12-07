(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcParsetree
open EcTypes
open EcTypesmod

(* -------------------------------------------------------------------- *)
module Context = struct
  module SM = EcMaps.StringMap

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
      let normalize (v : 'a data) ={
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
type action =
  | Ac_type      of (EcIdent.t * EcDecl.tydecl)
  | Ac_operator  of (EcIdent.t * EcDecl.operator)
  | Ac_axiom     of (EcIdent.t * EcDecl.axiom)
  | Ac_modtype   of (EcIdent.t * EcTypesmod.tymod)
  | Ac_module    of EcTypesmod.module_expr
  | Ac_theory    of (EcIdent.t * EcTypesmod.theory)


type scope = {
  sc_name       : EcIdent.t;
  sc_types      : EcDecl.tydecl          Context.context;
  sc_operators  : EcDecl.operator        Context.context;
  sc_axioms     : EcDecl.axiom           Context.context;
  sc_modules    : EcTypesmod.module_expr Context.context;
  sc_modtypes   : EcTypesmod.tymod       Context.context;
  sc_theories   : EcTypesmod.theory      Context.context;
  sc_history    : action list;
  sc_env        : EcEnv.env;
  sc_top        : scope option;
}

(* -------------------------------------------------------------------- *)
let name (scope : scope) =
  scope.sc_name

(* -------------------------------------------------------------------- *)
let env (scope : scope) = scope.sc_env

(* -------------------------------------------------------------------- *)
let attop (scope : scope) = scope.sc_top = None

(* -------------------------------------------------------------------- *)
let subscope (scope : scope option) (name : symbol) =
  let env =
    match scope with
    | None       -> EcEnv.empty
    | Some scope -> scope.sc_env
  in
  let (name, env) = EcEnv.enter name env in

  { sc_name       = name;
    sc_types      = Context.empty ();
    sc_operators  = Context.empty ();
    sc_axioms     = Context.empty ();
    sc_modtypes   = Context.empty ();
    sc_modules    = Context.empty ();
    sc_theories   = Context.empty ();
    sc_history    = [];
    sc_env        = env;
    sc_top        = scope; }

(* -------------------------------------------------------------------- *)
let bind (scope : scope) (action : action) =
  match action with
  | Ac_type (x, tydecl) ->
      { scope with
          sc_types   = Context.bind (EcIdent.name x) tydecl scope.sc_types;
          sc_history = action :: scope.sc_history;
          sc_env     = EcEnv.Ty.bind x tydecl scope.sc_env }

  | Ac_operator (x, op) ->
      { scope with
          sc_operators = Context.bind (EcIdent.name x) op scope.sc_operators;
          sc_history   = action :: scope.sc_history;
          sc_env       = EcEnv.Op.bind x op scope.sc_env }

  | Ac_axiom (x, ax) ->
      { scope with
          sc_axioms = Context.bind (EcIdent.name x) ax scope.sc_axioms;
          sc_history   = action :: scope.sc_history;
          sc_env       = EcEnv.Ax.bind x ax scope.sc_env }

  | Ac_modtype (x, tymod) ->
      { scope with
          sc_modtypes = Context.bind (EcIdent.name x) tymod scope.sc_modtypes;
          sc_history  = action :: scope.sc_history;
          sc_env      = EcEnv.ModTy.bind x tymod scope.sc_env }

  | Ac_module m ->
      { scope with
          sc_modules = Context.bind (EcIdent.name m.me_name) m scope.sc_modules;
          sc_history = action :: scope.sc_history;
          sc_env     = EcEnv.Mod.bind m.me_name m.me_sig scope.sc_env }

  | Ac_theory (x, th) ->
      { scope with
          sc_theories = Context.bind (EcIdent.name x) th scope.sc_theories;
          sc_history  = action :: scope.sc_history;
          sc_env      = EcEnv.Theory.bind x th scope.sc_env }

(* -------------------------------------------------------------------- *)
module Op = struct
  module TT = EcTypedtree

  let add (scope : scope) (op : poperator) =
    let tp  = TT.TyPolicy.init op.po_tyvars in
    let dom,   tp  = TT.transtys scope.sc_env tp (odfl [] op.po_dom) in
    let codom, tp  = TT.transty  scope.sc_env tp op.po_codom in
    let policy = { TT.epl_prob = op.po_prob } in
    let body, ue =
      let ue = EcUnify.UniEnv.create () in
      let body = 
        match op.po_body with
        | None -> None
        | Some(xs,body) ->
            let xs = List.map EcIdent.create xs in
            let env = EcEnv.Var.bindall (List.combine xs dom) scope.sc_env in
            let body = TT.transexpcast env policy ue codom body in
            Some(xs, Esubst.uni (EcUnify.UniEnv.asmap ue) body) in
      body, ue in
    let uni = Subst.uni (EcUnify.UniEnv.asmap ue) in 
    let dom, codom = List.map uni dom, uni codom in
    let dom = if op.po_dom = None then None else Some dom in
    let tyop =
      EcDecl.mk_op (TT.TyPolicy.decl tp) dom codom
        body op.po_prob in
    bind scope (Ac_operator (EcIdent.create op.po_name, tyop))
end

(* -------------------------------------------------------------------- *)
module Pred = struct
  module TT = EcTypedtree

  let add (scope : scope) (p : ppredicate) = assert false 
(*
    let tp = TT.TyPolicy.init p.pp_tyvars in
    match p.pp_def with
    | AbstrDef None -> assert false 
    | AbstrDef (Some dom) ->
        let dom, tp    = TT.transtys scope.sc_env tp dom in
        let typ = {
          pred_params = TT.TyPolicy.decl tp;
          pred_sig    = dom;
          pred_def    = None 
        } in
        bind scope (Ac_predicate (EcIdent.create p.pp_name, typ))
    | ConcrDef(params, def) ->
        let _dom, _tp = TT.transtys scope.sc_env tp (List.map snd params) in
        let _tp = TT.TyPolicy.relax tp in
        assert false 
*)
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  open EcParsetree
  open EcTypes
  open EcDecl

  module TT = EcTypedtree

  let transform (scope : scope) f e =
    { scope with
        sc_axioms = f scope.sc_axioms;
        sc_env     = e scope.sc_env }

  let transform_kind = function
    | PAxiom -> Axiom
    | PLemma -> Lemma 

  let add (scope : scope) (ax : paxiom) =
    let form = 
      TT.transformula (TT.Fenv.mono_fenv scope.sc_env) 
        TT.TyPolicy.empty ax.pa_formula in
    let axd = { 
      ax_spec = form;
      ax_kind = transform_kind ax.pa_kind
    } in
    transform scope
      (Context.bind ax.pa_name axd)
      (EcEnv.Ax.bind (EcIdent.create ax.pa_name) axd)
end

(* -------------------------------------------------------------------- *)
module Ty = struct
  open EcDecl
  open EcTypedtree

  let bind (scope : scope) name tydecl =
    bind scope (Ac_type (name, tydecl))

  let alias (scope : scope) name ty =
    (* FIXME : check that ty is closed, or close it *)
    let tydecl = {tyd_params = []; tyd_type = Some ty } in
      bind scope (EcIdent.create name) tydecl

  let add (scope : scope) (args, name) = 
    let tp = TyPolicy.init (Some args) in
    let tydecl = {
      tyd_params = TyPolicy.decl tp;
      tyd_type   = None;
    } in
    bind scope (EcIdent.create name) tydecl

  let define (scope : scope) (args, name) body = 
    let tp = TyPolicy.init (Some args) in
    let body, tp = transty scope.sc_env tp body in
    let tydecl = {
      tyd_params = TyPolicy.decl tp;
      tyd_type   = Some body;
    } in
    bind scope (EcIdent.create name) tydecl
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  let transform (scope : scope) f e =
    { scope with
        sc_modules = f scope.sc_modules;
        sc_env     = e scope.sc_env    ; }

  let add (scope : scope) (name : symbol) (m : pmodule_expr) =
    let name = EcIdent.create name in
    let m    = EcTypedtree.transmod scope.sc_env name m in
      transform scope
        (fun ctxt -> Context.bind (EcIdent.name name) m ctxt)
        (fun env  -> EcEnv.Mod.bind name m.me_sig env)
end

(* -------------------------------------------------------------------- *)
module ModType = struct
  let transform (scope : scope) f e =
    { scope with
        sc_modtypes = f scope.sc_modtypes;
        sc_env      = e scope.sc_env     ; }

  let add (scope : scope) (name : symbol) (i : pmodule_type) =
    let tymod = EcTypedtree.transtymod scope.sc_env i in
      transform scope
        (fun ctxt -> Context.bind name tymod ctxt)
        (fun env  -> EcEnv.ModTy.bind (EcIdent.create name) tymod env)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  exception TopScope

  let theory_of_history =
    let theory_item_of_action = function
      | Ac_type      (x, tydecl) -> Th_type      (x, tydecl)
      | Ac_operator  (x, op)     -> Th_operator  (x, op)
      | Ac_axiom     (x,ax)      -> Th_axiom     (x,ax)
      | Ac_modtype   (x, tymod)  -> Th_modtype   (x, tymod)
      | Ac_module    m           -> Th_module    m
      | Ac_theory    (x, th)     -> Th_theory    (x, th)
    in
      fun history -> List.map theory_item_of_action history

  let enter (scope : scope) (name : symbol) =
    subscope (Some scope) name

  let exit (scope : scope) =
    match scope.sc_top with
    | None     -> raise TopScope
    | Some sup ->
      let theory = theory_of_history scope.sc_history in
        (scope.sc_name, bind sup (Ac_theory (scope.sc_name, theory)))

  let import (scope : scope) (name : qsymbol) =
    { scope with
        sc_env = EcEnv.Theory.import name scope.sc_env }
end

(* -------------------------------------------------------------------- *)
let initial (name : symbol) =
  let scope = subscope None name in

  let scope = Ty.alias scope "unit" (EcTypes.tunit ()) in
  let scope = Ty.alias scope "bool" (EcTypes.tbool ()) in
  let scope = Ty.alias scope "int"  (EcTypes.tint  ()) in

    scope
