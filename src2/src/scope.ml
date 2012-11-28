(* -------------------------------------------------------------------- *)
open Utils
open Symbols
open Path

(* -------------------------------------------------------------------- *)
module Context = struct
  module SM = Maps.StringMap

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
type scope = {
  sc_name      : string;
  sc_types     : Typesmod.tydecl   Context.context;
  sc_operators : Typesmod.operator Context.context;
  sc_env       : Env.env;
}

(* -------------------------------------------------------------------- *)
let initial (name : symbol) = {
  sc_name      = name;
  sc_types     = Context.empty ();
  sc_operators = Context.empty ();
  sc_env       = Env.empty;
}

(* -------------------------------------------------------------------- *)
let name (scope : scope) =
  scope.sc_name

(* -------------------------------------------------------------------- *)
let env (scope : scope) = scope.sc_env

(* -------------------------------------------------------------------- *)
module Op = struct
  open Parsetree
  open Types
  open Typesmod

  module TT = Typedtree

  type operror =
  | OpE_DuplicatedTypeVariable

  exception OpError of operror

  let operror (error : operror) =
    raise (OpError error)

  let transform (scope : scope) f e =
    { scope with
        sc_operators = f scope.sc_operators;
        sc_env       = e scope.sc_env      ; }

  let add (scope : scope) (op : poperator) =
    if not (List.uniq op.po_tyvars) then
      operror OpE_DuplicatedTypeVariable;

    let policy  = TT.TyDecl op.po_tyvars in
    let transty = TT.transty scope.sc_env policy in

    let dom    = List.map transty (odfl [] op.po_dom) in
    let codom  = transty op.po_codom in

    let tyop = {
      op_sig  = (dom, codom);
      op_ctnt = (op.po_dom = None);
      op_prob = op.po_prob;
    }

    in
      transform scope
        (fun ctxt -> Context.bind op.po_name tyop ctxt)
        (fun env  -> Env.Op.bind (Ident.create op.po_name) tyop env)
end

(* -------------------------------------------------------------------- *)
module Ty = struct
  open Parsetree
  open Types
  open Typesmod

  let transform (scope : scope) f e =
    { scope with
        sc_types = f scope.sc_types;
        sc_env   = e scope.sc_env  ; }

  let add (scope : scope) (name : symbol) =
    let tydecl = {
      tyd_params = 0   ;
      tyd_type   = None;
    } in
      transform scope
        (fun ctxt -> Context.bind name tydecl ctxt)
        (fun env  -> Env.Ty.bind (Ident.create name) tydecl env)
end
