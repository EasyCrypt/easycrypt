(* -------------------------------------------------------------------- *)
open Symbols
open Types

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
type modifier = [ `Use | `Read | `Write ]

type module_expr = {
  me_name      : symbol;
  me_body      : module_body;
  me_interface : interface_sig;
}

and module_body =
  | ME_Ident       of Path.path
  | ME_Application of Path.path * Path.path list
  | ME_Structure   of module_structure
  | ME_Decl        of module_decl

and module_structure = {
  ms_params : (symbol * interface_body);
  ms_body   : module_item list;
}

and module_item = [
  | `Variable of variable
  | `Function of function_
]

and module_decl = {
  md_iname     : Path.path;
  md_interface : interface_sig;
}

and interface_expr = {
  ie_name : symbol;
  ie_body : interface_body;
}

and interface_body = interface_sig

and interface_sig = {
  is_body : interface_item list;
}

and interface_item = [
  | `VariableDecl of variable_decl
  | `FunctionDecl of function_decl
]

and function_ = {
  f_sig  : function_decl;
  f_body : unit;                        (* FIXME *)
}

and function_decl = {
  fd_name      : symbol;
  fd_params    : (symbol * Types.ty) list;
  fd_locals    : (symbol * Types.ty) list;
  fd_modifiers : (Path.path * modifier) list
}

and variable = {
  v_name : symbol;
  v_type : Types.ty;
  v_init : tyexpr;
}

and variable_decl = {
  vd_name : symbol;
  vd_type : Types.ty;
}

type operator = {
  op_name     : symbol;
  op_typarams : int;
  op_sig      : Types.ty list * Types.ty;
}

type axiom = {
  ax_name : symbol;
  ax_spec : unit;                       (* formula *)
}

(* -------------------------------------------------------------------- *)
type pretheory = pretheory_item list

and premodule = {
  pm_name : symbol;
  pm_args : (symbol * interface_body) list;
  pm_body : premodule_item list;
}

and preinterface = {
  pi_name : symbol;
  pi_body : preinterface_item list;
}

and pretheory_item = [
  | `Operator   of operator
  | `Axiom      of axiom
  | `Interface  of interface_expr
  | `Module     of module_expr
  | `ModuleDecl of module_decl
]

and premodule_item = [
  | `Module   of module_expr
  | `Variable of variable
  | `Function of function_
]

and preinterface_item = [
  | `FunctionDecl of function_decl
  | `VariableDecl of variable_decl
]

type preobj = [
  | `Operator     of operator
  | `Axiom        of axiom
  | `Interface    of interface_expr
  | `Module       of module_expr
  | `ModuleDecl   of module_decl
  | `FunctionDecl of function_decl
  | `VariableDecl of variable_decl
]

type scope = {
  sc_scope : pretheory;
  sc_focus : Path.path;
}

(* -------------------------------------------------------------------- *)
let resolve (scope : scope) (path: qsymbol) = None

module Op = struct
  type op = {
    op_path : Path.path;
    op_sig  : Types.ty list * Types.ty;
  }

  let resolve (scope : scope) (path : qsymbol) (sg : Types.ty list) =
    None
end

module Ty = struct
  let resolve (scope : scope) (path : qsymbol) = None
end
