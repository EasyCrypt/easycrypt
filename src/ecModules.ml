(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
(* open EcDecl *)

(* -------------------------------------------------------------------- *)
module Sp = EcPath.Sp

(* -------------------------------------------------------------------- *)
module UM : sig
  type flag  = [`Call | `Read | `Write]
  type flags

  val empty     : flags
  val singleton : flag -> flags
  val add       : flags -> flag -> flags
  val have      : flags -> flag -> bool
  val equal     : flags -> flags -> bool
  val included  : flags -> flags -> bool
end = struct
  (* TODO: to be rewritten using -pxp OCaml 4.0 feature *)

  type flag  = [`Call | `Read | `Write]
  type flags = UseFlags of int

  let iflag = function 
    | `Call  -> 0
    | `Read  -> 1
    | `Write -> 2

  let empty = UseFlags 0

  let add (UseFlags f : flags) (e : flag) =
    UseFlags (f lor (1 lsl (iflag e)))

  let have (UseFlags f : flags) (e : flag) =
    (f land (1 lsl (iflag e))) != 0

  let singleton (e : flag) =
    add empty e

  let equal (UseFlags fin) (UseFlags fout) =
    fin == fout

  let included (UseFlags fin) (UseFlags fout) =
    (lnot fin) land fout == 0
end

type use_flags = UM.flags

(* -------------------------------------------------------------------- *)
type module_type = EcPath.path 

type module_sig = {
  mt_params : (EcIdent.t * module_type) list;
  mt_body   : module_sig_body;
  mt_mforb  : EcPath.Sp.t;
}

and module_sig_body = module_sig_body_item list

and module_sig_body_item =
  | Tys_variable of (symbol * EcTypes.ty)
  | Tys_function of funsig

and funsig = {
  fs_name : symbol;
  fs_sig  : (symbol * EcTypes.ty) list * EcTypes.ty;
  fs_uses : use_flags EcPath.Mp.t;
}

(* -------------------------------------------------------------------- *)
type module_expr = {
  me_name  : symbol;
  me_body  : module_body;
  me_comps : module_comps;
  me_sig   : module_sig;
  me_uses  : EcPath.Sp.t;
  me_types : module_type list;
}

and module_body =
  | ME_Alias       of EcPath.mpath
  | ME_Structure   of module_structure
  | ME_Decl        of module_type

and module_structure = {
  ms_params : (EcIdent.t * module_type) list;
  ms_body   : module_item list;
}

and module_item =
  | MI_Module   of module_expr
  | MI_Variable of variable
  | MI_Function of function_

and module_comps = module_comps_item list

and module_comps_item = module_item

and function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_def option;
}

and function_def = {
  f_locals : (symbol * EcTypes.ty) list;
  f_body   : stmt;
  f_ret    : EcTypes.tyexpr option;
}

and variable = {
  v_name : symbol;
  v_type : EcTypes.ty;
}

and stmt = instr list

and instr =
  | Sasgn   of lvalue * EcTypes.tyexpr
  | Srnd    of lvalue * EcTypes.tyexpr
  | Scall   of lvalue option * EcPath.mpath * EcTypes.tyexpr list
  | Sif     of EcTypes.tyexpr * stmt * stmt
  | Swhile  of EcTypes.tyexpr * stmt
  | Sassert of EcTypes.tyexpr

and lvalue =
  | LvVar   of (EcTypes.prog_var * EcTypes.ty)
  | LvTuple of (EcTypes.prog_var * EcTypes.ty) list
  | LvMap   of (EcPath.path * EcTypes.ty list) * 
               EcTypes.prog_var * EcTypes.tyexpr * EcTypes.ty
 (* LvMap(op, m, x, ty)
  * - op is the set operator
  * - m  is the map to be updated 
  * - x  is the index to update
  * - ty is the type of the value associated to x
  *)
