(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

let mem_equal = EcIdent.id_equal

(* -------------------------------------------------------------------- *)
type memenv = {
  me_memory : memory;
  me_path   : EcPath.mpath;
  me_vars   : EcTypes.ty Msym.t;
}

let me_equal me1 me2 = 
  EcIdent.id_equal me1.me_memory me2.me_memory &&
    EcPath.m_equal me1.me_path me2.me_path &&
    Msym.equal ty_equal me1.me_vars me2.me_vars

(* -------------------------------------------------------------------- *)
let memory   { me_memory = m } = m
let mpath    { me_path   = m } = m
let bindings { me_vars   = m } = m

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let empty (me : memory) mp =
  { me_memory = me;
    me_path   = mp;
    me_vars   = Msym.empty; }

(* -------------------------------------------------------------------- *)
let bind (x : symbol) (ty : EcTypes.ty) (me : memenv) =
  let merger = function
    | Some _ -> raise (DuplicatedMemoryBinding x)
    | None   -> Some ty
  in
    { me with me_vars = Msym.change merger x me.me_vars }

(* -------------------------------------------------------------------- *)
let lookup (x : symbol) (me : memenv) =
  Msym.find_opt x me.me_vars

(* -------------------------------------------------------------------- *)
let me_subst sp smp sm st me =
  let m = EcIdent.Mid.find_def me.me_memory me.me_memory sm in
  let p = EcPath.m_subst sp smp me.me_path in
  let vars = 
    if st == identity then me.me_vars else
      Msym.map st me.me_vars in
  if m == me.me_memory && p == me.me_path && vars == me.me_vars then me else
    { me_memory = m;
      me_path   = p;
      me_vars   = vars }



