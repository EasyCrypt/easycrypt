(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

(* -------------------------------------------------------------------- *)
type memenv = {
  me_memory : memory;
  me_vars   : EcTypes.ty Msym.t;
}

let mem_equal = EcIdent.id_equal

(* -------------------------------------------------------------------- *)
let memory   { me_memory = m } = m
let bindings { me_vars   = m } = m

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let empty (me : memory) =
  { me_memory = me;
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



(* remove this *)
let dummy_memenv = let mem_id = EcIdent.create "$std" in
                   { me_memory = mem_id;
                     me_vars   = Msym.empty; }


