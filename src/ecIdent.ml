(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcMaps

(* -------------------------------------------------------------------- *)
type ident = { 
  id_symb : symbol;
  id_tag  : int;
}

(* -------------------------------------------------------------------- *)
let name x = x.id_symb
let tag  x = x.id_tag

(* -------------------------------------------------------------------- *)
let id_equal : ident -> ident -> bool = (==)
let id_compare i1 i2 = i2.id_tag - i1.id_tag 
let id_hash id = id.id_tag 

(* -------------------------------------------------------------------- *)
module IdComparable = struct
  type t = ident
  let compare = id_compare
end

module Mid = Map.Make(IdComparable)
module Sid = Mid.Set

(* -------------------------------------------------------------------- *)
type t = ident

let create (x : symbol) = 
  { id_symb = x;
    id_tag  = EcUidgen.unique () }

let fresh (id : t) = create (name id)

let tostring (id : t) =
  Printf.sprintf "%s/%d" id.id_symb id.id_tag

(* -------------------------------------------------------------------- *)
let pp_ident fmt id = Format.fprintf fmt "%s" (name id)
