(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcMaps

(* -------------------------------------------------------------------- *)
type ident = {
  id_symb : symbol;
  id_tag  : int;
}

type idents = ident list

(* -------------------------------------------------------------------- *)
let name x = x.id_symb
let tag  x = x.id_tag

(* -------------------------------------------------------------------- *)
let id_equal : ident -> ident -> bool = (==)
let id_compare i1 i2 = i2.id_tag - i1.id_tag
let id_hash id = id.id_tag

(* -------------------------------------------------------------------- *)
module Collection = MakeMSH(struct
  type t   = ident
  let  tag = fun (x : ident) -> x.id_tag
end)

module Sid = Collection.S
module Mid = Collection.M
module Hid = Collection.H

(* -------------------------------------------------------------------- *)
let fv_singleton x = Mid.singleton x 1
let fv_union m1 m2 = Mid.union (fun _ m n -> Some (m+n)) m1 m2
let fv_diff m1 m2  = Mid.diff (fun _ _ _ -> None) m1 m2
let fv_add x m     = Mid.change (fun x -> Some ((odfl 0 x) + 1)) x m

(* -------------------------------------------------------------------- *)
type t = ident

let create (x : symbol) =
  { id_symb = x;
    id_tag  = EcUid.unique () }

let fresh (id : t) = create (name id)

let tostring (id : t) =
  Printf.sprintf "%s/%d" id.id_symb id.id_tag

(* -------------------------------------------------------------------- *)
let pp_ident fmt id = Format.fprintf fmt "%s" (name id)
