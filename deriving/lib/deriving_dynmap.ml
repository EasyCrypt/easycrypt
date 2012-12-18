(* Finite maps : t -> dynamic *)

(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)
open Deriving_Typeable
open Deriving_Eq

module Comp (T : Typeable) (E : Eq with type a = T.a) =
struct
  type a = T.a
  let adjust_comparator : (T.a -> T.a -> bool) -> dynamic -> dynamic -> bool 
    = fun comparator d1 d2 ->
      match T.cast d1, T.cast d2 with
        | Some l, Some r -> comparator l r
        | _ -> assert false
  let eq = adjust_comparator E.eq
end


module DynMap =
struct
  module TypeMap = Map.Make(TypeRep)
  type comparator = dynamic -> dynamic -> bool
  type 'value t = (((dynamic * 'value) list * comparator) TypeMap.t)

  let empty = TypeMap.empty

  let add dynamic value comparator map =
    let typeRep = tagOf dynamic in
    let monomap = 
      try (List.filter
             (fun (k,_) -> not (comparator k dynamic))
             (fst (TypeMap.find typeRep map)))
      with Not_found -> []
    in
      TypeMap.add
        typeRep 
        (((dynamic,value)::monomap), comparator)
        map

  let mem dynamic map =
    try let monomap, comparator = TypeMap.find (tagOf dynamic) map in
      (List.exists 
         (fun (k,_) -> (comparator dynamic k)) 
         monomap)
    with Not_found -> false

  let find dynamic map =
    try 
      let monomap, comparator = TypeMap.find (tagOf dynamic) map in
        Some (snd (List.find
                     (fun (k,_) -> comparator dynamic k)
                     monomap))
    with Not_found -> None

  let iter : (dynamic -> 'a -> unit) -> 'a t -> unit
    = fun f -> 
      TypeMap.iter 
        (fun _ (monomap,_) -> List.iter (fun (k, v) -> f k v) monomap)
end
