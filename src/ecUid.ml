(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
let unique () = Oo.id (object end)

(* -------------------------------------------------------------------- *)
type uid = int

type uidmap = {
  (*---*) um_tbl : (symbol, uid) Hashtbl.t;
  mutable um_uid : int;
}

let create () =
  { um_tbl = Hashtbl.create 0;
    um_uid = 0; }

let lookup (um : uidmap) (x : symbol) =
  try  Some (Hashtbl.find um.um_tbl x)
  with Not_found -> None

let forsym (um : uidmap) (x : symbol) =
  match lookup um x with
    | Some uid -> uid
    | None ->
      let uid = um.um_uid in
        um.um_uid <- um.um_uid + 1;
        Hashtbl.add um.um_tbl x uid;
        uid

(* -------------------------------------------------------------------- *)
let uid_equal x y = x == y
let uid_compare x y = x - y

module Muid = Mint
module Suid = Set.MakeOfMap(Muid)

(* -------------------------------------------------------------------- *)
module NameGen = struct
  type t = {
    (*---*) ng_counter : Counter.t;
    mutable ng_map     : string Muid.t;
  }

  let names = "abcdefghijklmnopqrstuvwxyz"

  let ofint (i : int) =
    let rec ofint i acc =
      let acc =
        Printf.sprintf "%s%c" acc names.[i mod (String.length names)]
      in
        if   i >= String.length names
        then ofint (i / (String.length names)) acc
        else acc
    in
      if i < 0 then
        invalid_arg "EcUid.ofint [i < 0]";
      ofint i ""

  let create () = {
    ng_counter = Counter.create ();
    ng_map     = Muid.empty;
  }

  let get (map : t) (id : uid) =
    try  Muid.find id map.ng_map
    with Not_found ->
      let s = ofint (Counter.next map.ng_counter) in
        map.ng_map <- Muid.add id s map.ng_map;
        s
end
