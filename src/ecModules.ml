(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcAst

module Sid = EcIdent.Sid
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
include EcCoreModules

(* -------------------------------------------------------------------- *)
module OI = PreOI

(* -------------------------------------------------------------------- *)

let change_oinfo (ois : oracle_infos) (f : symbol) (oi : oracle_info) =
  Msym.add f oi ois

let oicalls_filter (ois : oracle_infos) (f : symbol) (filter : xpath -> bool) =
  match Msym.find f ois with
  | oi -> change_oinfo ois f (OI.filter filter oi)
  | exception Not_found -> ois

let change_oicalls (ois : oracle_infos) (f : symbol) (ocalls : xpath list) =
  let oi =
    match Msym.find f ois with
    | oi -> OI.filter (fun x -> List.mem x ocalls) oi
    | exception Not_found -> OI.mk ocalls
  in change_oinfo ois f oi

(* -------------------------------------------------------------------- *)
let mty_hash  = EcCoreFol.mty_hash
let mty_equal = EcCoreFol.mty_equal

let mr_equal  = EcCoreFol.mr_equal
let mr_hash   = EcCoreFol.mr_hash
