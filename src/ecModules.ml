(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcAst

module Sid = EcIdent.Sid
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
include EcCoreModules

(* -------------------------------------------------------------------- *)
(* Instantiation of EcCoreModules.PreOI on EcCoreFol.form. *)
module OI = struct
  include PreOI
  let equal = PreOI.equal f_equal
end

(* -------------------------------------------------------------------- *)

let mr_empty = {
  mr_xpaths = ur_empty EcPath.Sx.empty;
  mr_mpaths = ur_empty EcPath.Sm.empty;
  mr_oinfos = Msym.empty;
}

let mr_full = {
  mr_xpaths = ur_full EcPath.Sx.empty;
  mr_mpaths = ur_full EcPath.Sm.empty;
  mr_oinfos = Msym.empty;
}

let mr_add_restr mr (rx : Sx.t use_restr) (rm : Sm.t use_restr) =
  { mr_xpaths = ur_union Sx.union Sx.inter mr.mr_xpaths rx;
    mr_mpaths = ur_union Sm.union Sm.inter mr.mr_mpaths rm;
    mr_oinfos = mr.mr_oinfos; }

let change_oinfo restr f oi =
  { restr with mr_oinfos = Msym.add f oi restr.mr_oinfos }

let add_oinfo restr f oi = change_oinfo restr f oi

let oicalls_filter restr f filter =
  match Msym.find f restr.mr_oinfos with
  | oi -> change_oinfo restr f (OI.filter filter oi)
  | exception Not_found -> restr

let change_oicalls restr f ocalls =
  let oi = match Msym.find f restr.mr_oinfos with
    | oi ->
      let filter x = List.mem x ocalls in
      OI.filter filter oi
    | exception Not_found -> OI.mk ocalls `Unbounded in
  add_oinfo restr f oi

(* -------------------------------------------------------------------- *)
let mty_hash  = EcCoreFol.mty_hash
let mty_equal = EcCoreFol.mty_equal

let mr_equal  = EcCoreFol.mr_equal
let mr_hash   = EcCoreFol.mr_hash
