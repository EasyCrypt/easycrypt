(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcTypes
open EcPath
open EcCoreFol

module Sid = EcIdent.Sid
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
include EcCoreModules

(* -------------------------------------------------------------------- *)
(* Instantiation of EcCoreModules.PreOI on EcCoreFol.form. *)
module OI : sig
  type t = form PreOI.t

  val hash : t -> int
  val equal : t -> t -> bool
  val subst : (xpath -> xpath) -> t -> t

  val empty : t

  val is_in : t -> bool

  val cost : t -> xpath -> form option
  val cost_self : t -> form option

  val allowed : t -> xpath list
  val allowed_s : t -> Sx.t

  val mk :
    xpath list ->
    bool ->
    EcCoreFol.form Mx.t ->
    EcCoreFol.form option ->
    t
  val filter : (xpath -> bool) -> t -> t
end = struct
  type t = EcCoreFol.form PreOI.t

  let empty = PreOI.empty
  let is_in = PreOI.is_in

  let allowed = PreOI.allowed

  let allowed_s = PreOI.allowed_s

  let cost = PreOI.cost
  let cost_self = PreOI.cost_self

  let mk = PreOI.mk

  let filter = PreOI.filter
  let subst = PreOI.subst EcCoreFol.Fsubst.f_subst

  let equal = PreOI.equal EcCoreFol.f_equal

  let hash = PreOI.hash EcCoreFol.f_hash
end

(* -------------------------------------------------------------------- *)
type module_type       = EcCoreFol.module_type
type mod_restr         = form pre_mod_restr
type module_sig        = form pre_module_sig
type module_smpl_sig   = form pre_module_smpl_sig
type function_body     = form pre_function_body
type function_         = form pre_function_
type module_expr       = form pre_module_expr
type module_body       = form pre_module_body
type module_structure  = form pre_module_structure
type module_item       = form pre_module_item
type module_comps      = form pre_module_comps
type module_comps_item = form pre_module_comps_item

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

let add_oinfo restr f ocalls oin = change_oinfo restr f (OI.mk ocalls oin)

let change_oicalls restr f ocalls =
  let oi_in = match Msym.find f restr.mr_oinfos with
    | oi -> OI.is_in oi
    | exception Not_found -> true in
  add_oinfo restr f ocalls oi_in

let oicalls_filter restr f filter =
  match Msym.find f restr.mr_oinfos with
  | oi -> change_oinfo restr f (OI.filter filter oi)
  | exception Not_found -> restr

(* -------------------------------------------------------------------- *)
let sig_smpl_sig_coincide msig smpl_sig =
  let eqparams =
    List.for_all2 EcIdent.id_equal
      (List.map fst msig.mis_params)
      (List.map fst smpl_sig.miss_params) in

  let ls =
    List.map (fun (Tys_function fs) -> fs.fs_name, fs ) msig.mis_body
    |> EcSymbols.Msym.of_list
  and ls_smpl =
    List.map (fun (Tys_function fs) -> fs.fs_name, fs ) smpl_sig.miss_body
    |> EcSymbols.Msym.of_list in
  let eqsig =
    Msym.fold2_union (fun _ aopt bopt eqsig -> match aopt, bopt with
        | Some fs1, Some fs2 -> (fs_equal fs1 fs2) && eqsig
        | _ -> false)  ls_smpl ls true; in

  eqparams && eqsig

(* -------------------------------------------------------------------- *)
let get_uninit_read_of_fun (fp : xpath) (f : function_) =
  match f.f_def with
  | FBalias _ | FBabs _ -> Sx.empty

  | FBdef fd ->
      let w =
        let toloc { v_name = x } = (EcTypes.pv_loc fp x).pv_name in
        let w = List.map toloc (f.f_sig.fs_anames |> odfl []) in
        Sx.of_list (List.map xastrip w)
      in

      let w, r  = s_get_uninit_read w fd.f_body in
      let raout = fd.f_ret |> omap (Uninit.e_pv is_loc) in
      let raout = Sx.diff (raout |> odfl Sx.empty) w in
      Sx.union r raout

(* -------------------------------------------------------------------- *)
let get_uninit_read_of_module (p : path) (me : module_expr) =
  let rec doit_me acc (mp, me) =
    match me.me_body with
    | ME_Alias     _  -> acc
    | ME_Decl      _  -> acc
    | ME_Structure mb -> doit_mb acc (mp, mb)

  and doit_mb acc (mp, mb) =
    List.fold_left
      (fun acc item -> doit_mb1 acc (mp, item))
      acc mb.ms_body

  and doit_mb1 acc (mp, item) =
    match item with
    | MI_Module subme ->
        doit_me acc (EcPath.mqname mp subme.me_name, subme)

    | MI_Variable _ ->
        acc

    | MI_Function f ->
        let xp = xpath_fun mp f.f_name in
        let r  = get_uninit_read_of_fun xp f in
        if Sx.is_empty r then acc else (xp, r) :: acc

  in

  let mp =
    let margs =
      List.map
        (fun (x, _) -> EcPath.mpath_abs x [])
        me.me_params
    in EcPath.mpath_crt (EcPath.pqname p me.me_name) margs None

  in List.rev (doit_me [] (mp, me))

(* -------------------------------------------------------------------- *)
let mty_subst = EcCoreFol.Fsubst mty_subst
let mty_hash = EcCoreFol.mty_hash
let mty_equal = EcCoreFol.mty_equal
