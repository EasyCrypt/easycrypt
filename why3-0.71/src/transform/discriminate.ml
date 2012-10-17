(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task

let meta_inst   = register_meta "encoding : inst"   [MTty]
let meta_lskept = register_meta "encoding : lskept" [MTlsymbol]
let meta_lsinst = register_meta "encoding : lsinst" [MTlsymbol;MTlsymbol]

let meta_select_inst   = register_meta_excl "select_inst"   [MTstring]
let meta_select_lskept = register_meta_excl "select_lskept" [MTstring]
let meta_select_lsinst = register_meta_excl "select_lsinst" [MTstring]

module OHTy = OrderedHash(struct
  type t = ty
  let tag = ty_hash
end)

module OHTyl = OrderedHashList(struct
  type t = ty
  let tag = ty_hash
end)

module Mtyl = Stdlib.Map.Make(OHTyl)

module Lsmap = struct

(* TODO : transmettre les tags des logiques polymorphe vers les logiques
   instantié. Un tag sur un logique polymorphe doit être un tag sur toute
   la famille de fonctions *)

  type t = lsymbol Mtyl.t Mls.t

  let empty = Mls.empty

  let add ls tyl tyv lsmap =
    if ls_equal ls ps_equ then lsmap else
    if not (List.for_all Ty.ty_closed (oty_cons tyl tyv)) then lsmap else
    let newls = function
      | None -> Some (create_lsymbol (id_clone ls.ls_name) tyl tyv)
      | nls  -> nls
    in
    let insts = Mls.find_default ls Mtyl.empty lsmap in
    Mls.add ls (Mtyl.change (oty_cons tyl tyv) newls insts) lsmap

  let print_env fmt menv =
    Format.fprintf fmt "defined_lsymbol (%a)@."
      (Pp.print_iter2 Mls.iter Pp.semi Pp.comma Pretty.print_ls
         (Pp.print_iter2 Mtyl.iter Pp.semi Pp.arrow
            (Pp.print_list Pp.space Pretty.print_ty)
            Pretty.print_ls)) menv

  (** From/To metas *)
  let metas lsmap =
    let fold_inst ls _ lsinst decls =
      create_meta meta_lsinst [MAls ls; MAls lsinst] :: decls in
    let fold_ls ls insts decls = Mtyl.fold (fold_inst ls) insts decls in
    Mls.fold fold_ls lsmap []

  let of_metas metas =
    let fold env args =
      match args with
        | [MAls ls; MAls lsinst] ->
          let tydisl = oty_cons lsinst.ls_args lsinst.ls_value in
          if not (List.for_all Ty.ty_closed tydisl) then env else
          let insts = Mls.find_default ls Mtyl.empty env in
          Mls.add ls (Mtyl.add tydisl lsinst insts) env
        | _ -> assert false
    in
    List.fold_left fold Mls.empty metas

end

let find_logic env ls tyl tyv =
  if ls_equal ls ps_equ then ls else
  try Mtyl.find (oty_cons tyl tyv) (Mls.find ls env)
  with Not_found -> ls

module Ssubst =
  Set.Make(struct type t = ty Mtv.t
                  let compare = Mtv.compare OHTy.compare end)

(* find all the possible instantiation which can create a kept instantiation *)
let ty_quant env t =
  let rec add_vs acc0 ls tyl tyv =
    if ls_equal ls ps_equ then acc0 else
      try
        let insts = Mls.find ls env in
        let tyl = oty_cons tyl tyv in
        let fold_inst inst _ acc =
          let fold_subst subst acc =
            try
              let subst = List.fold_left2 ty_match subst tyl inst  in
              Ssubst.add subst acc
            with TypeMismatch _ -> acc
          in
          (* fold on acc0 *)
          Ssubst.fold fold_subst acc0 acc
        in
        Mtyl.fold fold_inst insts acc0
      with Not_found (* no such p *) -> acc0
  in
  t_app_fold add_vs (Ssubst.singleton (Mtv.empty)) t

let ts_of_ls env ls decls =
  if ls_equal ls ps_equ then decls else
  let add_ts sts ts = Sts.add ts sts in
  let add_ty sts ty = ty_s_fold add_ts sts ty in
  let add_tyl tyl _ sts = List.fold_left add_ty sts tyl in
  let insts = Mls.find_default ls Mtyl.empty env in
  let sts = Mtyl.fold add_tyl insts Sts.empty in
  let add_ts ts dl = create_ty_decl [ts,Tabstract] :: dl in
  Sts.fold add_ts sts decls

(* The Core of the transformation *)
let map env d = match d.d_node with
  | Dtype [_,Tabstract] -> [d]
  | Dtype _ -> Printer.unsupportedDecl d
      "Algebraic and recursively-defined types are \
            not supported, run eliminate_algebraic"
  | Dlogic [ls, None] ->
      let lls = Mtyl.values (Mls.find_default ls Mtyl.empty env) in
      let lds = List.map (fun ls -> create_logic_decl [ls,None]) lls in
      ts_of_ls env ls (d::lds)
  | Dlogic [ls, Some ld] when not (Sid.mem ls.ls_name d.d_syms) ->
      let f = ls_defn_axiom ld in
      let substs = ty_quant env f in
      let conv_f tvar (defns,axioms) =
        let f = t_ty_subst tvar Mvs.empty f in
        let f = t_app_map (find_logic env) f in
        match ls_defn_of_axiom f with
          | Some ld ->
              create_logic_decl [ld] :: defns, axioms
          | None ->
              let nm = ls.ls_name.id_string ^ "_inst" in
              let pr = create_prsymbol (id_derive nm ls.ls_name) in
              defns, create_prop_decl Paxiom pr f :: axioms
      in
      let defns,axioms = Ssubst.fold conv_f substs ([],[]) in
      ts_of_ls env ls (List.rev_append defns axioms)
  | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively-defined symbols are not supported, run eliminate_recursion"
  | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
  | Dprop (k,pr,f) ->
      let substs = ty_quant env f in
      let substs_len = Ssubst.cardinal substs in
      let conv_f tvar task =
        (* Format.eprintf "f0 : %a@. env : %a@." Pretty.print_fmla *)
        (*   (t_ty_subst tvar Mvs.empty f) *)
        (*   print_env env; *)
        let f = t_ty_subst tvar Mvs.empty f in
        let f = t_app_map (find_logic env) f in
        (* Format.eprintf "f : %a@. env : %a@." Pretty.print_fmla f *)
        (*   print_env menv; *)
        let pr =
          if substs_len = 1 then pr
          else create_prsymbol (id_clone pr.pr_name) in
        (* Format.eprintf "undef ls : %a, ts : %a@." *)
        (*   (Pp.print_iter1 Sls.iter Pp.comma Pretty.print_ls) *)
        (*   menv.undef_lsymbol *)
        (*   (Pp.print_iter1 Sts.iter Pp.comma Pretty.print_ts) *)
        (*   menv.undef_tsymbol; *)
        create_prop_decl k pr f :: task
      in
      let task = Ssubst.fold conv_f substs [] in
      task


let ft_select_inst =
  ((Hashtbl.create 17) : (Env.env,Sty.t) Trans.flag_trans)

let ft_select_lskept =
  ((Hashtbl.create 17) : (Env.env,Sls.t) Trans.flag_trans)

let ft_select_lsinst =
  ((Hashtbl.create 17) : (Env.env,Lsmap.t) Trans.flag_trans)

let metas_from_env env =
  let fold_inst tyl _ s = List.fold_left (fun s ty -> Sty.add ty s) s tyl in
  let fold_ls _ insts s = Mtyl.fold fold_inst insts s in
  let sty = Mls.fold fold_ls env Sty.empty in
  let add ty decls = create_meta Libencoding.meta_kept [MAty ty] :: decls in
  Sty.fold add sty (Lsmap.metas env)

let lsinst_completion kept lskept env =
  let fold_ls ls env =
    let rec aux env tydisl subst = function
      | [] ->
          let tydisl = List.rev tydisl in
          let tyl,tyv = match tydisl, ls.ls_value with
            | tyv::tyl, Some _ -> tyl, Some tyv
            | tyl, None -> tyl, None
            | _ -> assert false in
          Lsmap.add ls tyl tyv env
      | ty::tyl ->
          let fold_ty tykept env =
            try
              let subst = ty_match subst ty tykept in
              aux env (tykept::tydisl) subst tyl
            with TypeMismatch _ -> env
          in
          Sty.fold fold_ty kept env
    in
    aux env [] Mtv.empty (oty_cons ls.ls_args ls.ls_value)
  in
  Sls.fold fold_ls lskept env

let add_user_lsinst env = function
  | [MAls ls; MAls nls] -> Lsmap.add ls nls.ls_args nls.ls_value env
  | _ -> assert false

let clear_metas = Trans.fold (fun hd task ->
  match hd.task_decl.td_node with
    | Meta (m,_) when meta_equal m meta_lsinst -> task
    | _ -> add_tdecl task hd.task_decl) None

let select_lsinst env =
  let inst   = Trans.on_flag meta_select_inst   ft_select_inst   "none" env in
  let lskept = Trans.on_flag meta_select_lskept ft_select_lskept "none" env in
  let lsinst = Trans.on_flag meta_select_lsinst ft_select_lsinst "none" env in
  let trans task =
    let inst   = Trans.apply inst   task in
    let lskept = Trans.apply lskept task in
    let lsinst = Trans.apply lsinst task in
    let inst   = Sty.union inst   (Task.on_tagged_ty meta_inst   task) in
    let lskept = Sls.union lskept (Task.on_tagged_ls meta_lskept task) in
    let lsinst = Task.on_meta meta_lsinst add_user_lsinst lsinst task in
    let lsinst = lsinst_completion inst lskept lsinst in
    let task   = Trans.apply clear_metas task in
    Trans.apply (Trans.add_tdecls (metas_from_env lsinst)) task
  in
  Trans.store trans

let lsymbol_distinction =
  Trans.on_meta meta_lsinst (fun metas ->
    if metas = [] then Trans.identity
    else
      let env = Lsmap.of_metas metas in
      (* Format.eprintf "instantiate %a@." print_env env; *)
      Trans.decl (map env) None)

let discriminate env = Trans.seq [
  Libencoding.monomorphise_goal;
  select_lsinst env;
  Trans.print_meta Libencoding.debug meta_lsinst;
  lsymbol_distinction;
]

let () = Trans.register_env_transform "discriminate" discriminate

