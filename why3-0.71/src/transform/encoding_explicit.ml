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

(** transformation from polymorphic logic to untyped logic. The polymorphic
logic must not have finite support types. *)


open Util
open Ident
open Ty
open Term
open Decl
open Task
open Libencoding

(** module with printing functions *)
module Debug = struct
  let print_mtv vprinter fmter m =
    Mtv.iter (fun key value -> Format.fprintf fmter "@[%a@] -> @[%a@]@."
      Pretty.print_tv key vprinter value) m

  (** utility to print a list of items *)
  let rec print_list printer fmter = function
    | [] -> Format.fprintf fmter ""
    | e::es ->
      if es = [] then
        Format.fprintf fmter "@[%a@] %a" printer e (print_list printer) es
      else
        Format.fprintf fmter "@[%a@], %a" printer e (print_list printer) es

  let debug x = Format.eprintf "%s@." x
end

(** {2 module to separate utilities from important functions} *)

module Transform = struct

  (** creates a new logic symbol, with a different type if the
  given symbol was polymorphic *)
  let findL = Wls.memoize 63 (fun lsymbol ->
    if ls_equal lsymbol ps_equ then lsymbol else
    let new_ty = ls_ty_freevars lsymbol in
    (* as many t as type vars *)
    if Stv.is_empty new_ty then lsymbol (* same type *) else
      let add _ acc = ty_type :: acc in
      let args = Stv.fold add new_ty lsymbol.ls_args in
      (* creates a new lsymbol with the same name but a different type *)
      Term.create_lsymbol (id_clone lsymbol.ls_name) args lsymbol.ls_value)

  (** {1 transformations} *)

  (** translation of terms *)
  let rec term_transform varM t = match t.t_node with
      (* first case : predicate (not =), we must translate it and its args *)
    | Tapp(f, terms) when not (ls_equal f ps_equ) ->
      let terms = args_transform varM f terms t.t_ty in
      t_app (findL f) terms t.t_ty
    | _ -> (* default case : traverse *)
      t_map (term_transform varM) t

  and args_transform varM ls args ty =
    (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
    let tv_to_ty = ls_app_inst ls args ty in
    (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
    let args = List.map (term_transform varM) args in
    (* fresh args to be added at the beginning of the list of arguments *)
    let add _ ty acc = term_of_ty varM ty :: acc in
    Mtv.fold add tv_to_ty args

  (** transforms a list of logic declarations into another.
  Declares new lsymbols with explicit polymorphic signatures. *)
  let logic_transform decls =
    (* if there is a definition, we must take it into account *)
    let helper = function
    | (lsymbol, Some ldef) ->
      let new_lsymbol = findL lsymbol in (* new lsymbol *)
      let vars,expr,close = open_ls_defn_cb ldef in
      let add v (vl,vm) =
        let vs = Term.create_vsymbol (id_fresh "t") ty_type in
        vs :: vl, Mtv.add v (t_var vs) vm
      in
      let vars,varM = Stv.fold add (ls_ty_freevars lsymbol) (vars,Mtv.empty) in
      let t = term_transform varM expr in
      close new_lsymbol vars t
    | (lsymbol, None) ->
      (findL lsymbol, None)
    in
    [Decl.create_logic_decl (List.map helper decls)]

  (** transform an inductive declaration *)
  let ind_transform idl =
    let iconv (pr,f) = pr, Libencoding.t_type_close term_transform f in
    let conv (ls,il) = findL ls, List.map iconv il in
    [Decl.create_ind_decl (List.map conv idl)]

  (** transforms a proposition into another (mostly a substitution) *)
  let prop_transform (prop_kind, prop_name, f) =
    let quantified_fmla = Libencoding.t_type_close term_transform f in
    [Decl.create_prop_decl prop_kind prop_name quantified_fmla]

end

(** {2 main part} *)

let decl d = match d.d_node with
  | Dtype tdl -> d :: Libencoding.lsdecl_of_tydecl tdl
  | Dlogic ldl -> Transform.logic_transform ldl
  | Dind idl -> Transform.ind_transform idl
  | Dprop prop -> Transform.prop_transform prop

let explicit = Trans.decl decl (Task.add_decl None d_ts_type)

let explicit =
  Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
  Trans.on_tagged_ts Eliminate_algebraic.meta_enum (fun enum ->
    let check ts = not (ts.ts_args = [] && Sty.mem (ty_app ts []) kept) in
    let enum = Sts.filter check enum in
    if Sts.is_empty enum then explicit
    else
      let ts = Sts.choose enum in
      let ty = ty_app ts (List.map ty_var ts.ts_args) in
      Printer.unsupportedType ty
      "Encoding_explicit is unsound in presence of unprotected finite types"))


(** {2 monomorphise task } *)

open Libencoding

let lsmap kept = Wls.memoize 63 (fun ls ->
  let prot_arg = is_protecting_id ls.ls_name in
  let prot_val = is_protected_id ls.ls_name in
  let neg ty = if prot_arg && Sty.mem ty kept then ty else ty_base in
  let pos ty = if prot_val && Sty.mem ty kept then ty else ty_base in
  let ty_arg = List.map neg ls.ls_args in
  let ty_res = Util.option_map pos ls.ls_value in
  if Util.option_eq ty_equal ty_res ls.ls_value &&
     List.for_all2 ty_equal ty_arg ls.ls_args then ls
  else create_lsymbol (id_clone ls.ls_name) ty_arg ty_res)

let d_ts_base = create_ty_decl [ts_base, Tabstract]

let monomorph = Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
  let kept = Sty.add ty_type kept in
  let decl = d_monomorph kept (lsmap kept) in
  Trans.decl decl (Task.add_decl None d_ts_base))

let () = Hashtbl.replace Encoding.ft_enco_poly "explicit"
    (fun _ -> Trans.compose explicit monomorph)
