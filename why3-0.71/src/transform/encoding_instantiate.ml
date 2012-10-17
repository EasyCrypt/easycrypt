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

open Stdlib
open Util
open Ident
open Ty
open Term
open Task
open Theory
open Task
open Decl
open Encoding

let meta_complete = register_meta_excl
  "encoding_instantiate : complete" [MTstring]

exception TooMuchInstantiation of int
let max_instantiation = 512 (* 7 ** 3 = 343 *)

let () = Exn_printer.register (fun fmt exn ->
  match exn with
    | TooMuchInstantiation i -> Format.fprintf fmt
      "encoding_instantiate : %i instantiation to create, it is limited to %i"
      i max_instantiation
    | _ -> raise exn)

(* Ce type est utiliser pour indiquer un alpha *)
let tv_dumb = create_tvsymbol (id_fresh "instantiate_alpha")
let ty_dumb = ty_var tv_dumb

(* TODO : transmettre les tags des logiques polymorphe vers les logiques
   instantié. Un tag sur un logique polymorphe doit être un tag sur toute
   la famille de fonctions *)

module OHTyl = OrderedHashList(struct
  type t = ty
  let tag = ty_hash
end)

module Mtyl = Map.Make(OHTyl)
module Htyl = Hashtbl.Make(OHTyl)

type tenv =
  | Complete (* The transformation keep the polymorphism *)
  | Incomplete (* The environnement when the transformation isn't complete*)


(* A type is projected on term or type depending
   of its color (green part,red part, black part) *)
type tty =
  | Tyterm of ty
  | Tyty of ty

let print_tty fmt = function
  | Tyterm ty -> Format.fprintf fmt "(Tyterm %a)" Pretty.print_ty ty
  | Tyty ty -> Format.fprintf fmt "(Tyty %a)" Pretty.print_ty ty

(* It can be backprojected to type, ty_dumb is like a bottom type it
   never appear in final formulas *)
let reduce_to_type = function
  | Tyty ty -> ty
  | Tyterm _ -> ty_dumb


let reduce_to_real = function
  | Tyty ty | Tyterm ty -> ty

(* let reduce_to_pos tenv = function *)
(*   | Tyty ty -> ty *)
(*   | Tyterm _ -> match tenv with  *)
(*       | Incomplete -> assert false (\* All is type in this mode *\) *)
(*       | Tenv tenv -> tenv.undeco *)

(* let reduce_to_neg tenv = function *)
(*   | Tyty ty -> ty *)
(*   | Tyterm _ -> match tenv with  *)
(*       | Incomplete -> assert false (\* All is type in this mode *\) *)
(*       | Tenv tenv -> tenv.deco *)

(* The environnement of the transformation between two decl (* unmutable *) *)
type env = {
  etenv : tenv;
  ekeep : Sty.t;
  prop_toremove : ty Mtv.t Mpr.t;
  eprojty : ty Mty.t;
  edefined_lsymbol : lsymbol Mtyl.t Mls.t;
  edefined_tsymbol : tysymbol Mtyl.t Mts.t;
}

type auto_clone = task -> tenv -> Sty.t -> task * env

(* The environnement of the transformation during
   the transformation of a formula *)
type menv = {
  tenv : tenv;
  keep : Sty.t;
  mutable projty : ty Mty.t;
  mutable defined_lsymbol : lsymbol Mtyl.t Mls.t;
  mutable defined_tsymbol : tysymbol Mtyl.t Mts.t;
  mutable undef_lsymbol : Sls.t;
  mutable undef_tsymbol : Sts.t;
}

let print_env fmt menv =
  Format.fprintf fmt "defined_lsymbol (%a)@."
    (Pp.print_iter2 Mls.iter Pp.semi Pp.comma Pretty.print_ls
       (Pp.print_iter2 Mtyl.iter Pp.semi Pp.arrow
          (Pp.print_list Pp.space Pretty.print_ty)
          Pretty.print_ls)) menv.defined_lsymbol;
  Format.fprintf fmt "defined_tsymbol (%a)@."
    (Pp.print_iter2 Mts.iter Pp.semi Pp.comma Pretty.print_ts
       (Pp.print_iter2 Mtyl.iter Pp.semi Pp.arrow
          (Pp.print_list Pp.space Pretty.print_ty)
          Pretty.print_ts)) menv.defined_tsymbol

type tvar = ty Mtv.t

let rec projty menv tvar ty =
  let rec aux ty =
    match ty.ty_node with
      | Tyvar _ -> Tyterm ty
      | Tyapp (ts,tyl) ->
        try
          Tyty (Mty.find ty menv.projty)
        with Not_found ->
          match menv.tenv with
            | Incomplete ->
              (* In this configuration there is no term representing type,
                 all type are a type or are in the black part
                 (the or is not a xor)*)
              (* let preid = id_clone ts.ts_name in *)
              (* let ts = create_tysymbol preid [] None (\*Some ty*\) in *)
              (* let tty = ty_app ts [] in *)
              let tty = ty in
              menv.projty <- Mty.add ty tty menv.projty;
              menv.undef_tsymbol <- Sts.add ts menv.undef_tsymbol;
              (*Format.eprintf "projty : ts : %a env : %a@." Pretty.print_ts ts
              print_env menv;*)
              Tyty tty
            | Complete ->
              let tyl = List.map aux tyl in
              let tyl_red = List.map reduce_to_type tyl in
              let tys =
                try
                  Mtyl.find tyl_red (Mts.find ts menv.defined_tsymbol)
                with Not_found ->
                  let insts = try Mts.find ts menv.defined_tsymbol
                    with Not_found -> Mtyl.empty in
                  let args = List.fold_left (fun acc e ->
                    match e with
                      | Tyterm _ -> (create_tvsymbol (id_fresh "a"))::acc
                      | Tyty _ -> acc) [] tyl in
                  let tys = if List.length args = List.length ts.ts_args
                    then ts
                    else create_tysymbol (id_clone ts.ts_name) args None in
                  let insts = Mtyl.add tyl_red tys insts in
                  menv.defined_tsymbol <-
                    Mts.add ts insts menv.defined_tsymbol;
                  menv.undef_tsymbol <- Sts.add tys menv.undef_tsymbol;
                  tys in
              let args = List.rev (List.fold_left (fun acc e ->
                match e with
                  | Tyterm ty -> ty::acc
                  | Tyty _ -> acc) [] tyl) in
              Tyterm (ty_app tys args) in
  let ty = ty_inst tvar ty in
  aux ty

let projty_real menv tvar ty = reduce_to_real (projty menv tvar ty)

(* let reduce_to_default menv d = function *)
(*   | Tyty ty -> ty *)
(*   | Tyterm ty -> match menv.tenv with *)
(*       | Incomplete -> ty *)
(*       | Complete -> projty menv Mtv.empty d *)


let reduce_to_default menv tvar d ty =
  match projty menv tvar ty with
    | Tyty _ -> (*keep the term unfolded *) ty_inst tvar ty
    | Tyterm _ -> ty_var d

(* Weakmemo only on the symbols *)
let clone_lsymbol_memo =
  let clone_lsymbol p =
    let h = Htyl.create 7 in
    fun arg result ->
      let key = (option_apply arg (fun r -> r::arg) result) in
      try
        Htyl.find h key
      with Not_found ->
        let p = create_lsymbol (id_clone p.ls_name) arg result in
        Htyl.add h key p;
        p in
  Wls.memoize 7 clone_lsymbol

let find_logic menv tvar p tyl ret =
  if ls_equal p ps_equ then p else begin
    let inst = ls_app_inst p tyl ret in
     (* Format.eprintf "inst : %a@." *)
     (*   (Pp.print_iter2 Mtv.iter Pp.comma Pp.space Pp.nothing *)
     (*      Pretty.print_ty) inst; *)
    let inst = Mtv.mapi (reduce_to_default menv tvar) inst in
    let inst_l = Mtv.fold (fun _ v acc -> v::acc) inst [] in
    (* Format.eprintf "p : %a | arg : %a| tyl = %a | inst_l : %a@." *)
    (*   Pretty.print_ls p *)
    (*   (Pp.print_list Pp.comma Pretty.print_ty) p.ls_args *)
    (*   (Pp.print_list Pp.comma Pretty.print_ty) *)
    (*   (List.map (fun t -> (projty_real menv tvar t.t_ty)) tyl) *)
    (*   (Pp.print_list Pp.comma Pretty.print_ty) inst_l; *)
      try
      let insts = Mls.find p menv.defined_lsymbol in
      Mtyl.find inst_l insts
    with Not_found ->
      let insts =
        try
          Mls.find p menv.defined_lsymbol
        with Not_found ->
          Mtyl.empty in
      (* proj fold the types previously kept unfold in inst *)
      let proj ty = reduce_to_real (projty menv Mtv.empty ty) in
      let arg = List.map (ty_inst inst) p.ls_args in
      let arg = List.map proj arg in
      let result = option_map (ty_inst inst) p.ls_value in
      let result = option_map proj result in
      (* Format.eprintf "arg : %a ; result : %a@." *)
      (*   (Pp.print_list Pp.comma Pretty.print_ty) arg *)
      (*   (Pp.print_option Pretty.print_ty) result; *)
      let ls = if List.for_all2 ty_equal arg p.ls_args &&
          option_eq ty_equal result p.ls_value
        then p else clone_lsymbol_memo p arg result in
      let insts = Mtyl.add inst_l ls insts in
      menv.defined_lsymbol <- Mls.add p insts menv.defined_lsymbol;
      menv.undef_lsymbol <- Sls.add ls menv.undef_lsymbol;
      (* Format.eprintf "fl : env : %a  p : %a | inst : %a@." *)
      (*   print_env menv *)
      (*   Pretty.print_ls p *)
      (*   (Pp.print_list Pp.comma Pretty.print_ty) inst_l; *)
      ls
  end


(* let deco_res menv t ty = *)
(*   match ty with *)
(*     | Tyty _ -> t *)
(*     | Tyterm tyterm -> *)
(*       match menv.tenv with *)
(*         | Incomplete -> assert false *)
(*         | Tenv tenv -> fs_app tenv.sort [tyterm;t] tenv.deco *)

(* let sort_app tenv ty t = *)
(*   match tenv with *)
(*     | Incomplete -> assert false *)
(*     | Tenv tenv -> fs_app tenv.sort [ty;t] tenv.deco    *)


let conv_vs menv tvar vsvar vs =
  let ty = projty_real menv tvar vs.vs_ty in
  let vs' = if ty_equal ty vs.vs_ty then vs else
      create_vsymbol (id_clone vs.vs_name) ty in
  Mvs.add vs (t_var vs') vsvar,vs'

(* The convertion of term and formula *)
let rec rewrite_term menv tvar vsvar t =
  let fnT = rewrite_term menv tvar in
  let fnF = rewrite_fmla menv tvar in
  (* Format.eprintf "@[<hov 2>Term : %a =>@\n@?" Pretty.print_term t; *)
  let t = match t.t_node with
    | Tconst _ -> t
    | Tvar x -> Mvs.find x vsvar
    | Tapp(p,tl) ->
      let tl' = List.map (fnT vsvar) tl in
      let p = find_logic menv tvar p tl t.t_ty in
      fs_app p tl' (projty_real menv tvar (t_type t))
    | Tif(f, t1, t2) ->
      t_if (fnF vsvar f) (fnT vsvar t1) (fnT vsvar t2)
    | Tlet (t1, b) -> let u,t2,cb = t_open_bound_cb b in
      let (vsvar',u) = conv_vs menv tvar vsvar u in
      let t1 = fnT vsvar t1 in let t2 = fnT vsvar' t2 in
      t_let t1 (cb u t2)
    | Tcase _ | Teps _ ->
      Printer.unsupportedTerm t
        "Encoding instantiate : I can't encode this term"
    | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)
  in
  (* Format.eprintf "@[<hov 2>Term : => %a : %a@\n@?" *)
  (*   Pretty.print_term t Pretty.print_ty t.t_ty; *)
  t

and rewrite_fmla menv tvar vsvar f =
  let fnT = rewrite_term menv tvar in
  let fnF = rewrite_fmla menv tvar in
  (* Format.eprintf "@[<hov 2>Fmla : %a =>@\n@?" Pretty.print_fmla f; *)
  match f.t_node with
    | Tapp(p, tl) ->
      let tl' = List.map (fnT vsvar) tl in
      let p = find_logic menv tvar p tl None in
      ps_app p tl'
    | Tquant(q, b) ->
      let vl, tl, f1, cb = t_open_quant_cb b in
      let vsvar,vl = map_fold_left (conv_vs menv tvar) vsvar vl in

      let f1 = fnF vsvar f1 in
      (* Ici un trigger qui ne match pas assez de variables
         peut être généré *)
      let tl = TermTF.tr_map (fnT vsvar) (fnF vsvar) tl in
      t_quant q (cb vl tl f1)
    | Tlet (t1, b) -> let u,f2,cb = t_open_bound_cb b in
      let (vsvar',u) = conv_vs menv tvar vsvar u in
      let t1 = fnT vsvar t1 and f2 = fnF vsvar' f2 in
      (* Format.eprintf "u.vs_ty : %a == t1.t_ty : %a@." *)
      (*    Pretty.print_ty u.vs_ty Pretty.print_ty t1.t_ty; *)
      ty_equal_check u.vs_ty (t_type t1);
      t_let t1 (cb u f2)
    | _ -> TermTF.t_map (fun _ -> assert false) (fnF vsvar) f

(* Generation of all the possible instantiation of a formula *)
let gen_tvar env ts =
  let aux tv tvarl =
    let gen tvar ty = Mtv.add tv ty tvar in
    let tvarl' = List.fold_left (fun acc tvar ->
      Sty.fold (fun ty acc -> gen tvar ty :: acc) env.ekeep acc) [] tvarl in
    match env.etenv with
      | Incomplete -> tvarl'
      | Complete ->
        let gen acc tvar = (Mtv.add tv (ty_var tv) tvar)::acc in
        List.fold_left gen tvarl' tvarl in
  Stv.fold aux ts [Mtv.empty]

(*
let ty_args_from_tty =
  List.fold_left (fun acc e ->
    match e with
      | Tyterm _ -> tenv.ty::acc
      | Tyty _ -> acc) []

let conv_to_tty env ts tyl proj_ty =
  let ty = ty_app ts tyl in
  if Sty.mem ty env.keep
  then (assert (Mty.mem ty proj_ty); proj_ty)
  else let args = ty_args_from_tty tyl in
*)

let ty_quant =
  let rec add_vs s ty = match ty.ty_node with
    | Tyvar vs -> Stv.add vs s
    | _ -> ty_fold add_vs s ty in
  t_ty_fold add_vs Stv.empty

let add_decl_ud menv task =
  let task = Sts.fold
    (fun ts task -> add_ty_decl task [ts,Tabstract])
    menv.undef_tsymbol task in
  let task = Sls.fold
    (fun ls task -> add_logic_decl task [ls,None])
    menv.undef_lsymbol task in
  task


(* The Core of the transformation *)
let fold_map task_hd ((env:env),task) =
  match task_hd.task_decl.td_node with
    | Use _ | Clone _ -> env,add_tdecl task task_hd.task_decl
    | Meta(meta,ml) ->
      begin try
        let menv =  {
          tenv = env.etenv;
          keep = env.ekeep;
          projty = env.eprojty;
          defined_lsymbol = env.edefined_lsymbol;
          defined_tsymbol = env.edefined_tsymbol;
          undef_lsymbol = Sls.empty;
          undef_tsymbol = Sts.empty;
        } in
        let map = function
          | MAty ty -> MAty (projty_real menv Mtv.empty ty)
          (* | MAts {ts_name = name; ts_args = []; ts_def = Some ty} -> *)
          (*   MAts (conv_ts tenv ud name ty) *)
          (* | MAts {ts_args = []; ts_def = None} as x -> x *)
          | MAts _ -> raise Exit
          | MAls _ -> raise Exit
          | MApr _ -> raise Exit
          | MAstr _ as s -> s
          | MAint _ as i -> i in
        let arg = (List.map map ml) in
        let task = add_meta (add_decl_ud menv task) meta arg in
        {env with edefined_lsymbol = menv.defined_lsymbol;
          edefined_tsymbol = menv.defined_tsymbol;
          eprojty = menv.projty;
        }, task
      with
        | Printer.UnsupportedType _
        | Exit -> env,add_tdecl task task_hd.task_decl
      end
    | Decl d -> match d.d_node with
    | Dtype [_,Tabstract] -> (env,task)
    (* Nothing here since the type kept are already defined and the other
       will be lazily defined *)
    | Dtype _ -> Printer.unsupportedDecl
        d "encoding_decorate : I can work only on abstract\
            type which are not in recursive bloc."
    | Dlogic l ->
        let fn = function
          | _, Some _ ->
              Printer.unsupportedDecl
                d "encoding_decorate : I can't encode definition. \
Perhaps you could use eliminate_definition"
          | _, None -> () in
            (* Noting here since the logics are lazily defined *)
            List.iter fn l; (env,task)
    | Dind _ -> Printer.unsupportedDecl
        d "encoding_decorate : I can't work on inductive"
        (* let fn (pr,f) = pr, fnF f in *)
        (* let fn (ps,l) = ps, List.map fn l in *)
        (* [create_ind_decl (List.map fn l)] *)
    | Dprop (k,pr,f) ->
      let tvl = ty_quant f in
      assert (k <> Pgoal || Ty.Stv.is_empty tvl);
      let tvarl = gen_tvar env tvl in
      let tvarl_len = List.length tvarl in
      if tvarl_len > max_instantiation then
        raise (TooMuchInstantiation tvarl_len);
      let menv =  {
        tenv = env.etenv;
        keep = env.ekeep;
        projty = env.eprojty;
        defined_lsymbol = env.edefined_lsymbol;
        defined_tsymbol = env.edefined_tsymbol;
        undef_lsymbol = Sls.empty;
        undef_tsymbol = Sts.empty;
      } in
      let conv_f task tvar =
        if begin
          try (Mtv.equal ty_equal) tvar (Mpr.find pr env.prop_toremove)
          with Not_found -> false end
        then task
        else
        (* Format.eprintf "f0 : %a@. env : %a@." Pretty.print_fmla *)
        (*   (t_ty_subst tvar Mvs.empty f) *)
        (*   print_env menv; *)
        let f = rewrite_fmla menv tvar Mvs.empty f in
        (* Format.eprintf "f : %a@. env : %a@." Pretty.print_fmla f *)
        (*   print_env menv; *)
        let pr =
          if tvarl_len = 1 then pr
          else create_prsymbol (id_clone pr.pr_name) in
        (* Format.eprintf "undef ls : %a, ts : %a@." *)
        (*   (Pp.print_iter1 Sls.iter Pp.comma Pretty.print_ls) *)
        (*   menv.undef_lsymbol *)
        (*   (Pp.print_iter1 Sts.iter Pp.comma Pretty.print_ts) *)
        (*   menv.undef_tsymbol; *)
        let task = add_decl_ud menv task in
        let task = add_prop_decl task k pr f in
        task
      in
      {env with edefined_lsymbol = menv.defined_lsymbol;
        edefined_tsymbol = menv.defined_tsymbol;
        eprojty = menv.projty;
      },
      List.fold_left conv_f task tvarl


let monomorphise_goal =
  Trans.goal (fun pr f ->
    let stv = ty_quant f in
    let mty,ltv = Stv.fold (fun tv (mty,ltv) ->
      let ts = create_tysymbol (id_clone tv.tv_name) [] None in
      Mtv.add tv (ty_app ts []) mty,ts::ltv) stv (Mtv.empty,[]) in
    let f = t_ty_subst mty Mvs.empty f in
    let acc = [create_prop_decl Pgoal pr f] in
    let acc = List.fold_left
      (fun acc ts -> (create_ty_decl [ts,Tabstract]) :: acc)
      acc ltv in
    acc)


(* Some general env creation function *)
let create_env task tenv keep =
  let projty = Sty.fold (fun ty ty_ty ->
    Mty.add ty ty ty_ty)
    keep Mty.empty in
  let task = Sty.fold (fun ty task ->
    let add_ts task ts = add_ty_decl task [ts,Tabstract] in
    let task = ty_s_fold add_ts task ty in
    task (* the meta is yet here *)) keep task in
  task,{
    etenv = tenv;
    ekeep = keep;
    prop_toremove = Mpr.empty;
    eprojty = projty;
    edefined_lsymbol = Mls.empty;
    edefined_tsymbol = Mts.empty
  }

(* This one take use the tag but also all the type which appear in the goal *)
let is_ty_mono ~only_mono ty =
  try
    let rec check () ty = match ty.ty_node with
      | Tyvar _ -> raise Exit
      | Tyapp _ -> ty_fold check () ty in
    check () ty;
    true
  with Exit when not only_mono -> false


let create_trans_complete kept complete =
  let task = use_export None builtin_theory in
  let tenv = match complete with
    | None | Some [MAstr "yes"] -> Complete
    | Some [MAstr "no"] ->  Incomplete
    | _ -> failwith "instantiate complete wrong argument" in
  let init_task,env = create_env task tenv kept in
  Trans.fold_map fold_map env init_task

let encoding_instantiate =
  Trans.compose Libencoding.close_kept
  (Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
    Trans.on_meta_excl meta_complete (fun complete ->
      create_trans_complete kept complete)))

let () = Hashtbl.replace Encoding.ft_enco_kept "instantiate"
  (const encoding_instantiate)


let create_trans_complete create_env kept complete =
  let task = use_export None builtin_theory in
  let tenv = match complete with
    | None | Some [MAstr "yes"] -> Complete
    | Some [MAstr "no"] ->  Incomplete
    | _ -> failwith "instantiate complete wrong argument" in
  let init_task,env = create_env task tenv kept in
  Trans.fold_map fold_map env init_task

let t create_env =
  Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
  Trans.on_meta_excl meta_complete (fun complete ->
      create_trans_complete create_env kept complete))

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
