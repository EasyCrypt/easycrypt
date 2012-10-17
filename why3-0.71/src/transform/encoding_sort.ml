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

type tenv = {
  specials : tysymbol Hty.t;
  trans_lsymbol : lsymbol Hls.t
}

let init_tenv = {
  specials = Hty.create 17;
  trans_lsymbol = Hls.create 17 }


(* Convert type *)
let conv_ts tenv undefined name ty =
  let ts =
    try
      Hty.find tenv.specials ty
    with Not_found ->
      let ts = create_tysymbol (id_clone name) [] None in
      Hty.add tenv.specials ty ts;
      ts in
  Hts.replace undefined ts ();
  ts


let conv_ty tenv undefined ty =
  match ty.ty_node with
    | Tyapp (_,[]) -> ty
    | Tyapp (ts,_) ->
      let ts = conv_ts tenv undefined ts.ts_name ty in
      ty_app ts []
    | _ -> Printer.unsupportedType ty "type variable must be encoded"

(* Convert a variable *)
let conv_vs tenv ud vs =
  let ty = conv_ty tenv ud vs.vs_ty in
  if ty_equal ty vs.vs_ty then vs else
  create_vsymbol (id_clone vs.vs_name) ty

(* Convert a logic symbol to the encoded one *)
let conv_ls tenv ud ls =
  if ls_equal ls ps_equ then ls
  else try Hls.find tenv.trans_lsymbol ls with Not_found ->
  let ty_res = Util.option_map (conv_ty tenv ud) ls.ls_value in
  let ty_arg = List.map (conv_ty tenv ud) ls.ls_args in
  let ls' =
    if Util.option_eq ty_equal ty_res ls.ls_value &&
       List.for_all2 ty_equal ty_arg ls.ls_args then ls
    else create_lsymbol (id_clone ls.ls_name) ty_arg ty_res
  in
  Hls.add tenv.trans_lsymbol ls ls';
  ls'


let rec rewrite_term tenv ud vm t =
  let fnT = rewrite_term tenv ud in
  let fnF = rewrite_fmla tenv ud in
  match t.t_node with
  | Tconst _ -> t
  | Tvar x ->
      Mvs.find x vm
  | Tapp (fs,tl) ->
      let fs = conv_ls tenv ud fs in
      let tl = List.map (fnT vm) tl in
      fs_app fs tl (of_option fs.ls_value)
  | Tif (f, t1, t2) ->
      t_if (fnF vm f) (fnT vm t1) (fnT vm t2)
  | Tlet (t1, b) ->
      let u,t2,close = t_open_bound_cb b in
      let u' = conv_vs tenv ud u in
      let t1' = fnT vm t1 in
      let t2' = fnT (Mvs.add u (t_var u') vm) t2 in
      t_let t1' (close u' t2')
  | Tcase _ | Teps _ ->
      Printer.unsupportedTerm t "unsupported term"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and rewrite_fmla tenv ud vm f =
  let fnT = rewrite_term tenv ud in
  let fnF = rewrite_fmla tenv ud in
  match f.t_node with
  | Tapp (ps,tl) when ls_equal ps ps_equ ->
      ps_app ps (List.map (fnT vm) tl)
  | Tapp (ps,tl) ->
      let ps = conv_ls tenv ud ps in
      let tl = List.map (fnT vm) tl in
      ps_app ps tl
  | Tquant (q,b) ->
      let vl, tl, f1, close = t_open_quant_cb b in
      let add m v = let v' = conv_vs tenv ud v in Mvs.add v (t_var v') m, v' in
      let vm', vl' = Util.map_fold_left add vm vl in
      let tl' = TermTF.tr_map (fnT vm') (fnF vm') tl in
      let f1' = fnF vm' f1 in
      t_quant q (close vl' tl' f1')
  | Tlet (t1, b) ->
      let u,f1,close = t_open_bound_cb b in
      let u' = conv_vs tenv ud u in
      let t1' = fnT vm t1 in
      let f1' = fnF (Mvs.add u (t_var u') vm) f1 in
      t_let t1' (close u' f1')
  | Tcase _ ->
      Printer.unsupportedTerm f "unsupported formula"
  | _ -> TermTF.t_map (fnT vm) (fnF vm) f

let decl_ud ud task =
  let add ts () task = add_ty_decl task [ts,Tabstract] in
  Hts.fold add ud task

let fold tenv taskpre task =
  let fnT = rewrite_term tenv in
  let fnF = rewrite_fmla tenv in
  match taskpre.task_decl.td_node with
    | Decl d ->
      begin match d.d_node with
        | Dtype dl ->
          let add acc = function
            | ({ts_def = Some _} | {ts_args = _::_}), Tabstract -> acc
            | _, Tabstract as d -> d::acc
            | _ -> Printer.unsupportedDecl d "use eliminate_algebraic"
          in
          let l = List.rev (List.fold_left add [] dl) in
          if l = [] then task else add_ty_decl task l
        | Dlogic ll ->
          let ud = Hts.create 3 in
          let conv = function
            | ls, None -> conv_ls tenv ud ls, None
            | _ -> Printer.unsupportedDecl d "use eliminate_definition"
          in
          add_logic_decl (decl_ud ud task) (List.map conv ll)
        | Dind _ ->
          Printer.unsupportedDecl d "use eliminate_inductive"
        | Dprop _ ->
          let ud = Hts.create 3 in
          decl_ud ud (add_decl task
                        (DeclTF.decl_map (fnT ud Mvs.empty) (fnF ud Mvs.empty) d))
      end
    | Meta(meta,ml) ->
      begin try
        let ud = Hts.create 3 in
        let map = function
          | MAty ty -> MAty (conv_ty tenv ud ty)
          | MAts {ts_name = name; ts_args = []; ts_def = Some ty} ->
            MAts (conv_ts tenv ud name ty)
          | MAts {ts_args = []; ts_def = None} as x -> x
          | MAts _ -> raise Exit
          | MAls ls -> MAls (conv_ls tenv ud ls)
          | MApr _ -> raise Exit
          | MAstr _ as s -> s
          | MAint _ as i -> i in
        let arg = List.map map ml in
        add_meta (decl_ud ud task) meta arg
      with
        | Printer.UnsupportedType _
        | Exit -> add_tdecl task taskpre.task_decl
      end
    | _ -> add_tdecl task taskpre.task_decl

let t =
  let tenv = init_tenv in
  Trans.fold (fold tenv) None

let () = Trans.register_transform "encoding_sort" t

