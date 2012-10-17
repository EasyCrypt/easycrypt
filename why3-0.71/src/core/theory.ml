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

open Format
open Util
open Ident
open Ty
open Term
open Decl

(** Namespace *)

type namespace = {
  ns_ts : tysymbol Mstr.t;   (* type symbols *)
  ns_ls : lsymbol Mstr.t;    (* logic symbols *)
  ns_pr : prsymbol Mstr.t;   (* propositions *)
  ns_ns : namespace Mstr.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_ts = Mstr.empty;
  ns_ls = Mstr.empty;
  ns_pr = Mstr.empty;
  ns_ns = Mstr.empty;
}

exception ClashSymbol of string

let ns_replace eq chk x vo vn =
  if not chk then vn else
  if eq vo vn then vo else
  raise (ClashSymbol x)

let ns_union eq chk =
  Mstr.union (fun x vn vo -> Some (ns_replace eq chk x vo vn))

let rec merge_ns chk ns1 ns2 =
  let fusion _ ns1 ns2 = Some (merge_ns chk ns1 ns2) in
  { ns_ts = ns_union ts_equal chk ns1.ns_ts ns2.ns_ts;
    ns_ls = ns_union ls_equal chk ns1.ns_ls ns2.ns_ls;
    ns_pr = ns_union pr_equal chk ns1.ns_pr ns2.ns_pr;
    ns_ns = Mstr.union fusion     ns1.ns_ns ns2.ns_ns; }

let nm_add chk x ns m = Mstr.change x (function
  | None -> Some ns
  | Some os -> Some (merge_ns chk ns os)) m

let ns_add eq chk x v m = Mstr.change x (function
  | None -> Some v
  | Some vo -> Some (ns_replace eq chk x vo v)) m

let ts_add = ns_add ts_equal
let ls_add = ns_add ls_equal
let pr_add = ns_add pr_equal

let add_ts chk x ts ns = { ns with ns_ts = ts_add chk x ts ns.ns_ts }
let add_ls chk x ls ns = { ns with ns_ls = ls_add chk x ls ns.ns_ls }
let add_pr chk x pf ns = { ns with ns_pr = pr_add chk x pf ns.ns_pr }
let add_ns chk x nn ns = { ns with ns_ns = nm_add chk x nn ns.ns_ns }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_ts = ns_find (fun ns -> ns.ns_ts)
let ns_find_ls = ns_find (fun ns -> ns.ns_ls)
let ns_find_pr = ns_find (fun ns -> ns.ns_pr)
let ns_find_ns = ns_find (fun ns -> ns.ns_ns)

(** Meta properties *)

type meta_arg_type =
  | MTty
  | MTtysymbol
  | MTlsymbol
  | MTprsymbol
  | MTstring
  | MTint

type meta_arg =
  | MAty  of ty
  | MAts  of tysymbol
  | MAls  of lsymbol
  | MApr  of prsymbol
  | MAstr of string
  | MAint of int

type meta = {
  meta_name : string;
  meta_type : meta_arg_type list;
  meta_excl : bool;
  meta_tag  : int;
}

module SMmeta = StructMake(struct type t = meta let tag m = m.meta_tag end)

module Smeta = SMmeta.S
module Mmeta = SMmeta.M
module Hmeta = SMmeta.H

let meta_equal : meta -> meta -> bool = (==)

let meta_hash m = m.meta_tag

exception KnownMeta of meta
exception UnknownMeta of string
exception BadMetaArity of meta * int * int
exception MetaTypeMismatch of meta * meta_arg_type * meta_arg_type

let meta_table = Hashtbl.create 17

let mk_meta =
  let c = ref (-1) in
  fun s al excl -> {
    meta_name = s;
    meta_type = al;
    meta_excl = excl;
    meta_tag  = (incr c; !c) }

let register_meta s al excl =
  try
    let m = Hashtbl.find meta_table s in
    if al = m.meta_type && excl = m.meta_excl then m
    else raise (KnownMeta m)
  with Not_found ->
    let m = mk_meta s al excl in
    Hashtbl.add meta_table s m;
    m

let register_meta_excl s al = register_meta s al true
let register_meta      s al = register_meta s al false

let lookup_meta s =
  try Hashtbl.find meta_table s
  with Not_found -> raise (UnknownMeta s)

let list_metas () = Hashtbl.fold (fun _ v acc -> v::acc) meta_table []

(** Theory *)

type theory = {
  th_name   : ident;      (* theory name *)
  th_path   : string list;(* environment qualifiers *)
  th_decls  : tdecl list; (* theory declarations *)
  th_export : namespace;  (* exported namespace *)
  th_known  : known_map;  (* known identifiers *)
  th_local  : Sid.t;      (* locally declared idents *)
  th_used   : Sid.t;      (* used theories *)
}

and tdecl = {
  td_node : tdecl_node;
  td_tag  : int;
}

and tdecl_node =
  | Decl  of decl
  | Use   of theory
  | Clone of theory * symbol_map
  | Meta  of meta * meta_arg list

and symbol_map = {
  sm_ts : tysymbol Mts.t;
  sm_ls : lsymbol Mls.t;
  sm_pr : prsymbol Mpr.t;
}

(** Theory declarations *)

module Hstdecl = Hashcons.Make (struct

  type t = tdecl

  let eq_marg a1 a2 = match a1,a2 with
    | MAty ty1, MAty ty2 -> ty_equal ty1 ty2
    | MAts ts1, MAts ts2 -> ts_equal ts1 ts2
    | MAls ls1, MAls ls2 -> ls_equal ls1 ls2
    | MApr pr1, MApr pr2 -> pr_equal pr1 pr2
    | MAstr s1, MAstr s2 -> s1 = s2
    | MAint i1, MAint i2 -> i1 = i2
    | _,_ -> false

  let eq_smap sm1 sm2 =
    Mts.equal ts_equal sm1.sm_ts sm2.sm_ts &&
    Mls.equal ls_equal sm1.sm_ls sm2.sm_ls &&
    Mpr.equal pr_equal sm1.sm_pr sm2.sm_pr

  let equal td1 td2 = match td1.td_node, td2.td_node with
    | Decl d1, Decl d2 -> d_equal d1 d2
    | Use th1, Use th2 -> id_equal th1.th_name th2.th_name
    | Clone (th1,sm1), Clone (th2,sm2) ->
        id_equal th1.th_name th2.th_name && eq_smap sm1 sm2
    | Meta (t1,al1), Meta (t2,al2) ->
        t1 = t2 && list_all2 eq_marg al1 al2
    | _,_ -> false

  let hs_cl_ts _ ts acc = Hashcons.combine acc (ts_hash ts)
  let hs_cl_ls _ ls acc = Hashcons.combine acc (ls_hash ls)
  let hs_cl_pr _ pr acc = Hashcons.combine acc (pr_hash pr)

  let hs_ta = function
    | MAty ty -> ty_hash ty
    | MAts ts -> ts_hash ts
    | MAls ls -> ls_hash ls
    | MApr pr -> pr_hash pr
    | MAstr s -> Hashtbl.hash s
    | MAint i -> Hashtbl.hash i

  let hs_smap sm h =
    Mts.fold hs_cl_ts sm.sm_ts
      (Mls.fold hs_cl_ls sm.sm_ls
        (Mpr.fold hs_cl_pr sm.sm_pr h))

  let hash td = match td.td_node with
    | Decl d -> d_hash d
    | Use th -> id_hash th.th_name
    | Clone (th,sm) -> hs_smap sm (id_hash th.th_name)
    | Meta (t,al) -> Hashcons.combine_list hs_ta (Hashtbl.hash t) al

  let tag n td = { td with td_tag = n }

end)

let mk_tdecl n = Hstdecl.hashcons { td_node = n ; td_tag = -1 }

module Tdecl = StructMake (struct
  type t = tdecl
  let tag td = td.td_tag
end)

module Stdecl = Tdecl.S
module Mtdecl = Tdecl.M
module Htdecl = Tdecl.H

let td_equal : tdecl -> tdecl -> bool = (==)
let td_hash td = td.td_tag

(** Constructors and utilities *)

type theory_uc = {
  uc_name   : ident;
  uc_path   : string list;
  uc_decls  : tdecl list;
  uc_import : namespace list;
  uc_export : namespace list;
  uc_known  : known_map;
  uc_local  : Sid.t;
  uc_used   : Sid.t;
}

exception CloseTheory
exception NoOpenedNamespace

let empty_theory n p = {
  uc_name   = id_register n;
  uc_path   = p;
  uc_decls  = [];
  uc_import = [empty_ns];
  uc_export = [empty_ns];
  uc_known  = Mid.empty;
  uc_local  = Sid.empty;
  uc_used   = Sid.empty;
}

let close_theory uc = match uc.uc_export with
  | [e] -> {
      th_name   = uc.uc_name;
      th_path   = uc.uc_path;
      th_decls  = List.rev uc.uc_decls;
      th_export = e;
      th_known  = uc.uc_known;
      th_local  = uc.uc_local;
      th_used   = uc.uc_used }
  | _ -> raise CloseTheory

let get_namespace uc = List.hd uc.uc_import
let get_known uc = uc.uc_known

let open_namespace uc = match uc.uc_import with
  | ns :: _ -> { uc with
      uc_import =       ns :: uc.uc_import;
      uc_export = empty_ns :: uc.uc_export; }
  | [] -> assert false

let close_namespace uc import s =
  match uc.uc_import, uc.uc_export with
  | _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = match s with Some s -> add_ns false s e0 i1 | _ -> i1 in
      let e1 = match s with Some s -> add_ns true  s e0 e1 | _ -> e1 in
      { uc with uc_import = i1 :: sti; uc_export = e1 :: ste; }
  | [_], [_] -> raise NoOpenedNamespace
  | _ -> assert false

(* Base constructors *)

let known_clone kn sm =
  Mts.iter (fun _ ts -> known_id kn ts.ts_name) sm.sm_ts;
  Mls.iter (fun _ ls -> known_id kn ls.ls_name) sm.sm_ls;
  Mpr.iter (fun _ pr -> known_id kn pr.pr_name) sm.sm_pr

let known_meta kn al =
  let check = function
    | MAty ty -> ty_s_fold (fun () ts -> known_id kn ts.ts_name) () ty
    | MAts ts -> known_id kn ts.ts_name
    | MAls ls -> known_id kn ls.ls_name
    | MApr pr -> known_id kn pr.pr_name
    | _ -> ()
  in
  List.iter check al

let add_tdecl uc td = match td.td_node with
  | Decl d -> { uc with
      uc_decls = td :: uc.uc_decls;
      uc_known = known_add_decl uc.uc_known d;
      uc_local = Sid.union uc.uc_local d.d_news }
  | Use th when Sid.mem th.th_name uc.uc_used -> uc
  | Use th -> { uc with
      uc_decls = td :: uc.uc_decls;
      uc_known = merge_known uc.uc_known th.th_known;
      uc_used  = Sid.union uc.uc_used (Sid.add th.th_name th.th_used) }
  | Clone (_,sm) -> known_clone uc.uc_known sm;
      { uc with uc_decls = td :: uc.uc_decls }
  | Meta (_,al) -> known_meta uc.uc_known al;
      { uc with uc_decls = td :: uc.uc_decls }

(** Declarations *)

let add_symbol add id v uc =
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = add false id.id_string v i0 :: sti;
      uc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_type uc (ts,def) =
  let add_constr uc fs = add_symbol add_ls fs.ls_name fs uc in
  let uc = add_symbol add_ts ts.ts_name ts uc in
  match def with
    | Tabstract -> uc
    | Talgebraic lfs -> List.fold_left add_constr uc lfs

let add_logic uc (ls,_) = add_symbol add_ls ls.ls_name ls uc

let add_ind uc (ps,la) =
  let uc = add_symbol add_ls ps.ls_name ps uc in
  let add uc (pr,_) = add_symbol add_pr pr.pr_name pr uc in
  List.fold_left add uc la

let add_prop uc (_,pr,_) = add_symbol add_pr pr.pr_name pr uc

let create_decl d = mk_tdecl (Decl d)

let add_decl uc d =
  let uc = add_tdecl uc (create_decl d) in
  match d.d_node with
    | Dtype dl  -> List.fold_left add_type uc dl
    | Dlogic dl -> List.fold_left add_logic uc dl
    | Dind dl   -> List.fold_left add_ind uc dl
    | Dprop p   -> add_prop uc p

(** Declaration constructors + add_decl *)

let add_ty_decl uc dl = add_decl uc (create_ty_decl dl)
let add_logic_decl uc dl = add_decl uc (create_logic_decl dl)
let add_ind_decl uc dl = add_decl uc (create_ind_decl dl)
let add_prop_decl uc k p f = add_decl uc (create_prop_decl k p f)

(** Use *)

let create_use th = mk_tdecl (Use th)

let use_export uc th =
  let uc = add_tdecl uc (create_use th) in
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = merge_ns false th.th_export i0 :: sti;
      uc_export = merge_ns true  th.th_export e0 :: ste }
  | _ -> assert false

(** Clone *)

type th_inst = {
  inst_ts    : tysymbol Mts.t;
  inst_ls    : lsymbol  Mls.t;
  inst_lemma : Spr.t;
  inst_goal  : Spr.t;
}

let empty_inst = {
  inst_ts    = Mts.empty;
  inst_ls    = Mls.empty;
  inst_lemma = Spr.empty;
  inst_goal  = Spr.empty;
}

let create_inst ~ts ~ls ~lemma ~goal =
  let add_ts acc (tso,tsn) = Mts.add tso tsn acc in
  let add_ls acc (lso,lsn) = Mls.add lso lsn acc in
  let add_pr acc lem = Spr.add lem acc in {
    inst_ts    = List.fold_left add_ts Mts.empty ts;
    inst_ls    = List.fold_left add_ls Mls.empty ls;
    inst_lemma = List.fold_left add_pr Spr.empty lemma;
    inst_goal  = List.fold_left add_pr Spr.empty goal }

exception CannotInstantiate of ident

type clones = {
  cl_local : Sid.t;
  mutable ts_table : tysymbol Mts.t;
  mutable ls_table : lsymbol Mls.t;
  mutable pr_table : prsymbol Mpr.t;
}

let empty_clones s = {
  cl_local = s;
  ts_table = Mts.empty;
  ls_table = Mls.empty;
  pr_table = Mpr.empty;
}

(* populate the clone structure *)

let rec cl_find_ts cl ts =
  if not (Sid.mem ts.ts_name cl.cl_local) then ts
  else try Mts.find ts cl.ts_table
  with Not_found ->
    let td' = option_map (cl_trans_ty cl) ts.ts_def in
    let ts' = create_tysymbol (id_clone ts.ts_name) ts.ts_args td' in
    cl.ts_table <- Mts.add ts ts' cl.ts_table;
    ts'

and cl_trans_ty cl ty = ty_s_map (cl_find_ts cl) ty

let cl_find_ls cl ls =
  if not (Sid.mem ls.ls_name cl.cl_local) then ls
  else try Mls.find ls cl.ls_table
  with Not_found ->
    let ta' = List.map (cl_trans_ty cl) ls.ls_args in
    let vt' = option_map (cl_trans_ty cl) ls.ls_value in
    let ls' = create_lsymbol (id_clone ls.ls_name) ta' vt' in
    cl.ls_table <- Mls.add ls ls' cl.ls_table;
    ls'

let cl_trans_fmla cl f = t_s_map (cl_trans_ty cl) (cl_find_ls cl) f

let cl_find_pr cl pr =
  if not (Sid.mem pr.pr_name cl.cl_local) then pr
  else try Mpr.find pr cl.pr_table
  with Not_found ->
    let pr' = create_prsymbol (id_clone pr.pr_name) in
    cl.pr_table <- Mpr.add pr pr' cl.pr_table;
    pr'

(* initialize the clone structure *)

exception NonLocal of ident
exception BadInstance of ident * ident

let cl_init_ts cl ts ts' =
  let id = ts.ts_name in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  if List.length ts.ts_args <> List.length ts'.ts_args
    then raise (BadInstance (id, ts'.ts_name));
  cl.ts_table <- Mts.add ts ts' cl.ts_table

let cl_init_ls cl ls ls' =
  let id = ls.ls_name in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  let mtch sb ty ty' =
    try ty_match sb ty' (cl_trans_ty cl ty)
    with TypeMismatch _ -> raise (BadInstance (id, ls'.ls_name))
  in
  let sb = match ls.ls_value,ls'.ls_value with
    | Some ty, Some ty' -> mtch Mtv.empty ty ty'
    | None, None -> Mtv.empty
    | _ -> raise (BadInstance (id, ls'.ls_name))
  in
  ignore (try List.fold_left2 mtch sb ls.ls_args ls'.ls_args
  with Invalid_argument _ -> raise (BadInstance (id, ls'.ls_name)));
  cl.ls_table <- Mls.add ls ls' cl.ls_table

let cl_init_pr cl pr =
  let id = pr.pr_name in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id)

let cl_init th inst =
  let cl = empty_clones th.th_local in
  Mts.iter (cl_init_ts cl) inst.inst_ts;
  Mls.iter (cl_init_ls cl) inst.inst_ls;
  Spr.iter (cl_init_pr cl) inst.inst_lemma;
  Spr.iter (cl_init_pr cl) inst.inst_goal;
  cl

(* clone declarations *)

let cl_type cl inst tdl =
  let add_constr ls =
    if Mls.mem ls inst.inst_ls
      then raise (CannotInstantiate ls.ls_name)
      else cl_find_ls cl ls
  in
  let add_type (ts,td) acc =
    if Mts.mem ts inst.inst_ts then
      if ts.ts_def = None && td = Tabstract then acc
      else raise (CannotInstantiate ts.ts_name)
    else
      let ts' = cl_find_ts cl ts in
      let td' = match td with
        | Tabstract -> Tabstract
        | Talgebraic cl -> Talgebraic (List.map add_constr cl)
      in
      (ts',td') :: acc
  in
  create_ty_decl (List.fold_right add_type tdl [])

let extract_ls_defn f =
  let vl,_,f = match f.t_node with
    | Tquant (Tforall,b) -> t_open_quant b
    | _ -> [],[],f in
  match f.t_node with
    | Tapp (_, [{t_node = Tapp (ls,_)}; f])
    | Tbinop (_, {t_node = Tapp (ls,_)}, f) -> make_ls_defn ls vl f
    | _ -> assert false

let cl_logic cl inst ldl =
  let add_logic (ls,ld) acc = match ld with
    | None when Mls.mem ls inst.inst_ls ->
        acc
    | None ->
        (cl_find_ls cl ls, None) :: acc
    | Some _ when Mls.mem ls inst.inst_ls ->
        raise (CannotInstantiate ls.ls_name)
    | Some ld ->
        let f = ls_defn_axiom ld in
        extract_ls_defn (cl_trans_fmla cl f) :: acc
  in
  create_logic_decl (List.fold_right add_logic ldl [])

let cl_ind cl inst idl =
  let add_case (pr,f) =
    if Spr.mem pr inst.inst_lemma || Spr.mem pr inst.inst_goal
      then raise (CannotInstantiate pr.pr_name)
      else cl_find_pr cl pr, cl_trans_fmla cl f
  in
  let add_ind (ps,la) =
    if Mls.mem ps inst.inst_ls
      then raise (CannotInstantiate ps.ls_name)
      else cl_find_ls cl ps, List.map add_case la
  in
  create_ind_decl (List.map add_ind idl)

let cl_prop cl inst (k,pr,f) =
  let k' = match k with
    | Pskip | Pgoal -> Pskip
    | Plemma when Spr.mem pr inst.inst_goal -> Pskip
    | Paxiom when Spr.mem pr inst.inst_goal -> Pgoal
    | Paxiom when Spr.mem pr inst.inst_lemma -> Plemma
    | Paxiom | Plemma -> Paxiom
  in
  let pr' = cl_find_pr cl pr in
  let f' = cl_trans_fmla cl f in
  create_prop_decl k' pr' f'

let cl_decl cl inst d = match d.d_node with
  | Dtype tdl -> cl_type cl inst tdl
  | Dlogic ldl -> cl_logic cl inst ldl
  | Dind idl -> cl_ind cl inst idl
  | Dprop p -> cl_prop cl inst p

let cl_marg cl = function
  | MAty ty -> MAty (cl_trans_ty cl ty)
  | MAts ts -> MAts (cl_find_ts cl ts)
  | MAls ls -> MAls (cl_find_ls cl ls)
  | MApr pr -> MApr (cl_find_pr cl pr)
  | a -> a

let cl_smap cl sm = {
  sm_ts = Mts.map (cl_find_ts cl) sm.sm_ts;
  sm_ls = Mls.map (cl_find_ls cl) sm.sm_ls;
  sm_pr = Mpr.map (cl_find_pr cl) sm.sm_pr}

let cl_tdecl cl inst td = match td.td_node with
  | Decl d -> Decl (cl_decl cl inst d)
  | Use th -> Use th
  | Clone (th,sm) -> Clone (th, cl_smap cl sm)
  | Meta (id,al) -> Meta (id, List.map (cl_marg cl) al)

let clone_theory cl add_td acc th inst =
  let add acc td =
    let td =
      try  Some (mk_tdecl (cl_tdecl cl inst td))
      with EmptyDecl -> None
    in
    option_apply acc (add_td acc) td
  in
  let acc = List.fold_left add acc th.th_decls in
  let sm = {
    sm_ts = cl.ts_table;
    sm_ls = cl.ls_table;
    sm_pr = cl.pr_table}
  in
  add_td acc (mk_tdecl (Clone (th, sm)))

let clone_export uc th inst =
  let cl = cl_init th inst in
  let uc = clone_theory cl add_tdecl uc th inst in

  let g_ts _ ts = not (Mts.mem ts inst.inst_ts) in
  let g_ls _ ls = not (Mls.mem ls inst.inst_ls) in

  let f_ts ts = Mts.find_default ts ts cl.ts_table in
  let f_ls ls = Mls.find_default ls ls cl.ls_table in
  let f_pr pr = Mpr.find_default pr pr cl.pr_table in

  let rec f_ns ns = {
    ns_ts = Mstr.map f_ts (Mstr.filter g_ts ns.ns_ts);
    ns_ls = Mstr.map f_ls (Mstr.filter g_ls ns.ns_ls);
    ns_pr = Mstr.map f_pr ns.ns_pr;
    ns_ns = Mstr.map f_ns ns.ns_ns; } in

  let ns = f_ns th.th_export in

  match uc.uc_import, uc.uc_export with
    | i0 :: sti, e0 :: ste -> { uc with
        uc_import = merge_ns false ns i0 :: sti;
        uc_export = merge_ns true  ns e0 :: ste; }
    | _ -> assert false

let clone_theory add_td acc th inst =
  clone_theory (cl_init th inst) add_td acc th inst

let create_clone = clone_theory (fun tdl td -> td :: tdl)

let create_null_clone th =
  let sm = {
    sm_ts = Mts.empty;
    sm_ls = Mls.empty;
    sm_pr = Mpr.empty}
  in
  mk_tdecl (Clone (th,sm))

let is_empty_sm sm =
  Mts.is_empty sm.sm_ts &&
  Mls.is_empty sm.sm_ls &&
  Mpr.is_empty sm.sm_pr


(** Meta properties *)

let get_meta_arg_type = function
  | MAty  _ -> MTty
  | MAts  _ -> MTtysymbol
  | MAls  _ -> MTlsymbol
  | MApr  _ -> MTprsymbol
  | MAstr _ -> MTstring
  | MAint _ -> MTint

let create_meta m al =
  let get_meta_arg at a =
    (* we allow "constant tysymbol <=> ty" conversion *)
    let a = match at,a with
      | MTtysymbol, MAty ({ ty_node = Tyapp (ts,[]) }) -> MAts ts
      | MTty, MAts ({ts_args = []} as ts) -> MAty (ty_app ts [])
      | _, _ -> a
    in
    let mt = get_meta_arg_type a in
    if at = mt then a else raise (MetaTypeMismatch (m,at,mt))
  in
  let al = try List.map2 get_meta_arg m.meta_type al
    with Invalid_argument _ ->
      raise (BadMetaArity (m, List.length m.meta_type, List.length al))
  in
  mk_tdecl (Meta (m,al))

let add_meta uc s al = add_tdecl uc (create_meta s al)

let clone_meta tdt sm = match tdt.td_node with
  | Meta (t,al) ->
      let find_ts ts = Mts.find_default ts ts sm.sm_ts in
      let find_ls ls = Mls.find_default ls ls sm.sm_ls in
      let find_pr pr = Mpr.find_default pr pr sm.sm_pr in
      let cl_marg = function
        | MAty ty -> MAty (ty_s_map find_ts ty)
        | MAts ts -> MAts (find_ts ts)
        | MAls ls -> MAls (find_ls ls)
        | MApr pr -> MApr (find_pr pr)
        | a -> a
      in
      mk_tdecl (Meta (t, List.map cl_marg al))
  | _ -> invalid_arg "clone_meta"

(** access to meta *)

(*
let theory_meta  = option_apply Mmeta.empty (fun t -> t.task_meta)

let find_meta_tds th (t : meta) = mm_find (theory_meta th) t

let on_meta meta fn acc theory =
  let add td acc = match td.td_node with
    | Meta (_,ma) -> fn acc ma
    | _ -> assert false
  in
  let tds = find_meta_tds theory meta in
  Stdecl.fold add tds.tds_set acc
*)

(*
let on_meta _meta fn acc theory =
  let tdecls = theory.th_decls in
  List.fold_left
    (fun acc td ->
       match td.td_node with
         | Meta (_,ma) -> fn acc ma
         | _ -> acc)
    acc tdecls
*)


(** Base theories *)

let builtin_theory =
  let uc = empty_theory (id_fresh "BuiltIn") [] in
  let uc = add_ty_decl uc [ts_int, Tabstract] in
  let uc = add_ty_decl uc [ts_real, Tabstract] in
  let uc = add_logic_decl uc [ps_equ, None] in
  close_theory uc

let highord_theory =
  let uc = empty_theory (id_fresh "HighOrd") [] in
  let uc = add_ty_decl uc [ts_func, Tabstract] in
  let uc = add_ty_decl uc [ts_pred, Tabstract] in
  let uc = add_logic_decl uc [fs_func_app, None] in
  let uc = add_logic_decl uc [ps_pred_app, None] in
  close_theory uc

let create_theory ?(path=[]) n =
  use_export (empty_theory n path) builtin_theory

let tuple_theory = Util.memo_int 17 (fun n ->
  let uc = empty_theory (id_fresh ("Tuple" ^ string_of_int n)) [] in
  let uc = add_ty_decl uc [ts_tuple n, Talgebraic [fs_tuple n]] in
  close_theory uc)

let tuple_theory_name s =
  let l = String.length s in
  if l < 6 then None else
  let p = String.sub s 0 5 in
  if p <> "Tuple" then None else
  let q = String.sub s 5 (l - 5) in
  let i = try int_of_string q with _ -> 0 in
  (* we only accept the decimal notation *)
  if q <> string_of_int i then None else
  Some i

let add_decl_with_tuples uc d =
  let ids = Mid.set_diff d.d_syms uc.uc_known in
  let add id s = match is_ts_tuple_id id with
    | Some n -> Sint.add n s
    | None -> s in
  let ixs = Sid.fold add ids Sint.empty in
  let add n uc = use_export uc (tuple_theory n) in
  add_decl (Sint.fold add ixs uc) d

(* Exception reporting *)

let print_meta_arg_type fmt = function
  | MTty -> fprintf fmt "type"
  | MTtysymbol -> fprintf fmt "type_symbol"
  | MTlsymbol -> fprintf fmt "logic_symbol"
  | MTprsymbol -> fprintf fmt "proposition"
  | MTstring -> fprintf fmt "string"
  | MTint -> fprintf fmt "int"

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | NonLocal id ->
      Format.fprintf fmt "Non-local ident: %s" id.id_string
  | CannotInstantiate id ->
      Format.fprintf fmt "Cannot instantiate a defined ident %s" id.id_string
  | BadInstance (id1, id2) ->
      Format.fprintf fmt "Cannot instantiate ident %s with %s"
        id1.id_string id2.id_string
  | CloseTheory ->
      Format.fprintf fmt "Cannot close theory: some namespaces are still open"
  | NoOpenedNamespace ->
      Format.fprintf fmt "No opened namespaces"
  | ClashSymbol s ->
      Format.fprintf fmt "Symbol %s is already defined in the current scope" s
  | UnknownMeta s ->
      Format.fprintf fmt "Unknown metaproperty %s" s
  | KnownMeta m ->
      Format.fprintf fmt "Metaproperty %s is already registered with \
        a conflicting signature" m.meta_name
  | BadMetaArity (m,i1,i2) ->
      Format.fprintf fmt "Metaproperty %s requires %d arguments but \
        is applied to %d" m.meta_name i1 i2
  | MetaTypeMismatch (m,t1,t2) ->
      Format.fprintf fmt "Metaproperty %s expects %a argument but \
        is applied to %a"
        m.meta_name print_meta_arg_type t1 print_meta_arg_type t2
  | _ -> raise exn
  end

