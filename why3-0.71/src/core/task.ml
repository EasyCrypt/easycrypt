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

(** Clone and meta history *)

type tdecl_set = {
  tds_set : Stdecl.t;
  tds_tag : Hashweak.tag;
}

module Hstds = Hashcons.Make (struct
  type t = tdecl_set
  let equal s1 s2 = Stdecl.equal s1.tds_set s2.tds_set
  let hs_td td acc = Hashcons.combine acc (td_hash td)
  let hash s = Stdecl.fold hs_td s.tds_set 0
  let tag n s = { s with tds_tag = Hashweak.create_tag n }
end)

let mk_tds s = Hstds.hashcons {
  tds_set = s;
  tds_tag = Hashweak.dummy_tag;
}

let tds_empty = mk_tds Stdecl.empty
let tds_add td s = mk_tds (Stdecl.add td s.tds_set)
let tds_singleton td = mk_tds (Stdecl.singleton td)

let tds_equal : tdecl_set -> tdecl_set -> bool = (==)
let tds_hash tds = Hashweak.tag_hash tds.tds_tag

type clone_map = tdecl_set Mid.t
type meta_map = tdecl_set Mmeta.t

let cm_find cm th = Mid.find_default th.th_name tds_empty cm
let mm_find mm t = Mmeta.find_default t tds_empty mm

let cm_add cm th td = Mid.change th.th_name (function
  | None -> Some (tds_singleton td)
  | Some tds -> Some (tds_add td tds)) cm

let mm_add mm t td = Mmeta.change t (function
  | None -> Some (tds_singleton td)
  | Some tds -> Some (tds_add td tds)) mm

let mm_add mm t td = if t.meta_excl
  then Mmeta.add t (tds_singleton td) mm
  else mm_add mm t td

(** Task *)

type task = task_hd option

and task_hd = {
  task_decl  : tdecl;        (* last declaration *)
  task_prev  : task;         (* context *)
  task_known : known_map;    (* known identifiers *)
  task_clone : clone_map;    (* cloning history *)
  task_meta  : meta_map;     (* meta properties *)
  task_tag   : Hashweak.tag; (* unique magical tag *)
}

let task_hd_equal : task_hd -> task_hd -> bool = (==)

let task_hd_hash t = Hashweak.tag_hash t.task_tag

let task_equal t1 t2 = match t1, t2 with
  | Some t1, Some t2 -> task_hd_equal t1 t2
  | None, None -> true
  | _ -> false

let task_hash t = option_apply 0 (fun t -> task_hd_hash t + 1) t

module Hstask = Hashcons.Make (struct
  type t = task_hd

  let equal t1 t2 = td_equal t1.task_decl t2.task_decl &&
                  task_equal t1.task_prev t2.task_prev

  let hash t = Hashcons.combine (td_hash t.task_decl) (task_hash t.task_prev)

  let tag i task = { task with task_tag = Hashweak.create_tag i }
end)

let mk_task decl prev known clone meta = Some (Hstask.hashcons {
  task_decl  = decl;
  task_prev  = prev;
  task_known = known;
  task_clone = clone;
  task_meta  = meta;
  task_tag   = Hashweak.dummy_tag;
})

let task_known = option_apply Mid.empty (fun t -> t.task_known)
let task_clone = option_apply Mid.empty (fun t -> t.task_clone)
let task_meta  = option_apply Mmeta.empty (fun t -> t.task_meta)

let find_clone_tds task (th : theory) = cm_find (task_clone task) th
let find_meta_tds task (t : meta) = mm_find (task_meta task) t

(* constructors with checks *)

exception LemmaFound
exception SkipFound
exception GoalFound
exception GoalNotFound

let find_goal = function
  | Some {task_decl = {td_node = Decl {d_node = Dprop (Pgoal,p,f)}}} ->
      Some(p,f)
  | _ -> None

let task_goal task = match find_goal task with
  | Some (pr,_) -> pr
  | None        -> raise GoalNotFound

let task_goal_fmla task  = match find_goal task with
  | Some (_,f)  -> f
  | None        -> raise GoalNotFound

let check_task task = match find_goal task with
  | Some _  -> raise GoalFound
  | None    -> task

let check_decl = function
  | { d_node = Dprop (Plemma,_,_)} -> raise LemmaFound
  | { d_node = Dprop (Pskip,_,_)}  -> raise SkipFound
  | d -> d

let new_decl task d td =
  let kn = known_add_decl (task_known task) (check_decl d) in
  mk_task td (check_task task) kn (task_clone task) (task_meta task)

let new_decl task d td = try new_decl task d td with KnownIdent _ -> task

let new_clone task th td =
  let cl = cm_add (task_clone task) th td in
  mk_task td (check_task task) (task_known task) cl (task_meta task)

let new_meta task t td =
  let mt = mm_add (task_meta task) t td in
  mk_task td (check_task task) (task_known task) (task_clone task) mt

(* declaration constructors + add_decl *)

let add_decl task d = new_decl task d (create_decl d)

let add_ty_decl tk dl = add_decl tk (create_ty_decl dl)
let add_logic_decl tk dl = add_decl tk (create_logic_decl dl)
let add_ind_decl tk dl = add_decl tk (create_ind_decl dl)
let add_prop_decl tk k p f = add_decl tk (create_prop_decl k p f)

(* task constructors *)

let rec add_tdecl task td = match td.td_node with
  | Decl d -> new_decl task d td
  | Use th -> use_export task th
  | Clone (th,_) -> new_clone task th td
  | Meta (t,_) -> new_meta task t td

and flat_tdecl task td = match td.td_node with
  | Decl { d_node = Dprop (Plemma,pr,f) } -> add_prop_decl task Paxiom pr f
  | Decl { d_node = Dprop ((Pgoal|Pskip),_,_) } -> task
  | _ -> add_tdecl task td

and use_export task th =
  let td = create_null_clone th in
  if Stdecl.mem td (find_clone_tds task th).tds_set then task else
  let task = List.fold_left flat_tdecl task th.th_decls in
  new_clone task th td

let clone_export = clone_theory flat_tdecl

let add_meta task t al = new_meta task t (create_meta t al)

(* split theory *)

let split_tdecl names (res,task) td = match td.td_node with
  | Decl { d_node = Dprop ((Pgoal|Plemma),pr,f) }
    when option_apply true (Spr.mem pr) names ->
      let res = add_prop_decl task Pgoal pr f :: res in
      res, flat_tdecl task td
  | _ ->
      res, flat_tdecl task td

let split_theory th names init =
  fst (List.fold_left (split_tdecl names) ([],init) th.th_decls)

(* Generic utilities *)

let rec task_fold fn acc = function
  | Some task -> task_fold fn (fn acc task.task_decl) task.task_prev
  | None      -> acc

let rec task_iter fn = function
  | Some task -> fn task.task_decl; task_iter fn task.task_prev
  | None      -> ()

let task_tdecls = task_fold (fun acc td -> td::acc) []

let task_decls  = task_fold (fun acc td ->
  match td.td_node with Decl d -> d::acc | _ -> acc) []

(* Realization utilities *)

let used_theories task =
  let used { tds_set = s } =
    let th = match Mtdecl.choose s with
      | { td_node = Clone (th,_) }, _ -> th
      | _ -> assert false in
    let td = create_null_clone th in
    if Stdecl.mem td s then Some th else None
  in
  Mid.map_filter used (task_clone task)

let used_symbols thmap =
  let dict th = Mid.map (fun () -> th) th.th_local in
  let join _ = Mid.union (fun _ -> assert false) in
  Mid.fold join (Mid.map dict thmap) Mid.empty

let local_decls task symbmap =
  let rec skip t = function
    | { td_node = Clone (th,_) } :: rest
      when id_equal t.th_name th.th_name -> rest
    | _ :: rest -> skip t rest
    | [] -> []
  in
  let rec filter acc = function
    | { td_node = Decl d } :: rest ->
        let id = Sid.choose d.d_news in
        (try filter acc (skip (Mid.find id symbmap) rest)
        with Not_found -> filter (d::acc) rest)
    | _ :: rest -> filter acc rest
    | [] -> List.rev acc
  in
  filter [] (task_tdecls task)

(* Selectors *)

exception NotTaggingMeta of meta
exception NotExclusiveMeta of meta

let on_meta t fn acc task =
  let add td acc = match td.td_node with
    | Meta (_,ma) -> fn acc ma
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl.fold add tds.tds_set acc

let on_theory th fn acc task =
  let add td acc = match td.td_node with
    | Clone (_,sm) -> fn acc sm
    | _ -> assert false
  in
  let tds = find_clone_tds task th in
  Stdecl.fold add tds.tds_set acc

let on_meta_excl t task =
  if not t.meta_excl then raise (NotExclusiveMeta t);
  let add td _ = match td.td_node with
    | Meta (_,ma) -> Some ma
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl.fold add tds.tds_set None

let on_used_theory th task =
  let td = create_null_clone th in
  let tds = find_clone_tds task th in
  Stdecl.mem td tds.tds_set

let on_tagged_ty t task =
  begin match t.meta_type with
    | MTty :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MAty ty :: _) -> Sty.add ty acc
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl.fold add tds.tds_set Sty.empty

let on_tagged_ts t task =
  begin match t.meta_type with
    | MTtysymbol :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MAts ts :: _) -> Sts.add ts acc
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl.fold add tds.tds_set Sts.empty

let on_tagged_ls t task =
  begin match t.meta_type with
    | MTlsymbol :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MAls ls :: _) -> Sls.add ls acc
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl.fold add tds.tds_set Sls.empty

let on_tagged_pr t task =
  begin match t.meta_type with
    | MTprsymbol :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MApr pr :: _) -> Spr.add pr acc
    | _ -> assert false
  in
  let tds = find_meta_tds task t in
  Stdecl.fold add tds.tds_set Spr.empty

(* Exception reporting *)

let () = Exn_printer.register (fun fmt exn -> match exn with
  | LemmaFound ->   Format.fprintf fmt "Task cannot contain a lemma"
  | SkipFound ->    Format.fprintf fmt "Task cannot contain a skip"
  | GoalFound ->    Format.fprintf fmt "The task already ends with a goal"
  | GoalNotFound -> Format.fprintf fmt "The task does not end with a goal"
  | NotTaggingMeta m ->
      Format.fprintf fmt "Metaproperty '%s' is not a symbol tag" m.meta_name
  | NotExclusiveMeta m ->
      Format.fprintf fmt "Metaproperty '%s' is not exclusive" m.meta_name
  | _ -> raise exn)

(* task1 : prefix
   lt : to reduce
   lk : suffix (reverse order)
   i : length of lt
*)

let rec split i l acc = match i,l with
  | 0, l -> List.rev acc, l
  | _, [] -> assert false
  | n, a::l -> split (pred n) l (a::acc)

let merge task l = List.fold_left add_tdecl task l

let rec bisect_aux f task lt i lk =
  if i < 2 then
    if try f (merge task lk) with UnknownIdent _ -> false then [] else
        (assert (List.length lt = 1); lt)
  else
    let i1 = i/2 in
    let i2 =  i/2 + i mod 2 in
    let lt1,lt2 = split i1 lt [] in
    let task1 = merge task lt1 in (** Can't fail *)
    (** These "if then else" allow to remove big chunck with one call to f *)
    if try f (merge task1 lk) with UnknownIdent _ -> false
    then bisect_aux f task lt1 i1 lk
    else
      if try f (merge (merge task lt2) lk) with UnknownIdent _ -> false
      then bisect_aux f task lt2 i2 lk
      else
        let lt2 = bisect_aux f task1 lt2 i2 lk in
        let lk2 = List.append lt2 lk in
        let lt1 = bisect_aux f task lt1 i1 lk2 in
        List.append lt1 lt2

let bisect f task =
  let task,goal = match task with
    | Some {task_decl = {td_node = Decl {d_node = Dprop (Pgoal,_,_)}} as td;
            task_prev = task} -> task,td
    | _ -> raise GoalNotFound in
  let lt,i,tacc = task_fold (fun (acc,i,tacc) td ->
    match td.td_node with
      | Decl _ -> (td::acc,succ i,tacc)
      | _ -> (acc,i,td::tacc)) ([],0,[]) task in
  let task = merge None tacc in
  let lt = bisect_aux f task lt i [goal] in
  add_tdecl (merge task lt) goal
