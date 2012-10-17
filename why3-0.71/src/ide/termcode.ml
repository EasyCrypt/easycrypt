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

open Why3
open Ty
open Term


(* similarity code of terms, or of "shapes"

example:

  shape(forall x:int, x * x >= 0) =
         Forall(Int,App(infix_gteq,App(infix_st,Tvar 0,Tvar 0),Const(0)))
       i.e: de bruijn indexes, first-order term

*)

let vs_rename_alpha c h vs = incr c; Mvs.add vs !c h

let vl_rename_alpha c h vl = List.fold_left (vs_rename_alpha c) h vl

let rec pat_rename_alpha c h p = match p.pat_node with
  | Pvar v -> vs_rename_alpha c h v
  | Pas (p, v) -> pat_rename_alpha c (vs_rename_alpha c h v) p
  | Por (p, _) -> pat_rename_alpha c h p
  | _ -> Term.pat_fold (pat_rename_alpha c) h p


let tag_and = "A"
let tag_app = "a"
let tag_case = "C"
let tag_const = "c"
let tag_Dtype = "Dt"
let tag_Dlogic = "Dl"
let tag_Dind = "Di"
let tag_Dprop = "Dp"
let tag_exists = "E"
let tag_eps = "e"
let tag_forall = "F"
let tag_false = "f"
let tag_impl = "I"
let tag_if = "i"
let tag_let = "L"
let tag_not = "N"
let tag_or = "O"
let tag_Plemma = "Pl"
let tag_Paxiom = "Pa"
let tag_Pgoal = "Pg"
let tag_Pskip = "Ps"
let tag_iff = "q"
let tag_true = "t"
let tag_tDecl = "TD"
let tag_tClone = "TC"
let tag_tUse = "TU"
let tag_tMeta = "TM"
let tag_var = "V"
let tag_wild = "w"
let tag_as = "z"

let const_shape ~push acc c =
  let b = Buffer.create 17 in
  Format.bprintf b "%a" Pretty.print_const c;
  push (Buffer.contents b) acc

let rec pat_shape ~(push:string->'a->'a) c m (acc:'a) p : 'a =
  match p.pat_node with
    | Pwild -> push tag_wild acc
    | Pvar _ -> push tag_var acc
    | Papp (f, l) ->
        List.fold_left (pat_shape ~push c m)
          (push (f.ls_name.Ident.id_string) (push tag_app acc))
          l
    | Pas (p, _) -> push tag_as (pat_shape ~push c m acc p)
    | Por (p, q) ->
        pat_shape ~push c m (push tag_or (pat_shape ~push c m acc q)) p

let rec t_shape ~(push:string->'a->'a) c m (acc:'a) t : 'a =
  let fn = t_shape ~push c m in
  match t.t_node with
    | Tconst c -> const_shape ~push (push tag_const acc) c
    | Tvar v ->
        let x =
          try string_of_int (Mvs.find v m)
          with Not_found -> v.vs_name.Ident.id_string
        in
        push x (push tag_var acc)
    | Tapp (s,l) ->
        List.fold_left fn
          (push (s.ls_name.Ident.id_string) (push tag_app acc))
          l
    | Tif (f,t1,t2) -> fn (fn (fn (push tag_if acc) f) t1) t2
    | Tlet (t1,b) ->
        let u,t2 = t_open_bound b in
        let m = vs_rename_alpha c m u in
        t_shape ~push c m (fn (push tag_let acc) t1) t2
    | Tcase (t1,bl) ->
        let br_shape acc b =
          let p,t2 = t_open_branch b in
          let acc = pat_shape ~push c m acc p in
          let m = pat_rename_alpha c m p in
          t_shape ~push c m acc t2
        in
        List.fold_left br_shape (fn (push tag_case acc) t1) bl
    | Teps b ->
        let u,f = t_open_bound b in
        let m = vs_rename_alpha c m u in
        t_shape ~push c m (push tag_eps acc) f
    | Tquant (q,b) ->
        let vl,triggers,f1 = t_open_quant b in
        let m = vl_rename_alpha c m vl in
        let hq = match q with Tforall -> tag_forall | Texists -> tag_exists in
        (* argument first, intentionally, to give more weight on A in
           forall x,A *)
        let acc = push hq (t_shape ~push c m acc f1) in
        List.fold_right
          (fun trigger acc ->
             List.fold_right
               (fun t acc ->
                  t_shape ~push c m acc t)
               trigger acc)
          triggers acc
    | Tbinop (o,f,g) ->
        let tag = match o with
          | Tand -> tag_and
          | Tor -> tag_or
          | Timplies -> tag_impl
          | Tiff -> tag_iff
        in
        fn (push tag (fn acc g)) f
          (* g first, intentionally, to give more weight on B in A->B *)
    | Tnot f -> push tag_not (fn acc f)
    | Ttrue -> push tag_true acc
    | Tfalse -> push tag_false acc

let t_shape_buf t =
  let b = Buffer.create 17 in
  let push t () = Buffer.add_string b t in
  let () = t_shape ~push (ref (-1)) Mvs.empty () t in
  Buffer.contents b

let t_shape_list t =
  let push t l = t::l in
  List.rev (t_shape ~push (ref (-1)) Mvs.empty [] t)

let pr_shape_list fmt t =
  List.iter (fun s -> Format.fprintf fmt "%s" s) (t_shape_list t)


(* shape of a task *)

let logic_decl_shape ~(push:string->'a->'a) (acc:'a) (ls,d) : 'a =
  let acc = push (ls.ls_name.Ident.id_string) acc in
  match d with
    | None -> acc
    | Some def ->
        let vl,t = Decl.open_ls_defn def in
        let c = ref (-1) in
        let m = vl_rename_alpha c Mvs.empty vl in
        t_shape ~push c m acc t

let logic_ind_decl_shape ~(push:string->'a->'a) (acc:'a) (ls,cl) : 'a =
  let acc = push (ls.ls_name.Ident.id_string) acc in
  List.fold_right
    (fun (_,t) acc -> t_shape ~push (ref (-1)) Mvs.empty acc t)
    cl acc

let propdecl_shape ~(push:string->'a->'a) (acc:'a) (k,n,t) : 'a =
  let tag = match k with
    | Decl.Plemma -> tag_Plemma
    | Decl.Paxiom -> tag_Paxiom
    | Decl.Pgoal -> tag_Pgoal
    | Decl.Pskip -> tag_Pskip
  in
  let acc = push tag acc in
  let acc = push n.Decl.pr_name.Ident.id_string acc in
  t_shape ~push (ref(-1)) Mvs.empty acc t

let decl_shape ~(push:string->'a->'a) (acc:'a) d : 'a =
  match d.Decl.d_node with
    | Decl.Dtype tyl ->
        List.fold_right
          (fun _ty acc -> acc)
          tyl (push tag_Dtype acc)
    | Decl.Dlogic ldl ->
        List.fold_right
          (fun d acc -> logic_decl_shape ~push acc d)
          ldl (push tag_Dlogic acc)
    | Decl.Dind idl ->
        List.fold_right
          (fun d acc -> logic_ind_decl_shape ~push acc d)
          idl (push tag_Dind acc)
    | Decl.Dprop pdecl ->
        propdecl_shape ~push (push tag_Dprop acc) pdecl

let tdecl_shape ~(push:string->'a->'a) (acc:'a) t : 'a =
  match t.Theory.td_node with
    | Theory.Decl d -> decl_shape ~push (push tag_tDecl acc) d
    | Theory.Meta _ -> push tag_tMeta acc
    | Theory.Clone _ -> push tag_tClone acc
    | Theory.Use _ -> push tag_tUse acc

let rec task_shape ~(push:string->'a->'a) (acc:'a) t : 'a =
  match t with
    | None -> acc
    | Some t ->
        task_shape ~push (tdecl_shape ~push acc t.Task.task_decl)
          t.Task.task_prev

(* checksum of a task
   it is the MD5 digest of the shape
*)

let task_checksum t =
  let b = Buffer.create 257 in
  let push t () = Buffer.add_string b t in
  let () = task_shape ~push () t in
  let shape = Buffer.contents b in
  Digest.to_hex (Digest.string shape)



