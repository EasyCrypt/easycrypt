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

type seen =
  | SNot
  | SOnce
  | SBack

let rec find h e =
  try
    let r = Hid.find h e in
    if r == e then e
    else
      let r = find h r in
      Hid.replace h e r;
      r
  with Not_found -> e

let union h e1 e2 = Hid.replace h (find h e1) (find h e2)

let connexe (m:Sid.t Mid.t)  =
  let uf = Hid.create 32 in
  let visited = Hid.create 32 in
  Mid.iter (fun e _ -> Hid.replace visited e SNot) m;
  let rec visit i last =
    match Hid.find visited i with
      | SNot ->
          Hid.replace visited i SOnce;
          let s = Mid.find i m in
          let last = i::last in
          Sid.iter (fun x -> visit x last) s;
          Hid.replace visited i SBack
      | SOnce ->
          (try
             List.iter (fun e -> if e==i then raise Exit else union uf i e) last
           with Exit -> ())
      | SBack -> ()
  in
  Mid.iter (fun e _ -> visit e []) m;
  let ce = Hid.create 32 in
  Mid.iter (fun e es ->
              let r = find uf e in
              let rl,rs,rb = try
                Hid.find ce r
              with Not_found -> [],Sid.empty, ref false in
              Hid.replace ce r (e::rl,Sid.union rs es,rb)) m;
  let rec visit (l,s,b) acc =
    if !b then acc
    else
      begin
        b := true;
        let acc = Sid.fold (fun e acc ->
                              try
                                visit (Hid.find ce e) acc
                              with Not_found -> acc) s acc in
        l::acc
      end
  in
  List.rev (Hid.fold (fun _ -> visit) ce [])



let elt d =
  match d.d_node with
    | Dlogic l ->
        let mem = Hid.create 16 in
        List.iter (fun a -> Hid.add mem (fst a).ls_name a) l;
        let tyoccurences acc _ = acc in
        let loccurences acc ls =
          if Hid.mem mem ls.ls_name then Sid.add ls.ls_name acc else acc in
        let m = List.fold_left
          (fun acc (ls,ld) -> match ld with
             | None -> Mid.add ls.ls_name Sid.empty acc
             | Some ld ->
                 let fd = ls_defn_axiom ld in
                 let s = t_s_fold tyoccurences loccurences Sid.empty fd in
                 Mid.add ls.ls_name s acc) Mid.empty l in
          let l = connexe m in
          List.map (fun e -> create_logic_decl (List.map (Hid.find mem) e)) l
    | Dtype l ->
        let mem = Hid.create 16 in
        List.iter (fun ((ts,_) as a) -> Hid.add mem ts.ts_name a) l;
        let tyoccurences acc ts =
          if Hid.mem mem ts.ts_name then Sid.add ts.ts_name acc else acc
        in
        let m = List.fold_left
          (fun m (ts,def) ->
             let s = match def with
               | Tabstract ->
                   begin match ts.ts_def with
                     | None -> Sid.empty
                     | Some ty -> ty_s_fold tyoccurences Sid.empty ty
                   end
               | Talgebraic l ->
                   List.fold_left
                     (fun acc {ls_args = tyl; ls_value = ty} ->
                        let ty = of_option ty in
                        List.fold_left
                          (fun acc ty -> ty_s_fold tyoccurences acc ty)
                          acc (ty::tyl)
                     ) Sid.empty l
             in
             Mid.add ts.ts_name s m) Mid.empty l
        in
        let l = connexe m in
        List.map (fun e -> create_ty_decl (List.map (Hid.find mem) e)) l
    | Dind _ -> [d] (* TODO *)
    | Dprop _ -> [d]

let t = Trans.decl elt None

let () = Trans.register_transform "simplify_recursive_definition" t

