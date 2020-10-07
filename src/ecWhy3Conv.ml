(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------*)
open EcUtils
open Why3

(* ----------------------------------------------------------------------*)
module Talpha = struct
  type t = Term.vsymbol list * Term.term

  type talphaenv = {
    tae_map : int Term.Mvs.t;
    tae_ctn : int ref;
  }

  let tae_create () =
    { tae_map = Term.Mvs.empty; tae_ctn = ref 0; }

  let vs_rename_alpha tae vs =
    { tae with tae_map = Term.Mvs.add vs (postincr tae.tae_ctn) tae.tae_map; }

  let vl_rename_alpha tae vl =
    List.fold_left vs_rename_alpha tae vl

  let rec pat_rename_alpha m p =
    match p.Term.pat_node with
    | Term.Pvar v -> vs_rename_alpha m v
    | Term.Pas (p, v) -> pat_rename_alpha (vs_rename_alpha m v) p
    | Term.Por (p, _) -> pat_rename_alpha m p
    | _ -> Term.pat_fold pat_rename_alpha m p

  let w3_ty_compare t1 t2 = Ty.ty_hash   t1 - Ty.ty_hash   t2
  let w3_ls_compare l1 l2 = Term.ls_hash l1 - Term.ls_hash l2

  let w3_int_compare i1 i2 =
    compare2
      (lazy Number.(compare i1.il_kind i2.il_kind))
      (lazy (BigInt.compare i1.il_int i2.il_int))

  let w3_real_compare = Number.compare_real

  let w3_constant_compare = Constant.compare_const

  let rec pat_compare_alpha m1 m2 p1 p2 =
    let ct = w3_ty_compare p1.Term.pat_ty p2.Term.pat_ty in
    if ct <> 0 then ct else
      match p1.Term.pat_node, p2.Term.pat_node with
      | Term.Pwild, Term.Pwild -> 0

      | Term.Pvar v1, Term.Pvar v2 -> begin
          match Term.Mvs.find_opt v1 m1.tae_map,
                Term.Mvs.find_opt v2 m2.tae_map
          with
          | Some _ , None    -> 1
          | None   , Some _  -> -1
          | None   , None    -> Term.vs_hash v1 - Term.vs_hash v2
          | Some i1, Some i2 -> i1 - i2
        end

      | Term.Papp (f1, l1), Term.Papp (f2, l2) ->
          compare2
            (lazy (w3_ls_compare f1 f2))
            (lazy (List.compare (pat_compare_alpha m1 m2) l1 l2))

      | Term.Pas (p1, _), Term.Pas (p2, _) ->
          pat_compare_alpha m1 m2 p1 p2

      | Term.Por (p1, q1), Term.Por (p2, q2) ->
          compare2
            (lazy (pat_compare_alpha m1 m2 p1 p2))
            (lazy (pat_compare_alpha m1 m2 q1 q2))

      | _ -> compare_tag  p1.Term.pat_node p2.Term.pat_node

  let rec t_compare_alpha m1 m2 t1 t2 =
    if Term.t_equal t1 t2 then 0 else
      match ocompare w3_ty_compare t1.Term.t_ty t2.Term.t_ty with
      | ct when ct <> 0 -> ct
      | _ -> begin
        match t1.Term.t_node, t2.Term.t_node with
        | Term.Tvar v1, Term.Tvar v2 -> begin
            match Term.Mvs.find_opt v1 m1.tae_map,
                  Term.Mvs.find_opt v2 m2.tae_map
            with
            | Some _ , None    -> 1
            | None   , Some _  -> -1
            | None   , None    -> Term.vs_hash v1 - Term.vs_hash v2
            | Some i1, Some i2 -> i1 - i2
          end

        | Term.Tconst c1, Term.Tconst c2 ->
            w3_constant_compare c1 c2

        | Term.Tapp (f1, l1), Term.Tapp (f2, l2) ->
            compare2
              (lazy (w3_ls_compare f1 f2))
              (lazy (List.compare (t_compare_alpha m1 m2) l1 l2))

        | Term.Tif (f1, t1, e1), Term.Tif (f2, t2, e2) ->
            compare3
              (lazy (t_compare_alpha m1 m2 f1 f2))
              (lazy (t_compare_alpha m1 m2 t1 t2))
              (lazy (t_compare_alpha m1 m2 e1 e2))

        | Term.Tlet (t1, b1), Term.Tlet (t2, b2) -> begin
            match t_compare_alpha m1 m2 t1 t2 with
            | ct when ct <> 0 -> ct
            | _ ->
                let u1,e1 = Term.t_open_bound b1 in
                let u2,e2 = Term.t_open_bound b2 in
                let m1 = vs_rename_alpha m1 u1 in
                let m2 = vs_rename_alpha m2 u2 in
                  t_compare_alpha m1 m2 e1 e2
            end

        | Term.Tcase (t1, bl1), Term.Tcase (t2, bl2) -> begin
            match t_compare_alpha m1 m2 t1 t2 with
            | ct when ct <> 0 -> ct
            | _ ->
                let br_compare b1 b2 =
                  let p1,e1 = Term.t_open_branch b1 in
                  let p2,e2 = Term.t_open_branch b2 in
                    match pat_compare_alpha m1 m2 p1 p2 with
                    | ct when ct <> 0 -> ct
                    | _ ->
                      let m1 = pat_rename_alpha m1 p1 in
                      let m2 = pat_rename_alpha m2 p2 in
                        t_compare_alpha m1 m2 e1 e2
                in
                  List.compare br_compare bl1 bl2
          end

        | Term.Teps b1, Term.Teps b2 ->
            let u1,e1 = Term.t_open_bound b1 in
            let u2,e2 = Term.t_open_bound b2 in
            let m1 = vs_rename_alpha m1 u1 in
            let m2 = vs_rename_alpha m2 u2 in
              t_compare_alpha m1 m2 e1 e2

        | Term.Tquant (q1, b1), Term.Tquant (q2, b2) ->
            let compare_body b1 b2 =
              let cv v1 v2 = w3_ty_compare v1.Term.vs_ty v2.Term.vs_ty in
              let vl1,_,e1 = Term.t_open_quant b1 in
              let vl2,_,e2 = Term.t_open_quant b2 in
                compare2
                  (lazy (List.compare cv vl1 vl2))
                  (lazy (let m1 = vl_rename_alpha m1 vl1 in
                         let m2 = vl_rename_alpha m2 vl2 in
                           t_compare_alpha m1 m2 e1 e2))
            in
              compare2
                (lazy (compare q1 q2))
                (lazy (compare_body b1 b2))

        | Term.Tbinop (o1, f1, g1), Term.Tbinop (o2, f2, g2) ->
            compare3
              (lazy (compare o1 o2))
              (lazy (t_compare_alpha m1 m2 f1 f2))
              (lazy (t_compare_alpha m1 m2 g1 g2))

        | Term.Tnot f1, Term.Tnot f2 ->
            t_compare_alpha m1 m2 f1 f2

        | _ -> compare_tag t1.Term.t_node t2.Term.t_node
      end

  let compare (vl1,e1) (vl2,e2) =
    let m1 = tae_create () in
    let m2 = tae_create () in
    let cv v1 v2 = w3_ty_compare v1.Term.vs_ty v2.Term.vs_ty in
      compare2
        (lazy (List.compare cv vl1 vl2))
        (lazy (let m1 = vl_rename_alpha m1 vl1 in
               let m2 = vl_rename_alpha m2 vl2 in
                 t_compare_alpha m1 m2 e1 e2))
end

module Mta = EcMaps.Map.Make(Talpha)
module Sta = EcMaps.Set.Make(Talpha)
