(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcModules
open EcFol
open EcPV

(* -------------------------------------------------------------------- *)
(* Semantic sampling of a straight-line statement, shared by the [rndsem]
   rules of every logic: [s] (assignments and samplings only, no global
   write) is read as the single sampling [wr <$ D(s)] of the variables it
   writes, [D(s)] being [s] as nested [dlet] / [dunit]. *)
exception InvalidSemRnd

let semrnd env (mem : memenv) (used : PV.t option) (s : instr list) =
  let wr, gwr = PV.elements (is_write env s) in
  let wr =
    match used with
    | None -> wr
    | Some used -> List.filter (fun (pv, _) -> PV.mem_pv env pv used) wr in

  if not (List.is_empty gwr) then
    raise InvalidSemRnd;

  (* The written variables, in order of first write. *)
  let wr =
    let add (m, idx) pv =
      if   is_some (PVMap.find pv m)
      then (m, idx)
      else (PVMap.add pv idx m, idx+1) in

    let m, idx =
      List.fold_left (fun (m, idx) { i_node = i } ->
        match i with
        | Sasgn (lv, _) | Srnd (lv, _) ->
           List.fold_left add (m, idx) (lv_to_list lv)
        | _ -> (m, idx)
      )
      (PVMap.create env, 0) s in

    let m, _ =
      List.fold_left
        (fun (m, idx) (pv, _) -> add (m, idx) pv)
        (m, idx)
        wr in

    List.sort
      (fun (pv1, _) (pv2, _) ->
        compare (PVMap.find pv1 m) (PVMap.find pv2 m))
      wr in

  let rec do1 (m: memory) (subst : PVM.subst) (s : instr list) =
    match s with
    | [] ->
       let tuple =
         List.map (fun (pv, _) ->
           PVM.find env pv m subst) wr in
       {m;inv=f_dunit (f_tuple tuple)}

    | { i_node = Sasgn (lv, e) } :: s ->
       let e = ss_inv_of_expr m e in
       let e = map_ss_inv1 (PVM.subst env subst) e in
       let subst =
         match lv with
         | LvVar (pv, _) ->
            PVM.add env pv m e.inv subst
         | LvTuple pvs ->
            List.fold_lefti (fun subst i (pv, ty) ->
              PVM.add env pv m (f_proj e.inv i ty) subst
            ) subst pvs
       in
       do1 m subst s

    | { i_node = Srnd (lv, d) } :: s ->
       let d = ss_inv_of_expr m d in
       let d = map_ss_inv1 (PVM.subst env subst) d in
       let x = EcIdent.create (name_of_lv lv) in
       let subst, xty =
         match lv with
         | LvVar (pv, ty) ->
            let x = f_local x ty in
            (PVM.add env pv m x subst, ty)
         | LvTuple pvs ->
            let ty = ttuple (List.snd pvs) in
            let x = f_local x ty in
            let subst =
              List.fold_lefti (fun subst i (pv, ty) ->
                PVM.add env pv m (f_proj x i ty) subst
              ) subst pvs in
            (subst, ty)
       in
       let body = do1 m subst s in

       map_ss_inv2
       (f_dlet_simpl
         xty
         (ttuple (List.snd wr)))
         d
         (map_ss_inv1 (f_lambda [(x, GTty xty)]) body)

    | _ :: _ ->
       raise InvalidSemRnd

  in

  let mhr = EcIdent.create "&hr" in
  let distr = do1 mhr PVM.empty s in
  let distr = expr_of_ss_inv distr in

  match lv_of_list wr with
  | None ->
     let x =  { ov_name = Some "x"; ov_type = tunit; } in
     let mem, x = EcMemory.bind_fresh x mem in
     let x, xty = pv_loc (oget x.ov_name), x.ov_type in
     (mem, [i_rnd (LvVar (x, xty), distr)])
  | Some wr ->
     (mem, [i_rnd (wr, distr)])
