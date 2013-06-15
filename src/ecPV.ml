open EcIdent
open EcPath
open EcTypes
open EcModules
open EcFol
open EcEnv

module PVM = struct
  type mem_sel = 
  | MSvar of prog_var
  | MSmod of EcPath.mpath (* Only abstract module *)
      
  module M = EcMaps.Map.Make(struct
    (* We assume that the mpath are in normal form *) 
 
    type t = mem_sel * EcMemory.memory

    let ms_compare ms1 ms2 = 
      match ms1, ms2 with
      | MSvar v1, MSvar v2 -> pv_compare_p v1 v2
      | MSmod m1, MSmod m2 -> EcPath.m_compare m1 m2
      | MSvar _, MSmod _ -> -1
      | MSmod _, MSvar _ -> 1

    let compare (p1,m1) (p2,m2) = 
      let r = EcIdent.id_compare m1 m2 in
      if r = 0 then ms_compare p1 p2 
      else r
  end)

  type 'a subst = 'a M.t

  let empty = M.empty 

  let pvm env pv m = 
    let pv = EcEnv.NormMp.norm_pvar env pv in 
    (MSvar pv, m)

  let get_restr env mp = 
    match (EcEnv.Mod.by_mpath mp env).me_body with
    | EcModules.ME_Decl(_,restr) -> restr 
    | _ -> assert false 
    
  let check_pv env pv1 m s = 
    let pv = EcEnv.NormMp.norm_pvar env pv1 in 
    if is_glob pv then begin 
      let top = EcPath.m_functor pv.pv_name.x_top in
      let check1 k _ = 
        match k with 
        | (MSmod mp, m') when EcIdent.id_equal m m' ->
          let restr = get_restr env mp in
          if not (Sm.mem top restr) then
            let ppe = EcPrinting.PPEnv.ofenv env in
            EcBaseLogic.tacuerror 
              "The module %a can write %a (add restriction %a)"
              (EcPrinting.pp_topmod ppe) mp
              (EcPrinting.pp_pv ppe) pv1
              (EcPrinting.pp_topmod ppe) top
        | _ -> () in
      M.iter check1 s
    end;
    (MSvar pv, m)
    
  let add env pv m f s = 
    let pv = check_pv env pv m s in
    M.add pv f s 

  let add_glob env mp m f s = 
    let restr = get_restr env mp in
    let check1 k _ = 
      match k with 
      | (MSvar pv, m') when EcIdent.id_equal m m' ->
        let top = EcPath.m_functor pv.pv_name.x_top in
        if not (Sm.mem top restr) then
          let ppe = EcPrinting.PPEnv.ofenv env in
          EcBaseLogic.tacuerror 
            "The module %a can write %a (add restriction %a)"
            (EcPrinting.pp_topmod ppe) mp
            (EcPrinting.pp_pv ppe) pv
            (EcPrinting.pp_topmod ppe) top
      | (MSmod mp', m') when EcIdent.id_equal m m' ->
        if not (EcPath.m_equal mp mp') then
          if not (Sm.mem mp' restr) then
            let restr' = get_restr env mp' in
            if not (Sm.mem mp restr') then 
              let ppe = EcPrinting.PPEnv.ofenv env in
              EcBaseLogic.tacuerror 
                "The module %a can write %a (add restriction %a to %a, or %a to %a)"
                (EcPrinting.pp_topmod ppe) mp
                (EcPrinting.pp_topmod ppe) mp'
                (EcPrinting.pp_topmod ppe) mp
                (EcPrinting.pp_topmod ppe) mp' 
                (EcPrinting.pp_topmod ppe) mp'
                (EcPrinting.pp_topmod ppe) mp 
      | _ -> () in 
    M.iter check1 s;
    M.add (MSmod mp, m) f s

  let merge (s1 : 'a subst) (s2 : 'a subst) =
    (* TODO : should we check alias as in add_xxx *)
    M.merge (fun _ o1 o2 -> if o2 = None then o1 else o2) s1 s2

  let find env pv m s =
    M.find (pvm env pv m) s

  let check_binding m s = 
    M.iter (fun (_,m') f ->
      assert (not(EcIdent.id_equal m m') && 
              not (EcIdent.Mid.mem m f.f_fv))) s

  let subst env (s : form subst) = 
    Hf.memo_rec 107 (fun aux f ->
      match f.f_node with
      | Fpvar(pv,m) -> 
          (try find env pv m s with Not_found -> f)
      | Fglob(mp,m) ->
        let f' = EcEnv.NormMp.norm_glob env m mp in
        if f_equal f f' then
          (try M.find (MSmod mp,m) s with Not_found -> f)
        else aux f'
      | FequivF _ ->
        check_binding EcFol.mleft s;
        check_binding EcFol.mright s;
        EcFol.f_map (fun ty -> ty) aux f
      | FequivS es ->
        check_binding (fst es.es_ml) s;
        check_binding (fst es.es_mr) s;
        EcFol.f_map (fun ty -> ty) aux f
      | FhoareF _ | FbdHoareF _ ->
        check_binding EcFol.mhr s;
        EcFol.f_map (fun ty -> ty) aux f
      | FhoareS hs ->
        check_binding (fst hs.hs_m) s;
        EcFol.f_map (fun ty -> ty) aux f
      | FbdHoareS hs -> 
        check_binding (fst hs.bhs_m) s;
        EcFol.f_map (fun ty -> ty) aux f
      | Fpr(m,_,_,_) ->
        check_binding EcFol.mhr s;
        check_binding m s;
        EcFol.f_map (fun ty -> ty) aux f

      | _ -> EcFol.f_map (fun ty -> ty) aux f)

  let rec esubst env me (s : expr subst) e =
    match e.e_node with
    | Evar pv -> (try find env pv me s with Not_found -> e)
    | _ -> EcTypes.e_map (fun ty -> ty) (esubst env me s) e

  let rec isubst env me (s : expr subst) (i : instr) =
    let esubst = esubst env me s in
    let ssubst = ssubst env me s in

    match i.i_node with
    | Sasgn  (lv, e)     -> i_asgn   (lv, esubst e)
    | Srnd   (lv, e)     -> i_rnd    (lv, esubst e)
    | Scall  (lv, f, es) -> i_call   (lv, f, List.map esubst es)
    | Sif    (c, s1, s2) -> i_if     (esubst c, ssubst s1, ssubst s2)
    | Swhile (e, stmt)   -> i_while  (esubst e, ssubst stmt)
    | Sassert e          -> i_assert (esubst e)

  and issubst env me (s : expr subst) (is : instr list) =
    List.map (isubst env me s) is

  and ssubst env me (s : expr subst) (st : stmt) =
    stmt (issubst env me s st.s_node)

  let subst1 env pv m f = 
    let s = add env pv m f empty in
    subst env s
end

(* -------------------------------------------------------------------- *)
module PV = struct 
  module M = EcMaps.Map.Make (struct
    (* We assume that the mpath are in normal form *)  
    type t = prog_var 
    let compare = pv_compare_p
  end)

  type pv_fv = 
    { pv : ty M.t;         (* The key are in normal form *)
      glob : EcPath.Sm.t;  (* The set of abstract module *)
    }

  let empty = 
    { pv = M.empty;
      glob = EcPath.Sm.empty }

  let is_empty pv = 
    M.is_empty pv.pv && EcPath.Sm.is_empty pv.glob

  let add env pv ty fv = 
    { fv with pv = M.add (NormMp.norm_pvar env pv) ty fv.pv }

  let add_glob env mp fv =
    { fv with glob = EcPath.Sm.add (NormMp.norm_mpath env mp) fv.glob}

  let remove env pv fv =
    { fv with pv = M.remove (NormMp.norm_pvar env pv) fv.pv }

  let union _env fv1 fv2 =
    { pv = M.merge (fun _ o1 o2 -> if o2 = None then o1 else o2) fv1.pv fv2.pv;
      glob = EcPath.Sm.union fv1.glob fv2.glob }

  let disjoint _env fv1 fv2 = 
    M.set_disjoint fv1.pv fv2.pv &&
      (* FIXME not suffisant use disjoint_g *)
      EcPath.Sm.disjoint fv1.glob fv2.glob

  let diff _env fv1 fv2 = 
    { pv = M.set_diff fv1.pv fv2.pv;
      glob = EcPath.Sm.diff fv1.glob fv2.glob }

  let inter _env fv1 fv2 = 
    { pv = M.set_inter fv1.pv fv2.pv;
      glob = EcPath.Sm.inter fv1.glob fv2.glob }

  let elements fv = M.bindings fv.pv, EcPath.Sm.elements fv.glob (* FIXME *)

  let mem_pv pv fv = M.mem pv fv.pv 

  let mem_glob mp fv = EcPath.Sm.mem mp fv.glob

  let fv env m f =
    let rec aux fv f = 
      match f.f_node with
      | Fquant(_,_,f1) -> aux fv f1
      | Fif(f1,f2,f3) -> aux (aux (aux fv f1) f2) f3
      | Flet(_,f1,f2) -> aux (aux fv f1) f2
      | Fpvar(x,m') -> 
        if EcIdent.id_equal m m' then add env x f.f_ty fv else fv
      | Fglob (mp,m') ->
        if EcIdent.id_equal m m' then 
          let f' = EcEnv.NormMp.norm_glob env m mp in
          if f_equal f f' then add_glob env mp fv
          else aux fv f'
        else fv
      | Fint _ | Flocal _ | Fop _ -> fv
      | Fapp(e, es) -> List.fold_left aux (aux fv e) es
      | Ftuple es   -> List.fold_left aux fv es
      | FhoareF _  | FhoareS _ | FbdHoareF _  | FbdHoareS _ 
      | FequivF _ | FequivS _ | Fpr _ -> assert false 
    in
    aux empty f

  let pp env fmt fv =
    let ppe = EcPrinting.PPEnv.ofenv env in
    let vs,gs = elements fv in
    let pp_vs fmt (pv,_) = EcPrinting.pp_pv ppe fmt pv in
    if gs = [] then 
      Format.fprintf fmt "@[%a@]"
        (EcPrinting.pp_list ",@ " pp_vs) vs
    else Format.fprintf fmt "@[%a,@ %a@]"
      (EcPrinting.pp_list ",@ " pp_vs) vs
      (EcPrinting.pp_list ",@ " (EcPrinting.pp_topmod ppe)) gs

  let disjoint_g env mp1 mp2 = 
    let me1, me2 = EcEnv.Mod.by_mpath mp1 env, EcEnv.Mod.by_mpath mp2 env in
    match me1.me_body, me2.me_body with
    | ME_Decl(_,nu1), ME_Decl(_,nu2) ->
      EcPath.Sm.mem mp2 nu1 || EcPath.Sm.mem mp1 nu2
    | ME_Decl(_,nu1), ME_Structure ms2 ->
      EcPath.Sm.mem mp2 nu1 &&
        EcPath.Sm.for_all (fun m -> EcPath.Sm.mem m nu1) ms2.ms_uses
    | ME_Structure ms1, ME_Decl(_,nu2) ->
      EcPath.Sm.mem mp1 nu2 &&
        EcPath.Sm.for_all (fun m -> EcPath.Sm.mem m nu2) ms1.ms_uses
    | ME_Structure ms1, ME_Structure ms2 ->
      let us1 = EcPath.Sm.add mp1 ms1.ms_uses in
      let us2 = EcPath.Sm.add mp2 ms2.ms_uses in
      EcPath.Sm.disjoint us1 us2 
    | _, _ -> assert false 
      
  let check env modi fv = 
    let not_gen = diff env fv modi in 
    let mk_topv s = 
      M.fold (fun x _ topv ->
        if is_loc x then topv 
        else
          let x=x.pv_name in
          let top = EcPath.m_functor x.EcPath.x_top in
          EcPath.Sm.add top topv) s EcPath.Sm.empty in
    let topv = mk_topv not_gen.pv in
    let topvg = mk_topv modi.pv in
    let topm = not_gen.glob in
    
    let check s1 s2 = 
      EcPath.Sm.for_all (fun mp1 ->
        EcPath.Sm.for_all (fun mp2 -> disjoint_g env mp1 mp2) s1) s2 in

    (* FIXME error message *)
    assert (check modi.glob topv);
    assert (check modi.glob topm);
    assert (check topvg topm)
      
end
