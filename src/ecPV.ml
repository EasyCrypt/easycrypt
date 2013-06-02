open EcIdent
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

  type subst = form M.t

  let empty = M.empty 

  let pvm env pv m = 
    let pv = EcEnv.NormMp.norm_pvar env pv in 
    (MSvar pv, m)

  let add env pv m f s = M.add (pvm env pv m) f s 

  let add_glob _env mp m f s = M.add (MSmod mp, m) f s

  let add_none env pv m f s =
    M.change (fun o -> if o = None then Some f else o) (pvm env pv m) s

  let merge (s1:subst) (s2:subst) =
    M.merge (fun _ o1 o2 -> if o2 = None then o1 else o2) s1 s2

  let find env pv m s =
    M.find (pvm env pv m) s

  let subst env (s:subst) = 
    Hf.memo_rec 107 (fun aux f ->
      match f.f_node with
      | Fpvar(pv,m) -> 
          (try find env pv m s with Not_found -> f)
      | Fglob(mp,m) ->
        let f' = EcEnv.NormMp.norm_glob env m mp in
        if f_equal f f' then
          (try M.find (MSmod mp,m) s with Not_found -> f)
        else aux f'
      | FhoareF _ | FhoareS _ | FequivF _ | FequivS _ | Fpr _ -> assert false
      | _ -> EcFol.f_map (fun ty -> ty) aux f)

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
      
  let check_depend env fv mp = 
    (* FIXME error message *)
    let check_v v _ty =
      assert (is_glob v);
      let top = EcPath.m_functor v.pv_name.EcPath.x_top in
      assert (disjoint_g env mp top) in
    M.iter check_v fv.pv;
    let check_m m = assert (disjoint_g env mp m) in
    EcPath.Sm.iter check_m fv.glob 

end
