(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcPath
open EcTypes
open EcModules
open EcFol
open EcEnv

(* -------------------------------------------------------------------- *)

type alias_clash = 
 | AC_concrete_abstract of mpath * prog_var * mpath
 | AC_abstract_abstract of mpath * mpath

exception AliasClash of env * alias_clash 

let pp_alias_clash env fmt = function
  | AC_concrete_abstract(mp,npv,top) ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    Format.fprintf fmt 
      "The module %a can write %a (add restriction %a)"
      (EcPrinting.pp_topmod ppe) mp
      (EcPrinting.pp_pv ppe) npv
      (EcPrinting.pp_topmod ppe) top
  | AC_abstract_abstract(mp,mp') ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    Format.fprintf fmt 
      "The module %a can write %a (add restriction %a to %a, or %a to %a)"
      (EcPrinting.pp_topmod ppe) mp
      (EcPrinting.pp_topmod ppe) mp'
      (EcPrinting.pp_topmod ppe) mp
      (EcPrinting.pp_topmod ppe) mp' 
      (EcPrinting.pp_topmod ppe) mp'
      (EcPrinting.pp_topmod ppe) mp 

let _ = EcPException.register (fun fmt exn ->
  match exn with
  | AliasClash(env, ac) -> pp_alias_clash env fmt ac
  | _ -> raise exn)


module Mnpv = 
  EcMaps.Map.Make(struct
     (* We assume that the mpath are in normal form *) 
    type t = prog_var 
    let compare = pv_compare_p 
  end)

module Mpv = struct
  type ('a, 'b) t = 
    { s_pv : 'a Mnpv.t; 
      s_gl : 'b Mm.t;  (* only abstract module *)
    } 

  let empty = { s_pv = Mnpv.empty; s_gl = Mm.empty }

  let pvm = EcEnv.NormMp.norm_pvar

  let get_restr env mp = 
    match (EcEnv.Mod.by_mpath mp env).me_body with
    | EcModules.ME_Decl(_,restr) -> restr 
    | _ -> assert false 

  let check_npv_mp env npv top mp restr = 
    if not (Sm.mem top restr) then 
      raise (AliasClash (env,AC_concrete_abstract(mp,npv,top)))
    
  let check_npv env npv m = 
    if is_glob npv then 
      let top = EcPath.m_functor npv.pv_name.x_top in
      let check1 mp _ = 
        let restr = get_restr env mp in
        check_npv_mp env npv top mp restr in
      Mm.iter check1 m.s_gl

  let add env pv f m = 
    let pv = pvm env pv in
    check_npv env pv m;
    { m with s_pv = Mnpv.add pv f m.s_pv }

  let find env pv m =
    let pv = pvm env pv in
    try Mnpv.find pv m.s_pv
    with Not_found -> check_npv env pv m; raise Not_found 

  let check_mp_mp env mp restr mp' = 
    if not (EcPath.m_equal mp mp') && not (Sm.mem mp' restr) then
      let restr' = get_restr env mp' in
      if not (Sm.mem mp restr') then 
        raise (AliasClash(env,AC_abstract_abstract(mp,mp')))

  let check_glob env mp m =
    let restr = get_restr env mp in
    let check npv _ =
      if is_glob npv then 
        let top = EcPath.m_functor npv.pv_name.x_top in
        check_npv_mp env npv top mp restr in
    Mnpv.iter check m.s_pv;
    let check mp' _ = check_mp_mp env mp restr mp' in
    Mm.iter check m.s_gl

  let add_glob env mp f m = 
    check_glob env mp m;
    { m with s_gl = Mm.add mp f m.s_gl }

  let find_glob env mp m =
    try Mm.find mp m.s_gl
    with Not_found ->
      check_glob env mp m;
      raise Not_found 

  type esubst = (expr, unit) t

  let rec esubst env (s : esubst) e =
    match e.e_node with
    | Evar pv -> (try find env pv s with Not_found -> e)
    | _ -> EcTypes.e_map (fun ty -> ty) (esubst env s) e

  let rec isubst env (s : esubst) (i : instr) =
    let esubst = esubst env s in
    let ssubst = ssubst env s in

    match i.i_node with
    | Sasgn  (lv, e)     -> i_asgn   (lv, esubst e)
    | Srnd   (lv, e)     -> i_rnd    (lv, esubst e)
    | Scall  (lv, f, es) -> i_call   (lv, f, List.map esubst es)
    | Sif    (c, s1, s2) -> i_if     (esubst c, ssubst s1, ssubst s2)
    | Swhile (e, stmt)   -> i_while  (esubst e, ssubst stmt)
    | Sassert e          -> i_assert (esubst e)

  and issubst env (s : esubst) (is : instr list) =
    List.map (isubst env s) is

  and ssubst env (s : esubst) (st : stmt) =
    stmt (issubst env s st.s_node)

end

module PVM = struct

  type subst = (form, form) Mpv.t Mid.t

  let empty = Mid.empty 

  let pvm = EcEnv.NormMp.norm_pvar

  let get_restr env mp = 
    match (EcEnv.Mod.by_mpath mp env).me_body with
    | EcModules.ME_Decl(_,restr) -> restr 
    | _ -> assert false 

  let uerror env c = 
    EcBaseLogic.tacuerror "%a" (pp_alias_clash env) c
    
  let add env pv m f s = 
    try Mid.change (fun o -> Some (Mpv.add env pv f (odfl Mpv.empty o))) m s
    with AliasClash (env,c) -> uerror env c

  let find env pv m s =
    try Mpv.find env pv (Mid.find m s)
    with AliasClash (env,c) -> uerror env c

  let add_glob env mp m f s = 
    try Mid.change (fun o -> Some (Mpv.add_glob env mp f (odfl Mpv.empty o))) m s
    with AliasClash (env,c) -> uerror env c

  let find_glob env mp m s =
    try Mpv.find_glob env mp (Mid.find m s)
    with AliasClash (env,c) -> uerror env c

  let check_binding m s = assert (not (Mid.mem m s))

  let has_mod b = 
    List.exists (fun (_,gty) -> match gty with GTmodty _ -> true | _ -> false) b

  let rec subst env (s : subst) = 
    Hf.memo_rec 107 (fun aux f ->
      match f.f_node with
      | Fpvar(pv,m) -> 
          (try find env pv m s with Not_found -> f)
      | Fglob(mp,m) ->
        let f' = EcEnv.NormMp.norm_glob env m mp in
        if f_equal f f' then
          (try find_glob env mp m s with Not_found -> f)
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
      | Fquant(q,b,f1) ->
        let f1 = 
          if has_mod b then subst (Mod.add_mod_binding b env) s f1
          else aux f1 in
        f_quant q b f1 

      | _ -> EcFol.f_map (fun ty -> ty) aux f)

  let subst1 env pv m f = 
    let s = add env pv m f empty in
    subst env s
end

(* -------------------------------------------------------------------- *)
(* TODO set the type pv_fv abstract *)
(* TODO use the module Mpv instead *)
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
