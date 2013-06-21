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


let pvm = EcEnv.NormMp.norm_pvar

let get_restr env mp = 
  match (EcEnv.Mod.by_mpath mp env).me_body with
  | EcModules.ME_Decl(_,restr) -> restr 
  | _ -> assert false 

let uerror env c = 
  EcBaseLogic.tacuerror "%a" (pp_alias_clash env) c

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

module PV = struct 

  type t =  
    { s_pv : ty Mnpv.t; 
      s_gl : Sm.t;  (* only abstract module *)
    } 

  let empty = { s_pv = Mnpv.empty; s_gl = Sm.empty }

  let is_empty fv = Mnpv.is_empty fv.s_pv && Sm.is_empty fv.s_gl

  let add env pv ty fv = 
    { fv with s_pv = Mnpv.add (pvm env pv) ty fv.s_pv }

  let add_glob env mp fv = 
    let f = NormMp.norm_glob env mhr mp in
    let rec aux fv f = 
      match f.f_node with
      | Ftuple fs -> List.fold_left aux fv fs
      | Fpvar(pv,_) -> 
        { fv with s_pv = Mnpv.add (pvm env pv) f.f_ty fv.s_pv }
      | Fglob(mp,_) ->
        { fv with s_gl = Sm.add mp fv.s_gl}
      | _ -> assert false in
    aux fv f
      
  let remove env pv fv = 
    { fv with s_pv = Mnpv.remove (pvm env pv) fv.s_pv }
      
  let mem_pv env pv fv = Mnpv.mem (pvm env pv) fv.s_pv 
    
  (* We assume that mp is an abstract functor *)
  let mem_glob env mp fv = 
    ignore (get_restr env mp);
    Sm.mem mp fv.s_gl
    
  let union fv1 fv2 =
    { s_pv = Mnpv.merge 
        (fun _ o1 o2 -> if o2 = None then o1 else o2) fv1.s_pv fv2.s_pv;
      s_gl = Sm.union fv1.s_gl fv2.s_gl }

  let elements fv = Mnpv.bindings fv.s_pv, Sm.elements fv.s_gl

  let fv env m f =

    let remove b fv = 
      let do1 fv (id,gty) = 
        match gty with
        | GTmodty _ -> { fv with s_gl = Sm.remove (EcPath.mident id) fv.s_gl }
        | _ -> fv in
      List.fold_left do1 fv b in

    let rec aux env fv f = 
      match f.f_node with
      | Fquant(_,b,f1) -> 
        let env = Mod.add_mod_binding b env in
        let fv1 = aux env fv f1 in
        remove b fv1 
      | Fif(f1,f2,f3) -> aux env (aux env (aux env fv f1) f2) f3
      | Flet(_,f1,f2) -> aux env (aux env fv f1) f2
      | Fpvar(x,m') -> 
        if EcIdent.id_equal m m' then add env x f.f_ty fv else fv
      | Fglob (mp,m') ->
        if EcIdent.id_equal m m' then 
          let f' = NormMp.norm_glob env m mp in
          if f_equal f f' then add_glob env mp fv
          else aux env fv f'
        else fv
      | Fint _ | Flocal _ | Fop _ -> fv
      | Fapp(e, es) -> List.fold_left (aux env) (aux env fv e) es
      | Ftuple es   -> List.fold_left (aux env) fv es
      | FhoareF _  | FhoareS _ | FbdHoareF _  | FbdHoareS _ 
      | FequivF _ | FequivS _ | Fpr _ -> assert false 
    in
    aux env empty f

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

  let check_depend env fv mp = 
    try
      let restr = get_restr env mp in
      let check_v v _ = 
        if is_loc v then begin
          let ppe = EcPrinting.PPEnv.ofenv env in
          EcBaseLogic.tacuerror 
            "only global variable can be used in inv, %a is local"
            (EcPrinting.pp_pv ppe) v
        end;
        let top = EcPath.m_functor v.pv_name.x_top in
        if not (Sm.mem top restr) then
          raise (AliasClash (env,AC_concrete_abstract(mp,v,top))) in
      Mnpv.iter check_v fv.s_pv;
      let check_m mp' = 
        if not (Sm.mem mp' restr) then 
          let restr' = get_restr env mp' in
          if not (Sm.mem mp restr') then 
            raise (AliasClash(env,AC_abstract_abstract(mp,mp')))
      in            
      Sm.iter check_m fv.s_gl
    with AliasClash (env,c) -> uerror env c

  let diff fv1 fv2 = 
    { s_pv = Mnpv.set_diff fv1.s_pv fv2.s_pv;
      s_gl = Sm.diff fv1.s_gl fv2.s_gl }

  let interdep env fv1 fv2 = 
    let test_pv pv _ = 
      Mnpv.mem pv fv2.s_pv || 
        (is_glob pv && 
           let top = EcPath.m_functor pv.pv_name.x_top in
           let check1 mp = 
             let restr = get_restr env mp in
             Sm.mem top restr in
           Sm.exists check1 fv2.s_gl) in
    let test_mp mp = 
      let restr = get_restr env mp in
      let test_pv pv _ = 
        is_glob pv && 
          let top = EcPath.m_functor pv.pv_name.x_top in
          Sm.mem top restr in
      let test_mp mp' = Sm.mem mp' restr || Sm.mem mp (get_restr env mp') in
      Mnpv.exists test_pv fv2.s_pv || Sm.exists test_mp fv2.s_gl in

    { s_pv = Mnpv.filter test_pv fv1.s_pv;
      s_gl = Sm.filter test_mp fv1.s_gl }

  let indep env fv1 fv2 = 
    is_empty (interdep env fv1 fv2)
    
end
