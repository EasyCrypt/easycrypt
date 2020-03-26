(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
 | AC_concrete_abstract of mpath * prog_var
 | AC_abstract_abstract of mpath * mpath

exception AliasClash of env * alias_clash

let pvm = EcEnv.NormMp.norm_pvar

let uerror env c =
  EcCoreGoal.tacuerror_exn (AliasClash (env, c))

module Mnpv =
  EcMaps.Map.Make(struct
    (* We assume that the mpath are in normal form *)
    type t = prog_var
    let compare = pv_compare_p
  end)

module Snpv = EcMaps.Set.MakeOfMap(Mnpv)

(* -------------------------------------------------------------------- *)
module PVMap = struct
  type 'a t = {
    pvm_env : EcEnv.env;
    pvm_map : 'a Mnpv.t;
  }

  let create (env : EcEnv.env) =
    { pvm_env = env; pvm_map = Mnpv.empty; }

  let add k v m =
    { m with pvm_map =
        Mnpv.add (pvm m.pvm_env k) v m.pvm_map; }

  let find k m =
    Mnpv.find_opt (pvm m.pvm_env k) m.pvm_map

  let raw m = m.pvm_map
end

(* -------------------------------------------------------------------- *)
module Mpv = struct
  type ('a, 'b) t =
    { s_pv : 'a Mnpv.t;
      s_gl : (EcEnv.use * 'b) Mm.t;  (* only abstract module *)
    }

  let empty = { s_pv = Mnpv.empty; s_gl = Mm.empty }

  let check_npv_mp env npv mp restr =
    if not (NormMp.use_mem_xp npv.pv_name restr) then
      raise (AliasClash (env,AC_concrete_abstract(mp,npv)))

  let check_npv env npv m =
    if is_glob npv then
      let check1 mp (restr,_) =  check_npv_mp env npv mp restr in
      Mm.iter check1 m.s_gl

  let add env pv f m =
    let pv = pvm env pv in
    check_npv env pv m;
    { m with s_pv = Mnpv.add pv f m.s_pv }

  let find env pv m =
    let pv = pvm env pv in
    try Mnpv.find pv m.s_pv
    with Not_found -> check_npv env pv m; raise Not_found

  let check_mp_mp env mp restr mp' restr' =
    if not (EcPath.m_equal mp mp') &&
      not (NormMp.use_mem_gl mp' restr) then
      if not (NormMp.use_mem_gl mp restr') then
        raise (AliasClash(env,AC_abstract_abstract(mp,mp')))

  let check_glob env mp m =
    let restr = NormMp.get_restr env mp in
    let check npv _ =
      if is_glob npv then
        check_npv_mp env npv mp restr in
    Mnpv.iter check m.s_pv;
    let check mp' (restr',_) = check_mp_mp env mp restr mp' restr' in
    Mm.iter check m.s_gl

  let add_glob env mp f m =
    check_glob env mp m;
    { m with s_gl = Mm.add mp (NormMp.get_restr env mp, f) m.s_gl }

  let find_glob env mp m =
    try snd (Mm.find mp m.s_gl)
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
    | Sabstract _        -> i

  and issubst env (s : esubst) (is : instr list) =
    List.map (isubst env s) is

  and ssubst env (s : esubst) (st : stmt) =
    stmt (issubst env s st.s_node)

end

exception MemoryClash

module PVM = struct
  type subst = (form, form) Mpv.t Mid.t

  let empty = Mid.empty

  let of_mpv s m = Mid.singleton m s

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


  let check_binding m s =
    if (Mid.mem m s) then raise MemoryClash

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
      | Fpr pr ->
        check_binding pr.pr_mem s;
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

  let pick fv =
    try  Some (`Global (Sm.choose fv.s_gl))
    with Not_found ->
      try  Some (`PV (fst (Mnpv.choose fv.s_pv)))
      with Not_found -> None

  let global fv =
    { fv with s_pv = Mnpv.filter (fun pv _ -> is_glob pv) fv.s_pv }

  let local fv =
    { s_pv = Mnpv.filter (fun pv _ -> is_loc pv) fv.s_pv;
      s_gl = Sm.empty }

  let subset fv1 fv2 =
    Mnpv.submap (fun _ _ _ -> true) fv1.s_pv fv2.s_pv &&
      Sm.subset fv1.s_gl fv2.s_gl

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

  (* Works only for abstract module *)
  let remove_glob mp fv =
    { fv with s_gl = Sm.remove mp fv.s_gl }

  let mem_pv env pv fv = Mnpv.mem (pvm env pv) fv.s_pv

  (* We assume that mp is an abstract functor *)
  let mem_glob env mp fv =
    ignore (NormMp.get_restr env mp);
    Sm.mem mp fv.s_gl

  let union fv1 fv2 =
    { s_pv = Mnpv.merge
        (fun _ o1 o2 -> if o2 = None then o1 else o2) fv1.s_pv fv2.s_pv;
      s_gl = Sm.union fv1.s_gl fv2.s_gl }

  let elements fv =
    (Mnpv.bindings fv.s_pv, Sm.elements fv.s_gl)

  let ntr_elements fv =
    let xs, gs = elements fv in
    (List.ksort ~key:fst ~cmp:pv_ntr_compare xs,
     List.ksort ~key:identity ~cmp:m_ntr_compare gs)

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
      | Fif(f1,f2,f3) -> List.fold_left (aux env) fv [f1;f2;f3]
      | Fmatch(b,bs,_) -> List.fold_left (aux env) fv (b::bs)
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
      | Fproj(e,_)  -> aux env fv e
      | FhoareF _  | FhoareS _ | FbdHoareF _  | FbdHoareS _
      | FequivF _ | FequivS _ | FeagerF _ | Fpr _ -> assert false
    in
    aux env empty f

  let pp env fmt fv =
    let ppe = EcPrinting.PPEnv.ofenv env in
    let vs,gs = ntr_elements fv in
    let pp_vs fmt (pv,_) = EcPrinting.pp_pv ppe fmt pv in
    let pp_gl fmt mp =
      Format.fprintf fmt "(glob %a)" (EcPrinting.pp_topmod ppe) mp in

    begin
      if vs = [] || gs = [] then
        Format.fprintf fmt "@[%a%a@]"
          (EcPrinting.pp_list ",@ " pp_vs) vs
          (EcPrinting.pp_list ",@ " pp_gl) gs
      else
        Format.fprintf fmt "@[%a,@ %a@]"
          (EcPrinting.pp_list ",@ " pp_vs) vs
          (EcPrinting.pp_list ",@ " pp_gl) gs
    end

  let check_depend env fv mp =
    try
      let restr = NormMp.get_restr env mp in
      let check_v v _ =
        if is_loc v then begin
          let ppe = EcPrinting.PPEnv.ofenv env in
          EcCoreGoal.tacuerror
            "only global variable can be used in inv, %a is local"
            (EcPrinting.pp_pv ppe) v
        end;
        Mpv.check_npv_mp env v mp restr in
      Mnpv.iter check_v fv.s_pv;
      let check_m mp' =
        if not (NormMp.use_mem_gl mp' restr) then
          let restr' = NormMp.get_restr env mp' in
          if not (NormMp.use_mem_gl mp restr') then
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
           let check1 mp =
             let restr = NormMp.get_restr env mp in
             not (NormMp.use_mem_xp pv.pv_name restr) in
           Sm.exists check1 fv2.s_gl) in
    let test_mp mp =
      let restr = NormMp.get_restr env mp in
      let test_pv pv _ =
        is_glob pv &&
          not (NormMp.use_mem_xp pv.pv_name restr) in
      let test_mp mp' =
        not (NormMp.use_mem_gl mp' restr ||
             NormMp.use_mem_gl mp (NormMp.get_restr env mp')) in
      Mnpv.exists test_pv fv2.s_pv || Sm.exists test_mp fv2.s_gl in

    { s_pv = Mnpv.filter test_pv fv1.s_pv;
      s_gl = Sm.filter test_mp fv1.s_gl }

  let indep env fv1 fv2 =
    is_empty (interdep env fv1 fv2)

  let iter fpv fm fv =
    Mnpv.iter fpv fv.s_pv;
    Sm.iter fm fv.s_gl

  let check_notmod env pv fv =
    if mem_pv env pv fv then false
    else
      try
        if is_glob pv then begin
          let pv = EcEnv.NormMp.norm_pvar env pv in
          let check1 mp =
            let restr = NormMp.get_restr env mp in
            Mpv.check_npv_mp env pv mp restr in
          Sm.iter check1 fv.s_gl
        end;
        true
      with _ -> false

end

(* -------------------------------------------------------------------- *)
let get_abs_functor f =
  let f = f.EcPath.x_top in
  match f.EcPath.m_top with
  | `Local _ -> EcPath.mpath (f.EcPath.m_top) []
  | _ -> assert false

(* -------------------------------------------------------------------- *)
type 'a pvaccess = env -> PV.t -> 'a -> PV.t

(* -------------------------------------------------------------------- *)
let lp_write_r env w lp =
  let add w (pv, ty) = PV.add env pv ty w in
  match lp with
  | LvVar pv ->
      add w pv
  | LvTuple pvs ->
      List.fold_left add w pvs

let rec f_write_r ?(except=Sx.empty) env w f =
  let f    = NormMp.norm_xfun env f in
  let func = Fun.by_xpath f env in

  let folder w o =
    if Sx.mem o except then w else f_write_r ~except env w o in

  match func.f_def with
  | FBalias _ ->
      (* [f] is in normal-form *)
      assert false

  | FBabs oi ->
      let mp = get_abs_functor f in
      List.fold_left folder (PV.add_glob env mp w) oi.oi_calls

  | FBdef fdef ->
      let add x w =
        let vb = Var.by_xpath x env in
        PV.add env (pv_glob x) vb.vb_type w in
      List.fold_left folder
        (EcPath.Sx.fold add fdef.f_uses.us_writes w )
        fdef.f_uses.us_calls

and is_write_r ?(except=Sx.empty) env w s =
  List.fold_left (i_write_r ~except env) w s

and s_write_r ?(except=Sx.empty) env w s =
  is_write_r ~except env w s.s_node

and i_write_r ?(except=Sx.empty) env w i =
  match i.i_node with
  | Sasgn  (lp, _) -> lp_write_r env w lp
  | Srnd   (lp, _) -> lp_write_r env w lp
  | Sassert _      -> w

  | Scall(lp,f,_) ->
    if Sx.mem f except then w else
      let w  = match lp with None -> w | Some lp -> lp_write_r env w lp in
      f_write_r ~except env w f

  | Sif (_, s1, s2) ->
      List.fold_left (s_write_r ~except env) w [s1; s2]

  | Swhile (_, s) ->
      s_write_r ~except env w s

  | Sabstract id ->
      let us = AbsStmt.byid id env in
      let add_pv w (pv,ty) = PV.add env pv ty w in
      let w = List.fold_left add_pv w us.EcModules.aus_writes in
      List.fold_left (f_write_r ~except env) w us.EcModules.aus_calls

(* -------------------------------------------------------------------- *)
let rec f_read_r env r f =
  let f    = NormMp.norm_xfun env f in
  let func = Fun.by_xpath f env in

  match func.f_def with
  | FBalias _ ->
      (* [f] is in normal form *)
      assert false

  | FBabs oi ->
      let mp = get_abs_functor f in
      let r = if oi.oi_in then (PV.add_glob env mp r) else r in
      List.fold_left (f_read_r env) r oi.oi_calls

  | FBdef fdef ->
      let add x r =
        let vb = Var.by_xpath x env in
        PV.add env (pv_glob x) vb.vb_type r in
      let r = EcPath.Sx.fold add fdef.f_uses.us_reads r in
      List.fold_left (f_read_r env) r fdef.f_uses.us_calls

let rec e_read_r env r e =
  match e.e_node with
  | Evar pv -> PV.add env pv e.e_ty r
  | _ -> e_fold (e_read_r env) r e

let rec is_read_r env w s =
  List.fold_left (i_read_r env) w s

and s_read_r env w s =
  is_read_r env w s.s_node

and i_read_r env r i =
  match i.i_node with
  | Sasgn   (_lp, e) -> e_read_r env r e
  | Srnd    (_lp, e) -> e_read_r env r e
  | Sassert e       -> e_read_r env r e

  | Scall (_lp, f, es) ->
      let r = List.fold_left (e_read_r env) r es in
      f_read_r env r f

  | Sif (e, s1, s2) ->
      List.fold_left (s_read_r env) (e_read_r env r e) [s1; s2]

  | Swhile (e, s) ->
      s_read_r env (e_read_r env r e) s

  | Sabstract id ->
      let us = AbsStmt.byid id env in
      let add_pv r (pv,ty) = PV.add env pv ty r in
      let r = List.fold_left add_pv r us.EcModules.aus_reads in
      List.fold_left (f_read_r env) r us.EcModules.aus_calls

(* -------------------------------------------------------------------- *)
type 'a pvaccess0 = env -> 'a -> PV.t

let i_write  ?(except=Sx.empty) env i  = i_write_r  ~except env PV.empty i
let is_write ?(except=Sx.empty) env is = is_write_r ~except env PV.empty is
let s_write  ?(except=Sx.empty) env s  = s_write_r  ~except env PV.empty s
let f_write  ?(except=Sx.empty) env f  = f_write_r  ~except env PV.empty f

let e_read  env e  = e_read_r  env PV.empty e
let i_read  env i  = i_read_r  env PV.empty i
let is_read env is = is_read_r env PV.empty is
let s_read  env s  = s_read_r  env PV.empty s
let f_read  env f  = f_read_r  env PV.empty f

(* -------------------------------------------------------------------- *)
exception EqObsInError

module Mpv2 = struct
  type t = {
    s_pv : (Snpv.t * ty) Mnpv.t;
    s_gl : Sm.t;
  }

  let empty = { s_pv = Mnpv.empty; s_gl = Sm.empty }

  let add env ty pv1 pv2 eqs =
    let pv1 = pvm env pv1 in
    let pv2 = pvm env pv2 in
    { eqs with
      s_pv =
        Mnpv.change (fun o ->
          match o with
          | None -> Some (Snpv.singleton pv2, ty)
          | Some(s,ty) -> Some (Snpv.add pv2 s, ty))
          pv1 eqs.s_pv }

  let add_glob env mp1 mp2 eqs =
    let mp1, mp2 = NormMp.norm_mpath env mp1, NormMp.norm_mpath env mp2 in
    (* FIXME error message *)
    if not (EcPath.m_equal mp1 mp2) then assert false;
    if not (mp1.m_args = []) then assert false;
    begin match mp1.m_top with
    | `Local _ -> ()
    | _ -> assert false
    end;
    { eqs with s_gl = Sm.add mp1 eqs.s_gl }


  let remove env pv1 pv2 eqs =
    let pv1 = pvm env pv1 in
    let pv2 = pvm env pv2 in
    { eqs with
      s_pv =
        Mnpv.change (function
        | None ->  None
        | Some (s,_) ->
          let s = Snpv.remove pv2 s in
          if Snpv.is_empty s then None else raise EqObsInError)
          pv1 eqs.s_pv }

  let remove_glob mp eqs =
    begin match mp.m_top with
    | `Local _ -> ()
    | _ -> assert false
    end;
    { eqs with
      s_gl = Sm.remove mp eqs.s_gl }

  let union eqs1 eqs2 =
    { s_pv =
        Mnpv.union (fun _ (s1,ty) (s2,_) -> Some (Snpv.union s1 s2, ty))
          eqs1.s_pv eqs2.s_pv;
      s_gl = Sm.union eqs1.s_gl eqs2.s_gl }

  let subset eqs1 eqs2 =
    Mnpv.submap (fun _ (s1,_) (s2,_) ->
      Snpv.subset s1 s2) eqs1.s_pv eqs2.s_pv &&
    Sm.subset eqs1.s_gl eqs2.s_gl

  let equal eqs1 eqs2 =
    Mnpv.equal (fun (s1,_) (s2,_) -> Snpv.equal s1 s2) eqs1.s_pv eqs2.s_pv &&
    Sm.equal eqs1.s_gl eqs2.s_gl

  let is_mod_pv env pv mod_ =
    if Mnpv.mem pv mod_.PV.s_pv then true
    else
      if is_glob pv then
        let x = pv.pv_name in
        let check_mp mp =
          let restr = NormMp.get_restr env mp in
          not (EcPath.Mx.mem x restr.us_pv) in
        Sm.exists check_mp mod_.PV.s_gl
      else false

  let is_mod_mp env mp mod_ =
    let id = EcPath.mget_ident mp in
    let restr = NormMp.get_restr env mp in
    let check_v pv _ty =
      let x = pv.pv_name in
      not (EcPath.Mx.mem x restr.us_pv) in
    let check_mp mp' =
      not (Sid.mem (EcPath.mget_ident mp') restr.us_gl ||
           Sid.mem id (NormMp.get_restr env mp').us_gl) in
    Mnpv.exists check_v mod_.PV.s_pv ||
    Sm.exists check_mp mod_.PV.s_gl


  let split_nmod env modl modr eqo =
    { s_pv =
        Mnpv.mapi_filter (fun pvl (s,ty) ->
          if is_mod_pv env pvl modl then None
          else
            let s =
              Snpv.filter (fun pvr -> not (is_mod_pv env pvr modr)) s in
            if Snpv.is_empty s then None else Some (s,ty)) eqo.s_pv;
      s_gl =
        Sm.filter
          (fun m -> not (is_mod_mp env m modl) && not (is_mod_mp env m modr))
          eqo.s_gl }

  let split_mod env modl modr eqo =
    { s_pv =
        Mnpv.mapi_filter (fun pvl (s,ty) ->
          if is_mod_pv env pvl modl then Some (s,ty)
          else
            let s =
              Snpv.filter (fun pvr -> is_mod_pv env pvr modr) s in
            if Snpv.is_empty s then None else Some (s,ty)) eqo.s_pv;
      s_gl =
        Sm.filter (fun m -> is_mod_mp env m modl || is_mod_mp env m modr)
          eqo.s_gl }

  let subst_l env xl x eqs =
    let xl = pvm env xl in
    let x = pvm env x in
    if pv_equal xl x then eqs
    else match Mnpv.find_opt xl eqs.s_pv with
    | None -> eqs
    | Some (s,ty) ->
      { eqs with
        s_pv =
          Mnpv.change (fun o ->
            match o with
            | None -> Some (s,ty)
            | Some(s',_) -> Some (Snpv.union s s', ty))
            x (Mnpv.remove xl eqs.s_pv) }

  let substs_l env xls xs eqs =
    List.fold_left2 (fun eqs (xl,_) x -> subst_l env xl x eqs) eqs xls xs

  let subst_r env xl x eqs =
    let xl = pvm env xl in
    let x = pvm env x in
    if pv_equal xl x then eqs
    else
      { eqs with
        s_pv = Mnpv.map (fun (s,ty) ->
          Snpv.fold (fun x' s ->
            let x' = if pv_equal xl x' then x else x' in
            Snpv.add x' s) s Snpv.empty, ty) eqs.s_pv }

  let substs_r env xrs xs eqs =
    List.fold_left2 (fun eqs (xr,_) x -> subst_r env xr x eqs) eqs xrs xs

  let mem_pv_l env x eqs =
    let x = pvm env x in
    match Mnpv.find_opt x eqs.s_pv with
    | None -> false
    | Some (s,_) -> not (Snpv.is_empty s)

  let mem_pv_r env x eqs =
    let x = pvm env x in
    Mnpv.exists (fun _ (s,_) -> Snpv.mem x s) eqs.s_pv

  let to_form ml mr eqs inv =
    let l =
      Sm.fold (fun m l -> f_eqglob m ml m mr :: l) eqs.s_gl [] in
    let l =
      Mnpv.fold (fun pvl (s,ty) l ->
        Snpv.fold (fun pvr l -> f_eq (f_pvar pvl ty ml) (f_pvar pvr ty mr) :: l)
          s l) eqs.s_pv l in
    f_and_simpl (f_ands l) inv

  let of_form env ml mr f =
    let rec aux f eqs =
      match sform_of_form f with
      | SFtrue -> eqs
      | SFeq ({f_node = Fpvar(pvl,ml');f_ty = ty}, { f_node = Fpvar(pvr,mr') })
          when EcIdent.id_equal ml ml' && EcIdent.id_equal mr mr' ->
        add env ty pvl pvr eqs
      | SFeq ({ f_node = Fpvar(pvr,mr')},{f_node = Fpvar(pvl,ml');f_ty = ty})
          when EcIdent.id_equal ml ml' && EcIdent.id_equal mr mr' ->
        add env ty pvl pvr eqs
      | SFeq(({f_node = Fglob(mpl, ml')} as f1),
             ({f_node = Fglob(mpr, mr')} as f2))
          when EcIdent.id_equal ml ml' && EcIdent.id_equal mr mr' ->
        let f1' = NormMp.norm_glob env ml mpl in
        let f2' = NormMp.norm_glob env mr mpr in
        if f_equal f1 f1' && f_equal f2 f2' then add_glob env mpl mpr eqs
        else aux (f_eq f1' f2') eqs
      | SFeq(({f_node = Fglob(mpr, mr')} as f2),
             ({f_node = Fglob(mpl, ml')} as f1))
          when EcIdent.id_equal ml ml' && EcIdent.id_equal mr mr' ->
        let f1' = NormMp.norm_glob env ml mpl in
        let f2' = NormMp.norm_glob env mr mpr in
        if f_equal f1 f1' && f_equal f2 f2' then add_glob env mpl mpr eqs
        else aux (f_eq f1' f2') eqs
      | SFeq({f_node = Ftuple fs1}, {f_node = Ftuple fs2}) ->
        List.fold_left2 (fun eqs f1 f2 -> aux (f_eq f1 f2) eqs) eqs fs1 fs2
      | SFand(_, (f1, f2)) -> aux f1 (aux f2 eqs)
      | _ -> raise Not_found in
    aux f empty

  let enter_local env local ids1 ids2 =
    try
      let do1 local (x1,t1) (x2,t2) =
        EcReduction.EqTest.for_type_exn env t1 t2;
        Mid.add x2 x1 local in
      List.fold_left2 do1 local ids1 ids2
    with _ -> raise EqObsInError

  let needed_eq env ml mr f =

    let rec add_eq local eqs f1 f2 =
      match f1.f_node, f2.f_node with
      | Fquant(q1,bd1,f1), Fquant(q2,bd2,f2) when q1 = q2 ->
        let local =
          let toty (id,gty) = id, gty_as_ty gty in
          enter_local env local (List.map toty bd1) (List.map toty bd2) in
        add_eq local eqs f1 f2
      | Fif(e1,t1,f1), Fif(e2,t2,f2) ->
        List.fold_left2 (add_eq local) eqs [e1;t1;f1] [e2;t2;f2]
      | Fmatch(b1,fs1,ty1), Fmatch(b2,fs2,ty2) when
             EcReduction.EqTest.for_type env ty1 ty2
          && EcReduction.EqTest.for_type env b1.f_ty b2.f_ty
        -> List.fold_left2 (add_eq local) eqs (b1::fs1) (b2::fs2)
      | Flet(lp1,e1,f1), Flet(lp2,e2,f2) ->
        let eqs = add_eq local eqs e1 e2 in
        let local = enter_local env local (lp_bind lp1) (lp_bind lp2) in
        add_eq local eqs f1 f2
      | Fint i1, Fint i2 when EcBigInt.equal i1 i2 -> eqs
      | Flocal id1, Flocal id2 when
          opt_equal EcIdent.id_equal (Some id1) (Mid.find_opt id2 local) -> eqs
      | Fpvar(pv1,m1), Fpvar(pv2,m2)
          when EcIdent.id_equal ml m1 && EcIdent.id_equal mr m2 ->
          add env f1.f_ty pv1 pv2 eqs
      | Fpvar(pv2,m2), Fpvar(pv1,m1)
          when EcIdent.id_equal ml m1 && EcIdent.id_equal mr m2 ->
          add env f1.f_ty pv1 pv2 eqs
      | Fglob(_,m2), Fglob(_,m1)
        when EcIdent.id_equal ml m1 && EcIdent.id_equal mr m2 ->
        add_eq local eqs f2 f1
      | Fglob(mp1,m1), Fglob(mp2,m2)
        when EcIdent.id_equal ml m1 && EcIdent.id_equal mr m2 ->
        let f1' = NormMp.norm_glob env ml mp1 in
        let f2' = NormMp.norm_glob env mr mp2 in
        if f_equal f1 f1' && f_equal f2 f2' then add_glob env mp1 mp2 eqs
        else add_eq local eqs f1' f2'
      | Fop(op1,tys1), Fop(op2,tys2) when EcPath.p_equal op1 op2 &&
          List.all2 (EcReduction.EqTest.for_type env) tys1 tys2 -> eqs
      | Fapp(f1,a1), Fapp(f2,a2) ->
        List.fold_left2 (add_eq local) eqs (f1::a1) (f2::a2)
      | Ftuple es1, Ftuple es2 ->
        List.fold_left2 (add_eq local) eqs es1 es2
      | Fproj(f1,i1), Fproj(f2,i2) when i1 = i2 ->
        add_eq local eqs f1 f2
      | _, _ -> raise Not_found in

    let rec aux local eqs f =
      match f.f_node with
      | Fquant(_,bd1,f1) ->
        let local =
          let toty (id,gty) = id, gty_as_ty gty in
          let bd = List.map toty bd1 in
          enter_local env local bd bd in
        aux local eqs f1
      | Fif(e1,t1,f1) ->
        List.fold_left (aux local) eqs [e1;t1;f1]
      | Fmatch(b1,fs1,_) ->
        List.fold_left (aux local) eqs (b1::fs1)
      | Flet(lp1,e1,f1) ->
        let eqs = aux local eqs e1 in
        let local =
          let lp = lp_bind lp1 in
          enter_local env local lp lp in
        aux local eqs f1
      | Fop(op,_) when EcPath.p_equal op EcCoreLib.CI_Bool.p_true -> eqs

      | Fapp({f_node = Fop(op,_)},a) ->
        begin match op_kind op with
        | Some `True -> eqs
        | Some (`Eq | `Iff) -> add_eq local eqs (List.nth a 0) (List.nth a 1)
        | Some (`And _ | `Or _) -> List.fold_left (aux local) eqs a
        | Some `Imp -> aux local eqs (List.nth a 1)
        | _ -> raise Not_found
        end
      | _ -> raise Not_found in

    try aux Mid.empty empty f
    with _ -> raise Not_found

  let check_glob eqs =
    Mnpv.iter (fun pv (s,_)->
      if is_loc pv || Snpv.exists is_loc s then raise EqObsInError)
      eqs.s_pv

  let mem x1 x2 t =
    try Snpv.mem x2 (fst (Mnpv.find x1 t.s_pv))
    with Not_found -> false

  let mem_glob m t = Sm.mem m t.s_gl

  let iter fv fg t =
    Mnpv.iter (fun x1 (s,ty) -> Snpv.iter (fun x2 -> fv x1 x2 ty) s) t.s_pv;
    Sm.iter fg t.s_gl

  let eq_fv2 t =
    let pv = ref Mnpv.empty in
    let fv _ x2 ty = pv := Mnpv.add x2 (Snpv.singleton x2, ty) !pv in
    let gl = ref Sm.empty in
    let fg m = gl := Sm.add m !gl in
    iter fv fg t;
    { s_pv = !pv; s_gl = !gl }

  let fv2 t =
    let pv = ref Mnpv.empty in
    let fv _ x2 ty = pv := Mnpv.add x2 ty !pv in
    let gl = ref Sm.empty in
    let fg m = gl := Sm.add m !gl in
    iter fv fg t;
    { PV.s_pv = !pv; PV.s_gl = !gl }

  let eq_refl (fv:PV.t) =
    let pv = ref Mnpv.empty in
    let fx x ty = pv := Mnpv.add x (Snpv.singleton x, ty) !pv in
    Mnpv.iter fx fv.PV.s_pv;
    let gl = ref Sm.empty in
    let fg m = gl := Sm.add m !gl in
    Sm.iter fg fv.PV.s_gl;
    { s_pv = !pv; s_gl = !gl }

(*add_eqs env local eqs e1 e2 : collect a set of equalities with ensure the
   equality of e1 and e2 *)
  let rec add_eqs env local eqs e1 e2 =
    match e1.e_node, e2.e_node with
    | Equant(qt1,bds1,e1), Equant(qt2,bds2,e2) when qt_equal qt1 qt2 ->
      let local = enter_local env local bds1 bds2 in
      add_eqs env local eqs e1 e2
    | Eint i1, Eint i2 when EcBigInt.equal i1 i2 -> eqs
    | Elocal x1, Elocal x2 when
        opt_equal EcIdent.id_equal (Some x1) (Mid.find_opt x2 local) -> eqs
    | Evar pv1, Evar pv2
      when EcReduction.EqTest.for_type env e1.e_ty e2.e_ty ->
      add env e1.e_ty pv1 pv2 eqs
  (* TODO it could be greate to work up to reduction,
     I postpone this for latter *)
    | Eop(op1,tys1), Eop(op2,tys2)
      when EcPath.p_equal op1 op2 &&
        List.all2  (EcReduction.EqTest.for_type env) tys1 tys2 -> eqs
    | Eapp(f1,a1), Eapp(f2,a2) ->
      List.fold_left2 (add_eqs env local) eqs (f1::a1) (f2::a2)
    | Elet(lp1,a1,b1), Elet(lp2,a2,b2) ->
      let blocal = enter_local env local (lp_bind lp1) (lp_bind lp2) in
      let eqs = add_eqs env local eqs a1 a2 in
      add_eqs env blocal eqs b1 b2
    | Etuple es1, Etuple es2 ->
      List.fold_left2 (add_eqs env local) eqs es1 es2
    | Eproj(es1,i1), Eproj(es2,i2) when i1 = i2 ->
      add_eqs env local eqs es1 es2
    | Eif(e1,t1,f1), Eif(e2,t2,f2) ->
      List.fold_left2 (add_eqs env local) eqs [e1;t1;f1] [e2;t2;f2]
    | Ematch(b1,es1,ty1), Ematch(b2,es2,ty2)
      when EcReduction.EqTest.for_type env ty1 ty2
        && EcReduction.EqTest.for_type env b1.e_ty b2.e_ty ->
      List.fold_left2 (add_eqs env local) eqs (b1::es1) (b2::es2)
    | _, _ -> raise EqObsInError

  let add_eqs env e1 e2 eqs =  add_eqs env Mid.empty eqs e1 e2

end


(* Same function but specialized to the case where c1 and c2 are equal,
   and where the invariant is true *)

let is_in_refl env lv eqo =
  match lv with
  | LvVar (pv,_) -> PV.mem_pv env pv eqo
  | LvTuple lr -> List.exists (fun (pv,_) -> PV.mem_pv env pv eqo) lr

let add_eqs_refl env eqo e =
  let f = form_of_expr mhr e in
  let fv = PV.fv env mhr f in
  PV.union fv eqo

let remove_refl env lv eqo =
  match lv with
  | LvVar (pv,_) -> PV.remove env pv eqo
  | LvTuple lr -> List.fold_left (fun eqo (pv,_) -> PV.remove env pv eqo) eqo lr

let rec s_eqobs_in_refl env c eqo =
  is_eqobs_in_refl env (List.rev c.s_node) eqo

and is_eqobs_in_refl env c eqo =
  match c with
  | [] -> eqo
  | i::c ->
    is_eqobs_in_refl env c (i_eqobs_in_refl env i eqo)

and i_eqobs_in_refl env i eqo =
  match i.i_node with
  | Sasgn(lv,e) ->
    if is_in_refl env lv eqo then
      add_eqs_refl env (remove_refl env lv eqo) e
    else eqo

  | Srnd(lv,e) ->
    add_eqs_refl env (remove_refl env lv eqo) e

  | Scall(lv,f,args) ->
    let eqo  =
      match lv with
      | None -> eqo
      | Some lv -> remove_refl env lv eqo in
    let geqo = PV.global eqo in
    let leqo = PV.local  eqo in
    let geqi = eqobs_inF_refl env f geqo in
    let eqi  = List.fold_left (add_eqs_refl env) (PV.union leqo geqi) args in
    eqi

  | Sif(e,st,sf) ->
    let eqs1 = s_eqobs_in_refl env st eqo in
    let eqs2 = s_eqobs_in_refl env sf eqo in
    let eqi = PV.union eqs1 eqs2 in
    add_eqs_refl env eqi e

  | Swhile(e,s) ->
    let rec aux eqo =
      let eqi = s_eqobs_in_refl env s eqo in
      if PV.subset eqi eqo then eqo
      else aux (PV.union eqi eqo) in
    aux (add_eqs_refl env eqo e)

  | Sassert e -> add_eqs_refl env eqo e
  | Sabstract _ -> assert false

and eqobs_inF_refl env f' eqo =
  let f = NormMp.norm_xfun env f' in
  let ffun = Fun.by_xpath f env in
  match ffun.f_def with
  | FBalias _ -> assert false
  | FBdef fdef ->
    let eqo =
      match fdef.f_ret with
      | None -> eqo
      | Some r -> add_eqs_refl env eqo r in
    let eqi = s_eqobs_in_refl env fdef.f_body eqo in
    let local = PV.local eqi in
    let params =
      match ffun.f_sig.fs_anames with
      | None -> PV.add env (pv_arg f) ffun.f_sig.fs_arg PV.empty
      | Some lv ->
        List.fold_left (fun fv v -> PV.add env (pv_loc f v.v_name) v.v_type fv)
          PV.empty lv in
    if PV.subset local params then PV.global eqi
    else
      let diff = PV.diff local params in
      let ppe = EcPrinting.PPEnv.ofenv env in
      EcCoreGoal.tacuerror "In function %a, %a are used before being initialized"
        (EcPrinting.pp_funname ppe) f' (PV.pp env) diff

  | FBabs oi ->
    let do1 eqo o = PV.union (eqobs_inF_refl env o eqo) eqo in
    let top = EcPath.m_functor f.x_top in
    let rec aux eqo =
      let eqi = List.fold_left do1 eqo oi.oi_calls in
      if PV.subset eqi eqo then eqo
      else aux eqi in
    if oi.oi_in then aux (PV.add_glob env top eqo)
    else
      let eqi = aux (PV.remove_glob top eqo) in
      if PV.mem_glob env top eqi then begin
        let ppe = EcPrinting.PPEnv.ofenv env in
        EcCoreGoal.tacuerror "Function %a may use oracles that need equality on glob %a."
        (EcPrinting.pp_funname ppe) f' (EcPrinting.pp_topmod ppe) top
      end;
      eqi

(* -------------------------------------------------------------------- *)
let check_module_in env mp mt =
  let sig_ = ModTy.sig_of_mt env mt in
  let params = sig_.mis_params in
  let global = PV.fv env mhr (NormMp.norm_glob env mhr mp) in
  let env = List.fold_left
    (fun env (id,mt) ->
      Mod.bind_local id mt (Sx.empty,Sm.empty) env) env params in
  let extra = List.map (fun (id,_) -> EcPath.mident id) params in
  let mp = EcPath.mpath mp.m_top (mp.m_args @ extra) in
  let check = function
    | Tys_function(fs,oi) ->
      let f = EcPath.xpath_fun mp fs.fs_name in
      let eqi = eqobs_inF_refl env f global in
      (* We remove the paramater not take into account *)
      let eqi =
        List.fold_left (fun eqi mp -> PV.remove_glob mp eqi) eqi extra in
      if not (oi.oi_in) && not (PV.is_empty eqi) then
        let ppe = EcPrinting.PPEnv.ofenv env in
        EcCoreGoal.tacuerror "The function %a should initialize %a"
          (EcPrinting.pp_funname ppe) f (PV.pp env) eqi in

  List.iter check sig_.mis_body
