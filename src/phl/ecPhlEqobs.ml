(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let extend_body f fsig body =
  let arg = pv_arg f in
  let i =
    match fsig.fs_anames with
    | None | Some [] -> []

    | Some [v] ->
        [i_asgn (LvVar (pv_loc f v.v_name, v.v_type),
                 e_var arg fsig.fs_arg)]

    | Some lv ->
        let lv = List.map (fun v -> pv_loc f v.v_name, v.v_type) lv in
        [i_asgn (LvTuple lv, e_var arg fsig.fs_arg)]

  in
    (arg, s_seq (stmt i) body)

(* -------------------------------------------------------------------- *)
(* Invariant ifvl,ifvr = PV.fv env ml inv, PV.fv env mr inv *)
type sim = {
  sim_env      : env;
  sim_inv      : form;
  sim_ifvl     : PV.t;
  sim_ifvr     : PV.t;
  default_spec : EcPath.xpath -> EcPath.xpath -> Mpv2.t -> Mpv2.t;
  needed_spec  : (EcPath.xpath * EcPath.xpath * Mpv2.t) list;
}

let init_sim env spec inv =

  let default_spec fl fr eqo =
    let check_eq eqo' = Mpv2.subset eqo eqo' in
    let test1 (ofl',ofr', eqo') =
      match ofl', ofr' with
      | Some fl', Some fr' ->
        NormMp.x_equal env fl fl' && NormMp.x_equal env fr fr' && check_eq eqo'
      | _, _ -> false in
    let test2 (ofl',ofr', eqo') =
      match ofl', ofr' with
      | Some fl', None -> NormMp.x_equal env fl fl' && check_eq eqo'
      | None, Some fr' -> NormMp.x_equal env fr fr' && check_eq eqo'
      | _, _ -> false in
    let test3 (ofl',ofr', eqo') =
      match ofl', ofr' with
      | None, None -> check_eq eqo'
      | _, _ -> false in
    let get test () =
      List.opick
        (fun (_,_,eqo' as t) -> if test t then Some eqo' else None) spec in
    match List.fpick [get test1; get test2; get test3] with
    | None ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      EcEnv.notify env `Warning
        "warning default specification for %a %a not given"
        (EcPrinting.pp_funname ppe) fl (EcPrinting.pp_funname ppe) fr;
      raise EqObsInError
    | Some eq -> eq in

  { sim_env  = env;
    sim_inv  = inv;
    sim_ifvl = PV.fv env mleft inv;
    sim_ifvr = PV.fv env mright inv;
    default_spec = default_spec;
    needed_spec  = [];
  }

let default_spec sim fl fr eqo =
  let eqi = sim.default_spec fl fr eqo in
  let env = sim.sim_env in
  let test (fl', fr', eqi') =
    NormMp.x_equal env fl fl' && NormMp.x_equal env fr fr' &&
      Mpv2.equal eqi' eqi in
  let sim =
    if List.exists test sim.needed_spec then sim
    else { sim with needed_spec = (fl,fr,eqi)::sim.needed_spec } in
  sim, eqi

let add_eqs sim eqs e1 e2 = Mpv2.add_eqs sim.sim_env e1 e2 eqs

let check sim pv fv = PV.check_notmod sim.sim_env pv fv

let checks sim pvs fv = List.for_all (fun (pv,_) -> check sim pv fv) pvs

let check_lvalue aux lv =
  match lv with
  | LvVar (xl,_)   -> aux xl
  | LvTuple ll -> List.for_all (fun (x,_) -> aux x)  ll

let check_not_l sim lvl eqo =
  let aux pv =
    check sim pv sim.sim_ifvl &&
      not (Mpv2.mem_pv_l sim.sim_env pv eqo) in
  check_lvalue aux lvl

let check_not_r sim lvr eqo =
  let aux pv =
    check sim pv sim.sim_ifvr &&
      not (Mpv2.mem_pv_r sim.sim_env pv eqo) in
  check_lvalue aux lvr

(* -------------------------------------------------------------------- *)
let remove sim lvl lvr eqs =
  let env = sim.sim_env in
  let aux eqs (pvl,tyl) (pvr,tyr) =
    if EcReduction.EqTest.for_type env tyl tyr then begin
      if not (check sim pvl sim.sim_ifvl && check sim pvr sim.sim_ifvr) then
        raise EqObsInError;
      Mpv2.remove env pvl pvr eqs
    end else
      raise EqObsInError in

  match lvl, lvr with
  | LvVar xl, LvVar xr -> aux eqs xl xr
  | LvTuple ll, LvTuple lr when List.length ll = List.length lr ->
    List.fold_left2 aux eqs ll lr
  | _, _ -> raise EqObsInError

(* -------------------------------------------------------------------- *)
let oremove sim lvl lvr eqs =
  match lvl, lvr with
  | None, None -> eqs
  | Some lvl, Some lvr -> remove sim lvl lvr eqs
  | _, _ -> raise EqObsInError

(* -------------------------------------------------------------------- *)
let rec check_deadcode_i check_lv i =
  match i.i_node with
  | Sasgn(lv,_) -> check_lv lv
  | Sif(_,s1,s2) -> check_deadcode_s check_lv s1 && check_deadcode_s check_lv s2
  | _ -> false
        (* TODO :
           For random we need a way to known that the distribution
           is lossless;
           For while we can do the same if we are able to ensure
           the termination;
           As well for procedure *)
and check_deadcode_s check_lv s =
  List.for_all (check_deadcode_i check_lv) s.s_node

(* -------------------------------------------------------------------- *)
let rec s_eqobs_in_rev rsl rsr sim (eqo:Mpv2.t) =
  match rsl, rsr with
  | { i_node = Sasgn(LvVar (xl,_), el)}::rsl, _
    when is_var el && check sim xl sim.sim_ifvl ->
    s_eqobs_in_rev rsl rsr sim (Mpv2.subst_l sim.sim_env xl (destr_var el) eqo)
  | _, { i_node = Sasgn(LvVar (xr,_), er)} :: rsr
    when is_var er && check sim xr sim.sim_ifvr ->
    s_eqobs_in_rev rsl rsr sim (Mpv2.subst_r sim.sim_env xr (destr_var er) eqo)

  | { i_node = Sasgn(LvTuple xls, el)}::rsl, _
    when is_tuple_var el && checks sim xls sim.sim_ifvl ->
    s_eqobs_in_rev rsl rsr sim
      (Mpv2.substs_l sim.sim_env xls (destr_tuple_var el) eqo)
  | _, { i_node = Sasgn(LvTuple xrs, er)} :: rsr
    when is_tuple_var er && checks sim xrs sim.sim_ifvr ->
    s_eqobs_in_rev rsl rsr sim
      (Mpv2.substs_r sim.sim_env xrs (destr_tuple_var er) eqo)

    (* this is dead code *)
  | il :: rsl, _ when check_deadcode_i (fun lv -> check_not_l sim lv eqo) il ->
    s_eqobs_in_rev rsl rsr sim eqo
  | _, ir::rsr when check_deadcode_i (fun lv -> check_not_r sim lv eqo) ir ->
    s_eqobs_in_rev rsl rsr sim eqo

  | il::rsl', ir::rsr' ->
    let o =
      try Some (i_eqobs_in il ir sim eqo) with EqObsInError -> None in
    begin match o with
    | None -> rsl, rsr, sim, eqo
    | Some (sim, eqi) -> s_eqobs_in_rev rsl' rsr' sim eqi
    end

  | _, _ -> rsl, rsr, sim, eqo

and i_eqobs_in il ir sim (eqo:Mpv2.t) =
  match il.i_node, ir.i_node with
  | Sasgn(lvl,el), Sasgn(lvr,er) | Srnd(lvl,el), Srnd(lvr,er) ->
    sim, add_eqs sim (remove sim lvl lvr eqo) el er

  | Scall(lvl,fl,argsl), Scall(lvr,fr,argsr)
    when List.length argsl = List.length argsr ->
    let eqo = oremove sim lvl lvr eqo in
    let env = sim.sim_env in
    let modl, modr = f_write env fl, f_write env fr in
    let eqnm = Mpv2.split_nmod env modl modr eqo in
    let outf = Mpv2.split_mod  env modl modr eqo in
    Mpv2.check_glob outf;
    let sim, eqi = f_eqobs_in fl fr sim outf in
    let eqi = List.fold_left2 (add_eqs sim) (Mpv2.union eqnm eqi) argsl argsr in
    sim, eqi

  | Sif(el,stl,sfl), Sif(er,str,sfr) ->
    let sim, eqs1 = s_eqobs_in_full stl str sim eqo in
    let sim, eqs2 = s_eqobs_in_full sfl sfr sim eqo in
    let eqi = add_eqs sim (Mpv2.union eqs1 eqs2) el er in
    sim, eqi

  | Swhile(el,sl), Swhile(er,sr) ->
    let rec aux eqo =
      let sim', eqi = s_eqobs_in_full sl sr sim eqo in
      if Mpv2.subset eqi eqo then sim', eqo
      else aux (Mpv2.union eqi eqo) in
    aux (add_eqs sim eqo el er)

  | Sassert el, Sassert er -> sim, add_eqs sim eqo el er
  | _, _ -> raise EqObsInError

and s_eqobs_in_full sl sr sim eqo =
  let r1,r2,sim, eqi = s_eqobs_in sl sr sim eqo in
  if r1 <> [] || r2 <> [] then raise EqObsInError;
  sim, eqi

and s_eqobs_in sl sr sim eqo =
  s_eqobs_in_rev (List.rev sl.s_node) (List.rev sr.s_node) sim eqo

(* -------------------------------------------------------------------- *)
and f_eqobs_in fl fr sim eqO =
  let env = sim.sim_env in
  let nfl  = NormMp.norm_xfun env fl in
  let nfr  = NormMp.norm_xfun env fr in
  let modl, modr = f_write env fl, f_write env fr in
  let eqnm = Mpv2.split_nmod env modl modr eqO in
  let outf = Mpv2.split_mod  env modl modr eqO in

  let defl = Fun.by_xpath nfl env in
  let defr = Fun.by_xpath nfr env in
  (* TODO check that inv contain only global *)
  let sim, eqi =
    try
      match defl.f_def, defr.f_def with
      | FBabs oil, FBabs oir ->
        let (topl,_,_,_), (topr,_,_,_) =
          try EcLowPhlGoal.abstract_info2 env fl fr
          with TcError _ -> raise EqObsInError in

        let top = EcPath.m_functor nfl.EcPath.x_top in
        let sim, eqi =
          (* Try to infer the good invariant for oracle *)
          let eqo = Mpv2.remove_glob top outf in
          let rec aux eqo =
            let sim, eqi =
              List.fold_left2
                (fun (sim,eqo) o_l o_r -> f_eqobs_in o_l o_r sim eqo)
                (sim,eqo) oil.oi_calls oir.oi_calls in
            if Mpv2.subset eqi eqo then sim, eqo
            else aux (Mpv2.union eqi eqo) in
          aux eqo in
        begin
          try
            let inv = Mpv2.to_form mleft mright eqi sim.sim_inv in
            let fvl = PV.fv env mleft inv in
            let fvr = PV.fv env mright inv in
            PV.check_depend env fvl topl;
            PV.check_depend env fvr topr
          with TcError _ -> raise EqObsInError
        end;
        let eqi = if oil.oi_in then Mpv2.add_glob env top top eqi else eqi in
        sim, eqi

      | FBdef funl, FBdef funr ->
        let sigl, sigr = defl.f_sig, defr.f_sig in
        let testty =
          EcReduction.EqTest.for_type env sigl.fs_arg sigr.fs_arg
          && EcReduction.EqTest.for_type env sigl.fs_ret sigr.fs_ret
        in
        if not testty then raise EqObsInError;
        let eqo' =
          match funl.f_ret, funr.f_ret with
          | None, None -> outf
          | Some el, Some er -> add_eqs sim outf el er
          | _, _ -> raise EqObsInError in

        let argl, bodyl = extend_body nfl sigl funl.f_body in
        let argr, bodyr = extend_body nfr sigr funr.f_body in
        let sim, eqi    = s_eqobs_in_full bodyl bodyr sim eqo' in

        let eqi = Mpv2.remove sim.sim_env argl argr eqi in
        Mpv2.check_glob eqi;
        sim, eqi
      | _, _ -> raise EqObsInError
    with EqObsInError ->
      default_spec sim nfl nfr outf in
  sim, Mpv2.union eqnm eqi

(* -------------------------------------------------------------------- *)
let mk_inv_spec2 env inv (fl, fr, eqi, eqo) =
  let defl = Fun.by_xpath fl env in
  let defr = Fun.by_xpath fr env in
  let sigl, sigr = defl.f_sig, defr.f_sig in
  let testty =
    EcReduction.EqTest.for_type env sigl.fs_arg sigr.fs_arg
    && EcReduction.EqTest.for_type env sigl.fs_ret sigr.fs_ret in
  if not testty then raise EqObsInError;
  let eq_params =
    f_eqparams
      fl sigl.fs_arg sigl.fs_anames mleft
      fr sigr.fs_arg sigr.fs_anames mright in
  let eq_res = f_eqres fl sigl.fs_ret mleft fr sigr.fs_ret mright in
  let pre = f_and eq_params (Mpv2.to_form mleft mright eqi inv) in
  let post = f_and eq_res (Mpv2.to_form mleft mright eqo inv) in
  f_equivF pre fl fr post

(* -------------------------------------------------------------------- *)
let mk_inv_spec env inv (fl, fr, eqg) =
  mk_inv_spec2 env inv (fl, fr, eqg, eqg)

(* -------------------------------------------------------------------- *)
let t_eqobs_inS_r sim eqo tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let sim = { sim with sim_env = env } in
  let es = tc1_as_equivS tc in
  let ml = fst (es.es_ml) and mr = fst (es.es_mr) in
  let sl, sr, sim, eqi =
    try s_eqobs_in es.es_sl es.es_sr sim eqo
    with EqObsInError -> tc_error !!tc "cannot apply sim ..."
  in
  let inv = sim.sim_inv in
  let post = Mpv2.to_form ml mr eqo inv in
  let pre  = Mpv2.to_form ml mr eqi inv in

  let sl = stmt (List.rev sl) and sr = stmt (List.rev sr) in
  if not (EcReduction.is_alpha_eq hyps post es.es_po) then
    tc_error !!tc "cannot apply sim";

  let sg = List.map (mk_inv_spec env inv) sim.needed_spec in
  let concl = f_equivS es.es_ml es.es_mr es.es_pr sl sr pre in

  FApi.xmutate1 tc `EqobsIn (sg @ [concl])

(* -------------------------------------------------------------------- *)
let t_eqobs_inS = FApi.t_low2 "eqobs-in" t_eqobs_inS_r

(* -------------------------------------------------------------------- *)
let t_eqobs_inF_r sim eqo tc =
  let env, hyps, concl = FApi.tc1_eflat tc in
  let sim = { sim with sim_env = env } in
  let ef = tc1_as_equivF tc in
  let sim, eqi =
    try f_eqobs_in ef.ef_fl ef.ef_fr sim eqo
    with EqObsInError -> tc_error !!tc "cannot apply sim ..." in
  let inv = sim.sim_inv in
  let sg = List.map (mk_inv_spec env inv) sim.needed_spec in
  let concl' = mk_inv_spec2 env inv (ef.ef_fl, ef.ef_fr, eqi, eqo) in
  if not (EcReduction.is_alpha_eq hyps concl concl') then
    tc_error !!tc "cannot apply sim for fun";
  FApi.xmutate1 tc `EqobsIn sg

(* -------------------------------------------------------------------- *)
let t_eqobs_inF = FApi.t_low2 "eqobs-in" t_eqobs_inF_r

(* -------------------------------------------------------------------- *)
let process_eqs env tc f =
   try
      Mpv2.of_form env mleft mright f
   with Not_found ->
     tc_error_lazy !!tc (fun fmt ->
       let ppe = EcPrinting.PPEnv.ofenv env in
       Format.fprintf fmt
         "cannot recognize %a as a set of equalities"
         (EcPrinting.pp_form ppe) f)

(* -------------------------------------------------------------------- *)
let process_hint tc hyps (feqs, inv) =
  let env = LDecl.toenv hyps in
  let ienv = LDecl.inv_memenv hyps in
  let doinv pf = TTC.pf_process_form !!tc ienv tbool pf in
  let doeq pf = process_eqs env tc (doinv pf) in
  let dof g = omap (EcTyping.trans_gamepath env) g in
  let geqs =
    List.map (fun ((f1,f2),geq) -> dof f1, dof f2, doeq geq)
      feqs in
  let ginv = odfl f_true (omap doinv inv) in
  geqs, ginv

(* -------------------------------------------------------------------- *)
let process_eqobs_inS info tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in
  let spec, inv = process_hint tc hyps info.EcParsetree.sim_hint in
  let eqo =
    match info.EcParsetree.sim_eqs with
    | Some pf ->
      process_eqs env tc (TTC.tc1_process_prhl_formula tc pf)
    | None ->
      try Mpv2.needed_eq env mleft mright es.es_po
      with _ -> tc_error !!tc "cannot infer the set of equalities" in
  let post = Mpv2.to_form mleft mright eqo inv in
  let sim = init_sim env spec inv in
  let t_main tc =
    match info.EcParsetree.sim_pos with
    | None ->
      FApi.t_last
        (FApi.t_try (FApi.t_seq EcPhlSkip.t_skip t_logic_trivial))
        (t_eqobs_inS sim eqo tc)
    | Some(p1,p2) ->
      let _,sl2 = s_split p1 es.es_sl in
      let _,sr2 = s_split p2 es.es_sr in
      let _, eqi =
        try s_eqobs_in_full (stmt sl2) (stmt sr2) sim eqo
        with EqObsInError -> tc_error !!tc "cannot apply sim" in
      (EcPhlApp.t_equiv_app (p1, p2) (Mpv2.to_form mleft mright eqi inv) @+ [
        t_id;
        fun tc ->
          FApi.t_last
            (EcPhlSkip.t_skip @! t_logic_trivial)
            (t_eqobs_inS sim eqo tc)
      ]) tc in
  (EcPhlConseq.t_equivS_conseq es.es_pr post @+
    [t_logic_trivial;
     t_logic_trivial;
     t_main]) tc

(* -------------------------------------------------------------------- *)
let process_eqobs_inF info tc =
  if info.EcParsetree.sim_pos <> None then
    tc_error !!tc "no positions excepted";
  let env, hyps, _ = FApi.tc1_eflat tc in
  let ef = tc1_as_equivF tc in
  let spec, inv = process_hint tc hyps info.EcParsetree.sim_hint in
  let fl = ef.ef_fl and fr = ef.ef_fr in
  let eqo =
    match info.EcParsetree.sim_eqs with
    | Some pf ->
      let _,(ml,mr) = Fun.equivF_memenv fl fr env in
      let hyps = LDecl.push_all [ml;mr] hyps in
      process_eqs env tc (TTC.pf_process_form !!tc hyps tbool pf)
    | None ->
      try Mpv2.needed_eq env mleft mright ef.ef_po
      with _ -> tc_error !!tc "cannot infer the set of equalities" in
  let eqo = Mpv2.remove env (pv_res fl) (pv_res fr) eqo in
  let sim = init_sim env spec inv in
  let _, eqi =
    try f_eqobs_in fl fr sim eqo
    with EqObsInError -> tc_error !!tc "not able to process" in
  let ef' = destr_equivF (mk_inv_spec2 env inv (fl, fr, eqi, eqo)) in
  (EcPhlConseq.t_equivF_conseq ef'.ef_pr ef'.ef_po @+ [
    t_logic_trivial;
    t_logic_trivial;
     t_eqobs_inF sim eqo]) tc

(* -------------------------------------------------------------------- *)
let process_eqobs_in cm info tc =
  let prett cm tc =
    let dt, ts = EcHiGoal.process_crushmode cm in
      EcPhlConseq.t_conseqauto ~delta:dt ?tsolve:ts tc in

  let tt tc =
    let concl = FApi.tc1_goal tc in
    match concl.f_node with
    | FequivF _ -> process_eqobs_inF info tc
    | FequivS _ -> process_eqobs_inS info tc
    | _ -> tc_error_noXhl ~kinds:[`Equiv `Any] !!tc
  in

  FApi.t_last tt ((omap prett cm |> odfl t_id) tc)
