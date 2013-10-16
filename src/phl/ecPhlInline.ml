(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcCorePhl

(* -------------------------------------------------------------------- *)
class rn_hl_inline side pattern =
object
  inherit xrule "[hl] inline"

  method side    : bool option = side
  method pattern : s_pat       = pattern
end

let rn_hl_inline side pattern =
  RN_xtd (new rn_hl_inline side pattern :> xrule)

(* --------------------------------------------------------------------- *)
module LowInternal = struct
  let inline hyps me sp s =
    let env = LDecl.toenv hyps in
    let module P = EcPath in
  
    let inline1 me lv p args = 
      let p = EcEnv.NormMp.norm_xpath env p in
      let f = EcEnv.Fun.by_xpath p env in
      let fdef = 
        match f.f_def with
        | FBdef def -> def 
        | _ -> begin
          let ppe = EcPrinting.PPEnv.ofenv env in
          tacuerror
            "Abstract function `%a' cannot be inlined"
            (EcPrinting.pp_funname ppe) p
        end
      in
      let me, anames = 
        List.map_fold fresh_pv me f.f_sig.fs_params in
      let me, lnames = 
        List.map_fold fresh_pv me fdef.f_locals in
      let subst =
        let for1 mx v x =
          (* Remark p is in normal form so (P.xqname p v.v_name) is *)
          P.Mx.add
            (P.xqname p v.v_name)
            (P.xqname (EcMemory.xpath me) x)
            mx
        in
        let mx = P.Mx.empty in
        let mx = List.fold_left2 for1 mx f.f_sig.fs_params anames in
        let mx = List.fold_left2 for1 mx fdef.f_locals lnames in
        let on_xp xp =
          let xp' = EcEnv.NormMp.norm_xpath env xp in
          P.Mx.find_def xp xp' mx 
        in
        { e_subst_id with es_xp = on_xp }
      in
  
      let prelude =
        List.map2
          (fun (v, newx) e ->
            let newpv = pv_loc (EcMemory.xpath me) newx in
            i_asgn (LvVar (newpv, v.v_type), e))
          (List.combine f.f_sig.fs_params anames)
          args in
  
      let body  = s_subst subst fdef.f_body in
  
      let resasgn =
        match fdef.f_ret with
        | None   -> None
        | Some r -> Some (i_asgn (oget lv, e_subst subst r)) in
  
      me, prelude @ body.s_node @ (otolist resasgn) in
  
    let rec inline_i me ip i = 
      match ip, i.i_node with
      | IPpat, Scall (lv, p, args) -> 
        inline1 me lv p args 
      | IPif(sp1, sp2), Sif(e,s1,s2) ->
        let me,s1 = inline_s me sp1 s1.s_node in
        let me,s2 = inline_s me sp2 s2.s_node in
        me, [i_if(e,stmt s1, stmt s2)]
      | IPwhile sp, Swhile(e,s) ->
        let me,s = inline_s me sp s.s_node in
        me, [i_while(e,stmt s)]
      | _, _ -> assert false (* FIXME error message *)

    and inline_s me sp s = 
      match sp with
      | [] -> me, s
      | (toskip,ip)::sp ->
        let r,i,s = List.split_n toskip s in
        let me,si = inline_i me ip i in
        let me,s = inline_s me sp s in
        me, List.rev_append r (si @ s)

    in
    let me, s = inline_s me sp s.s_node in
      (me, stmt s )
end

(* -------------------------------------------------------------------- *)
let t_inline_bdHoare sp g =
  let hyps,concl = get_goal g in
  let hoare      = t_as_bdHoareS concl in
  let (me, stmt) = LowInternal.inline hyps hoare.bhs_m sp hoare.bhs_s in
  let concl      = f_bdHoareS_r { hoare with bhs_m = me; bhs_s = stmt; } in
    prove_goal_by [concl] (rn_hl_inline None sp) g

let t_inline_hoare sp g =
  let hyps,concl = get_goal g in
  let hoare      = t_as_hoareS concl in
  let (me, stmt) = LowInternal.inline hyps hoare.hs_m sp hoare.hs_s in
  let concl      = f_hoareS_r { hoare with hs_m = me; hs_s = stmt; } in
    prove_goal_by [concl] (rn_hl_inline None sp) g

let t_inline_equiv side sp g =
  let hyps,concl = get_goal g in
  let equiv = t_as_equivS concl in
  let concl =
    match side with
    | true  ->
        let (me, stmt) = LowInternal.inline hyps equiv.es_ml sp equiv.es_sl in
          f_equivS_r { equiv with es_ml = me; es_sl = stmt; }
    | false ->
        let (me, stmt) = LowInternal.inline hyps equiv.es_mr sp equiv.es_sr in
          f_equivS_r { equiv with es_mr = me; es_sr = stmt; }
  in
    prove_goal_by [concl] (rn_hl_inline (Some side) sp) g


(* -------------------------------------------------------------------- *)
module HiInternal = struct
  let pat_all fs s =
    let rec aux_i i = 
      match i.i_node with
      | Scall(_,f,_) -> 
        if EcPath.Sx.mem f fs then Some IPpat else None
      | Sif(_,s1,s2) -> 
        let sp1 = aux_s 0 s1.s_node in
        let sp2 = aux_s 0 s2.s_node in
        if sp1 = [] && sp2 = [] then None 
        else Some (IPif(sp1,sp2))
      | Swhile(_,s) ->
        let sp = aux_s 0 s.s_node in
        if sp = [] then None else Some (IPwhile(sp)) 
      | _ -> None
  
    and aux_s n s = 
      match s with
      | [] -> []
      | i::s ->
        match aux_i i with
        | Some ip -> (n,ip) :: aux_s 0 s 
        | None -> aux_s (n+1) s
    in
      aux_s 0 s.s_node

  let pat_of_occs cond occs s =
    let occs = ref occs in
    let rec aux_i occ i = 
      match i.i_node with
      | Scall (_,f,_) -> 
        if cond f then 
          let occ = 1 + occ in
          if Sint.mem occ !occs then begin
            occs := Sint.remove occ !occs; 
            occ, Some IPpat
          end else occ, None
        else occ, None
      | Sif(_,s1,s2) ->
        let occ, sp1 = aux_s occ 0 s1.s_node in
        let occ, sp2 = aux_s occ 0 s2.s_node in
        let ip = if sp1 = [] && sp2 = [] then None else Some(IPif(sp1,sp2)) in
        occ, ip
      | Swhile(_,s) ->
        let occ, sp = aux_s occ 0 s.s_node in
        let ip = if sp = [] then None else Some(IPwhile sp) in
        occ, ip
      | _ -> occ, None 
    and aux_s occ n s =
      match s with
      | [] -> occ, []
      | i::s ->
        match aux_i occ i with
        | occ, Some ip -> 
          let occ, sp = aux_s occ 0 s in
          occ, (n,ip) :: sp
        | occ, None -> aux_s occ (n+1) s in
    let _, sp = aux_s 0 0 s.s_node in
      assert (Sint.is_empty !occs); (* FIXME error message *)
      sp
end

(* -------------------------------------------------------------------- *)  
let rec process_inline_all side fs g =
  let concl = get_concl g in
  match concl.f_node, side with
  | FequivS _, None ->
      t_seq
        (process_inline_all (Some true ) fs)
        (process_inline_all (Some false) fs) g

  | FequivS es, Some b ->
      let sp = HiInternal.pat_all fs (if b then es.es_sl else es.es_sr) in
        if   sp = []
        then t_id None g
        else t_seq
               (t_inline_equiv b sp)
               (process_inline_all side fs) g

  | FhoareS hs, None ->
      let sp = HiInternal.pat_all fs hs.hs_s in
        if   sp = []
        then t_id None g
        else t_seq
               (t_inline_hoare sp)
               (process_inline_all side fs) g

  | FbdHoareS bhs, None ->
      let sp = HiInternal.pat_all fs bhs.bhs_s in
      if   sp = []
      then t_id None g
      else t_seq
        (t_inline_bdHoare sp)
        (process_inline_all side fs) g

  | _, _ -> cannot_apply "inline" "Wrong parameters or phl/prhl judgement not found" 

(* -------------------------------------------------------------------- *)
let process_inline_occs side fs occs g =
  let cond = 
    if EcPath.Sx.is_empty fs then fun _ -> true
    else fun f -> EcPath.Sx.mem f fs in
  let occs = Sint.of_list occs in
  let concl = get_concl g in
  match concl.f_node, side with
  | FequivS es, Some b ->
    let sp =  HiInternal.pat_of_occs cond occs (if b then es.es_sl else es.es_sr) in
    t_inline_equiv b sp g 
  | FhoareS hs, None ->
    let sp =  HiInternal.pat_of_occs cond occs hs.hs_s in
    t_inline_hoare sp g 
  | _, _ -> assert false (* FIXME error message *)

(* -------------------------------------------------------------------- *)
let process_inline infos g =
  match infos with
  | `ByName (side, (fs, occs)) -> begin
      let hyps = get_hyps g in
      let env = LDecl.toenv hyps in
      let fs = 
        List.fold_left (fun fs f ->
          let f = EcTyping.trans_gamepath env f in
          EcPath.Sx.add f fs) EcPath.Sx.empty fs 
      in
      match occs with
      | None -> process_inline_all side fs g
      | Some occs -> process_inline_occs side fs occs g
    end

  | `ByPattern _ -> failwith "not-implemented"
