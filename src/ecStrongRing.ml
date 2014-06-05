(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcTypes
open EcFol
open EcEnv
open EcAlgebra
open EcAlgTactic
open EcCoreGoal
open EcLowGoal

type norm_kind = 
  | NKring  of cring * RState.rstate ref 
  | NKfield of cfield * RState.rstate ref 
  | NKdefault

type einfo = {
  i_env    : env;
  kind_tbl : norm_kind Hty.t;
  rw_info  : EcPath.path list;
}

let prewrite = 
  EcPath.extend EcCoreLib.p_top ["Ring"; "rw_algebra"]

let init_einfo env = 
  { i_env    = env;
    kind_tbl = Hty.create 23;
    rw_info  = EcPath.Sp.elements (EcEnv.BaseRw.by_path prewrite env);
  }

let get_field env hyps ty () = 
  let tparams = (LDecl.tohyps hyps).EcBaseLogic.h_tvar in
  match EcTyping.get_field (tparams, ty) env with
  | Some f ->
    let cr = cfield_of_field f in
    let m  = ref RState.empty in
    Some (NKfield(cr,m))
  | None -> None

let get_ring env hyps ty () = 
  let tparams = (LDecl.tohyps hyps).EcBaseLogic.h_tvar in
  match EcTyping.get_ring (tparams,ty) env with
  | Some r ->
    let cr = cring_of_ring r in
    let m = ref RState.empty in
    Some (NKring(cr,m))
  | None -> None

let norm_kind einfo hyps ty =
  try Hty.find einfo.kind_tbl ty 
  with Not_found ->
    let kind = 
      odfl NKdefault 
        (List.fpick 
           [get_field einfo.i_env hyps ty; 
            get_ring einfo.i_env hyps ty]) in
    Hty.add einfo.kind_tbl ty kind;
    kind

let t_reflex_assumption g = 
  FApi.t_ors [t_reflex; 
              t_assumption `Alpha ; 
              FApi.t_seq t_symmetry (t_assumption `Alpha)] g

let t_intro_eq g = t_intros_s (`Symbol ["_"]) g

let is_in_hyps hyps f1 f2 =
  let is_in hyps f1 f2 = 
    try ignore (alpha_find_in_hyps hyps (f_eq f1 f2)); true
    with Not_found -> false in
  EcReduction.is_alpha_eq hyps f1 f2 ||
    is_in hyps f1 f2 || is_in hyps f2 f1

let t_ring r l (f1,f2) g = 
  FApi.t_seq (t_ring r l (f1,f2)) t_fail g 

let t_seq_last t1 t2 g =
  FApi.t_last t2 (t1 g)

let rec t_lseq_last lt g =
  match lt with
  | [] -> t_id g
  | t::lt -> t_seq_last t (t_lseq_last lt) g
(*
let pp_concl fmt g = 
  let env, hyps, concl = get_goal_e g in
  let ppe = EcPrinting.PPEnv.ofenv env in
  EcPrinting.pp_goal ppe fmt (1,(LDecl.tohyps hyps,concl))

let pp_form fmt (f,g) = 
  let env, _,_ = get_goal_e g in
  let ppe = EcPrinting.PPEnv.ofenv env in
  EcPrinting.pp_form ppe fmt f
*)

open FApi

let autorewrite info f1 f2 g = 
  let g = fst (newgoal (!@ g) (f_eq f1 f2)) in
  let g = EcHiGoal.LowRewrite.t_autorewrite info.rw_info (as_tcenv1 g) in
  destr_eq (tc_goal g)   

let t_autorw info g = 
  EcHiGoal.LowRewrite.t_autorewrite info.rw_info g

let rec t_alg_eq info g =
  let f1, f2 = destr_eq (tc1_goal g) in
  t_cut_alg_eq t_reflex_assumption info f1 f2 g

and t_cut_alg_eq t_cont info f1 f2 g =
  let hyps = tc1_hyps g in
  if is_in_hyps hyps f1 f2 then t_id g
  else match norm_kind info hyps f1.f_ty with
    | NKring(cr,m)  -> t_cut_ring_eq t_cont info cr m f1 f2 g
    | NKfield(cr,m) -> t_cut_field_eq t_cont info cr m f1 f2 g
    | NKdefault     -> t_cut_subterm_eq1 t_cont info f1 f2 g

and t_cut_alg_eqs t_cont info fs1 fs2 g =
  match fs1, fs2 with
  | [], [] -> t_cont g
  | f1::fs1, f2::fs2 -> 
    t_cut_alg_eq (t_cut_alg_eqs t_cont info fs1 fs2) info f1 f2 g
  | _, _ -> assert false

and t_cut_subterm_eq t_cont info f1 f2 g =
  let hyps = tc1_hyps g in
  if is_in_hyps hyps f1 f2 then t_cont g 
  else t_cut_subterm_eq1 t_cont info f1 f2 g 

and t_cut_subterm_eq1 t_cont info f1 f2 g = 
  let f1', f2' = autorewrite info f1 f2 g in
  let t_cont g = 
    t_seqsub (t_cut (f_eq f1 f2)) 
      [ (fun g -> t_first t_reflex_assumption (t_autorw info g));
        t_seq t_intro_eq t_cont] g in
  t_cut_subterm_eq2 t_cont info f1' f2' g 

and t_cut_subterm_eq2 t_cont info f1 f2 g = 
  let hyps = tc1_hyps g in
  if is_in_hyps hyps f1 f2 then t_cont g 
  else match f1.f_node, f2.f_node with
  | Fapp(op1,fs1), Fapp(op2,fs2) ->
    let hyps = tc1_hyps g in
    if EcReduction.is_alpha_eq hyps op1 op2 && 
      List.length fs1 = List.length fs2 then
      let t_cont g = 
        (t_seqsub (t_cut (f_eq f1 f2)) [
          t_seq 
            (t_congr (op1,op2) (List.combine fs1 fs2, f1.f_ty))
            t_reflex_assumption;
          t_seq t_intro_eq t_cont]) g in
      t_cut_alg_eqs t_cont info fs1 fs2 g
    else t_fail g
  | Ftuple fs1, Ftuple fs2 when List.length fs1 = List.length fs2 ->
    let t_cont g = 
      (t_seqsub (t_cut (f_eq f1 f2)) [
        t_seq t_split t_reflex_assumption;
        t_seq t_intro_eq t_cont]) g in
    t_cut_alg_eqs t_cont info fs1 fs2 g
  | _, _ -> t_fail g 

and t_cut_field_eq _t_cont _info _cr _rm _f1 _f2 g = t_fail g 

and t_cut_ring_eq t_cont info cr rm f1 f2 g = 
  let hyps = tc1_hyps g in
  let pe1, rm' = toring hyps cr !rm f1 in
  let pe2, rm' = toring hyps cr rm' f2 in
  rm := rm';
  let pe = ring_simplify_pe cr [] (EcRing.PEsub(pe1,pe2)) in
  let fv = Sint.elements (EcRing.fv_pe pe) in
  let r = ring_of_cring cr in
  if fv = [] then
    t_seqsub (t_cut (f_eq f1 f2)) 
      [ t_ring r [] (f1,f2);
        t_seq t_intro_eq t_cont ] g
  else
    let fs  = List.map (fun i -> oget (RState.get i rm')) fv in
    let t_end fs' g = 
      let rm' = RState.update !rm fv fs' in
      let f1' = ofring r rm' pe1 in
      let f2' = ofring r rm' pe2 in
      t_seqsub (t_cut (f_eq f1 f2))
        [t_seqsub (t_transitivity f1')
            [t_seq (t_ring_congr cr !rm pe1 fv fs') t_reflex_assumption;
             t_seqsub (t_transitivity f2') 
               [t_ring r [] (f1',f2');
                t_seq t_symmetry 
                  (t_seq (t_ring_congr cr !rm pe1 fv fs') t_reflex_assumption)
               ]
            ];
         t_seq t_intro_eq t_cont] g in
    t_cut_merges t_end info rm fv fs g
   
and t_cut_merges t_end info rm fv fs g = 
  let m = ref Mint.empty in
  let t_end g = 
    let get i =
      let i' = try Mint.find i !m with Not_found -> i in
      oget (RState.get i' !rm) in
    let fs' = List.map get fv in
    t_end fs' g in

  let t_unify1 t_cont i1 f1 i2 f2 g = 
    let t_cont g = m := Mint.add i1 i2 !m; t_cont g in
    t_cut_subterm_eq t_cont info f1 f2 g in

  let tomatch = ref [] in
  let t_tomatch t_cont i1 f1 g = 
    let rec t_match l g = 
      match l with
      | [] -> tomatch := (i1,f1) :: !tomatch; t_cont g
      | (i2,f2)::l -> t_or (t_unify1 t_cont i1 f1 i2 f2) (t_match l) g in
    t_match !tomatch g in

  let rec t_aux ifs g =
    match ifs with
    | [] -> t_end g 
    | (i1,f1) :: ifs -> t_tomatch (t_aux ifs) i1 f1 g in
  
  t_aux (List.combine fv fs)  g

let t_alg_eq g = 
  let env = tc1_env g in
  let info = init_einfo env in
  t_alg_eq info g




