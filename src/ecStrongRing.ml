(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcTypes
open EcFol
open EcEnv
open EcAlgebra
open EcLogic
open EcAlgTactic

type norm_kind = 
  | NKring  of cring * RState.rstate ref 
  | NKfield of cfield * RState.rstate ref 
  | NKdefault

type einfo = {
  i_env    : env;
  kind_tbl : norm_kind Hty.t;
}

(* hyp_tbl f -> Some = (n, ns, hyps, f') means that
 *  1. n is a node proving : hyps |- f = f'
 *  2. ns is the remaining subgoal of n
 * hyp_tbl f -> None = means that f is known to be in normal form *)
type info = {
  (*---*) i_einfo : einfo;
  mutable i_juc   : judgment_uc;
  (*---*) hyp_tbl : (int * int list * LDecl.hyps * form) option Hf.t; 
}

let init_einfo env = 
  { i_env    = env;
    kind_tbl = Hty.create 23; }

let init_info env juc = 
  { i_einfo  = init_einfo env;
    i_juc    = juc;
    hyp_tbl  = Hf.create 523; }
 
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

let add_refl info f =
  Hf.add info.hyp_tbl f None;
  None

let add_proof info n (juc,ns) =
  info.i_juc <- juc;
  let hyps, concl = get_node (juc, n) in
  let f,f' = destr_eq concl in
  let res = Some(n,ns,hyps,f') in
  Hf.add info.hyp_tbl f res;
  res

let new_goal info hyps f f' =
  new_goal info.i_juc (hyps, f_eq f f')

let get_norm f = function
  | None -> f
  | Some(_,_,_,f') -> f'

let t_subterm = function
  | None -> t_reflex ~reduce:false
  | Some (n,ns,_,_) -> t_use n ns

let t_subterms hfs = List.map t_subterm hfs

let rec t_normalize info hyps f =
  try Hf.find info.hyp_tbl f
  with Not_found ->
    match norm_kind info.i_einfo hyps f.f_ty with
    | NKring(cr,m)  -> t_normalize_ring info cr m hyps f
    | NKfield(cr,m) -> t_normalize_field info cr m hyps f 
    | NKdefault     -> t_normalize_subterm info hyps f 
      
and t_normalize_subterm info hyps f =
  match f.f_node with
  | Fapp(op, fs) ->
    let ln = List.map (t_normalize info hyps) fs in
    let fs' = List.map2 get_norm fs ln in
    let f' = f_app op fs' f.f_ty in
    if f_equal f f' then add_refl info f
    else 
      let g = new_goal info hyps f f' in
      let gs =
        t_seq_subgoal (t_congr (op,op) (List.combine fs fs', f.f_ty))
          (t_reflex :: t_subterms ln) g in
      add_proof info (snd g) gs
  | Ftuple fs ->
    let ln = List.map (t_normalize info hyps) fs in
    let fs' = List.map2 get_norm fs ln in
    let f' = f_tuple fs' in
    if f_equal f f' then add_refl info f
    else 
      let g = new_goal info hyps f f' in
      let gs = t_seq_subgoal t_split (t_subterms ln) g in
      add_proof info (snd g) gs
  | _ -> add_refl info f 
      
and t_normalize_ring info cr rm hyps f = 
  let pe, rm' = toring hyps cr !rm f in
  rm := rm';
  let fv  = Sint.elements (EcRing.fv_pe pe) in
  let fs  = List.map (fun i -> oget (RState.get i rm')) fv in
  let ln  = List.map (t_normalize_subterm info hyps) fs in
  let fs' = List.map2 get_norm fs ln in
  let f1, n_congr =
    if List.all2 f_equal fs fs' then f, None
    else
      let f1,n1,gs = n_ring_congr info.i_juc hyps cr !rm f fv fs' in
      let (juc,ns1) = t_subgoal (t_subterms ln) gs in
      info.i_juc <- juc;
      f1, Some (n1,ns1) in
  let f2, juc, n_norm = 
    let rm', f2, n2, (juc,ns2) = n_ring_norm info.i_juc hyps cr !rm f1 in
    rm := rm';
    if f_equal f1 f2 then f1, info.i_juc, None
    else f2, juc, Some(n2,ns2) in
  match n_congr, n_norm with
  | None, None -> None
  | Some (n1,ns1), None -> add_proof info n1 (juc,ns1)
  | None, Some(n2,ns2)  -> add_proof info n2 (juc,ns2)
  | Some (n1,ns1), Some(n2,ns2) ->
    info.i_juc <- juc;
    let g = new_goal info hyps f f2 in
    let gs = 
      t_seq_subgoal (t_transitivity f1) [t_use n1 ns1; t_use n2 ns2] g in
    add_proof info (snd g) gs

and t_normalize_field _info _cr _rm _hyps _f = assert false  

let t_alg_normalize f g =
  let env,hyps,_ = get_goal_e g in
  let info = init_info env (fst g) in
  let res = t_normalize info hyps f in
  let f' = get_norm f res in
  let g = if f_equal f f' then g else (info.i_juc, snd g) in
  t_on_first (t_subterm res) (t_cut (f_eq f f') g)

let t_seq_last t1 t2 g =
  t_on_last t2 (t1 g)

let rec t_lseq_last lt g =
  match lt with
  | [] -> t_id None g
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
let t_reflex_assumption g = 
  (* FIXME : we should not use _ in try *)
  let t_reflex g = try t_reflex g with _ -> t_fail g in
  t_lor [t_reflex; t_assumption; t_seq t_symmetry t_assumption] g

let t_intro_eq g = 
  let h  = LDecl.fresh_id (get_hyps g) "_" in
  t_intros_i [h] g

let is_in_hyp hyps f1 f2 =
  let is_in hyps f1 f2 = 
    try ignore (alpha_find_in_hyps (f_eq f1 f2) hyps); true
    with Not_found -> false in
  EcReduction.is_alpha_eq hyps f1 f2 ||
    is_in hyps f1 f2 || is_in hyps f2 f1

let t_ring r l (f1,f2) g = 
  t_seq (t_ring r l (f1,f2)) t_fail g 

let rec t_alg_eq info g =
  let f1, f2 = destr_eq (get_concl g) in
  t_seq (t_cut_alg_eq info f1 f2) t_reflex_assumption g

and t_cut_alg_eq info f1 f2 g =
  let hyps = get_hyps g in
  if is_in_hyp hyps f1 f2 then t_id None g
  else match norm_kind info hyps f1.f_ty with
    | NKring(cr,m)  -> t_cut_ring_eq  info cr m f1 f2 g
    | NKfield(cr,m) -> t_cut_field_eq info cr m f1 f2 g
    | NKdefault     -> t_cut_subterm_eq info f1 f2 g

and t_cut_subterm_eq info f1 f2 g =
  match f1.f_node, f2.f_node with
  | Fapp(op1,fs1), Fapp(op2,fs2) ->
    let hyps = get_hyps g in
    if EcReduction.is_alpha_eq hyps op1 op2 then 
      t_seq_last (t_lseq_last (List.map2 (t_cut_alg_eq info) fs1 fs2))
        (t_seq_subgoal (t_cut (f_eq f1 f2)) [
          t_seq 
            (t_congr (op1,op2) (List.combine fs1 fs2, f1.f_ty))
            t_reflex_assumption;
          t_intro_eq]) g
    else t_fail g
  | Ftuple fs1, Ftuple fs2 ->
    t_seq_last (t_lseq_last (List.map2 (t_cut_alg_eq info) fs1 fs2))
      (t_seq_subgoal (t_cut (f_eq f1 f2)) [
        t_seq t_split t_reflex_assumption;
        t_intro_eq]) g
  | _, _ -> t_fail g 

and t_cut_field_eq _info _cr _rm _f1 _f2 g = t_fail g 

and t_cut_ring_eq info  cr rm f1 f2 g =
  let hyps = get_hyps g in
  let pe1, rm' = toring hyps cr !rm f1 in
  let pe2, rm' = toring hyps cr rm' f2 in
  rm := rm';
  let pe = ring_simplify_pe cr [] (EcRing.PEsub(pe1,pe2)) in
  let fv = Sint.elements (EcRing.fv_pe pe) in
  let r = ring_of_cring cr in
  if fv = [] then
    t_seq_subgoal (t_cut (f_eq f1 f2)) 
      [ t_ring r [] (f1,f2) ;
        t_intro_eq ] g
  else
    let fs  = List.map (fun i -> oget (RState.get i rm')) fv in
    let gs, fs' = t_cut_merges info  rm fv fs g in
    let cut_congr f h (juc,n1 as g) =
      let hyps = get_hyps g in
      let f', n, gs = n_ring_congr juc hyps cr !rm f fv fs' in
      let (juc,ns) = t_on_goals t_reflex_assumption gs in
      t_seq_subgoal (t_cut (f_eq f f')) 
        [ t_use n ns;
          t_intros_i [h]] (juc,n1) in
    let t_trans_ring h1 h2 g = 
      let hyps = get_hyps g in
      let _, f1' = destr_eq (LDecl.lookup_hyp_by_id h1 hyps) in
      let _, f2' = destr_eq (LDecl.lookup_hyp_by_id h2 hyps) in
      t_seq_subgoal (t_transitivity f1')
        [ t_hyp h1;
          t_seq_subgoal (t_transitivity f2')
            [ t_ring r [] (f1', f2');
              t_seq t_symmetry (t_hyp h2)]] g in
    let t_end g = 
      let hyps = get_hyps g in
      let h1, h2 = as_seq2 (LDecl.fresh_ids hyps ["_";"_"]) in
      t_seq_subgoal (t_cut (f_eq f1 f2))
        [ t_lseq [ cut_congr f1 h1; cut_congr f2 h2; t_trans_ring h1 h2];
          t_intro_eq ] g in
    t_on_last t_end gs 
   
and t_cut_merges info  rm fv fs g = 
  let m = ref Mint.empty in
  let t_unify1 i1 f1 i2 f2 g = 
    let gs = t_cut_subterm_eq info  f1 f2 g in
    m := Mint.add i1 i2 !m; gs in
  let tomatch = ref [] in
  let t_tomatch i1 f1 g = 
    let rec t_match l g = 
      match l with
      | [] -> tomatch := (i1,f1) :: !tomatch; t_id None g
      | (i2,f2)::l -> t_or (t_unify1 i1 f1 i2 f2) (t_match l) g in
    t_match !tomatch g in
  let rec aux ifs g =
    match ifs with
    | [] -> t_id None g
    | (i1,f1) :: ifs -> t_seq_last (t_tomatch i1 f1) (aux ifs) g in
  let gs = aux (List.combine fv fs) g in
  let get i =
    let i' = try Mint.find i !m with Not_found -> i in
    oget (RState.get i' !rm) in
  let fs' = List.map get fv in
  gs, fs' 

let t_alg_eq g = 
  let env,_,_ = get_goal_e g in
  let info = init_einfo env in
  t_alg_eq info g
