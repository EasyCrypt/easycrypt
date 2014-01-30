open EcUtils
open EcMaps
open EcTypes
open EcFol
open EcEnv
open EcAlgebra
open EcLogic
open EcAlgTactic
(* I assume I have a tactic 
    norm_rewrite : EcIdent.t -> rw -> form -> tactic 
    the semantic is the following :
    [norm_rewrite h rw e 
       hyps |- concl ---> hyps, (h:e =e') |- concl 
     where e' is the normal form of e upto rewriting in rw *)

type norm_kind = 
  | NKring of cring * RState.rstate ref 
  | NKfield of cfield * RState.rstate ref 
  | NKdefault

type info = 
  { i_env   : env;
    hyp_tbl : (EcIdent.t option * form) Hf.t; 
    (* hyp_tbl f -> (h,f') means that h is an hypothesis proving that f = f' *)
    kind_tbl : norm_kind Hty.t
  }

let init_info env = 
  { i_env    = env;
    hyp_tbl  = Hf.create 523;
    kind_tbl = Hty.create 23;
  }
 
let get_field info ty () = 
  match Algebra.get_field ty info.i_env with
  | Some f ->
    let cr = cfield_of_field f in
    let m  = ref RState.empty in
    Some (NKfield(cr,m))
  | None -> None

let get_ring info ty () = 
  match Algebra.get_ring ty info.i_env with
  | Some r ->
    let cr = cring_of_ring r in
    let m = ref RState.empty in
    Some (NKring(cr,m))
  | None -> None

let norm_kind info ty =
  try Hty.find info.kind_tbl ty 
  with Not_found ->
    let kind = 
      odfl NKdefault (List.fpick [get_field info ty; get_ring info ty]) in
    Hty.add info.kind_tbl ty kind;
    kind

let t_intros_eq info g =
  let hyps,concl = get_goal g in
  let h = LDecl.fresh_id hyps "_" in
  let f,f' = 
    try destr_eq (fst (destr_imp concl)) 
    with DestrError _ -> assert false in
  Hf.add info.hyp_tbl f (Some h,f');
  t_intros_i [h] g

let t_add_refl info f g =
  Hf.add info.hyp_tbl f (None, f);
  t_id None g

let already_done info f = Hf.mem info.hyp_tbl f 

let get_heq info f = 
  try Hf.find info.hyp_tbl f
  with Not_found -> assert false

let get_heqs info fs = List.map (get_heq info) fs

let get_eqs info fs = List.map snd (get_heqs info fs)


let t_subterm (h,_) = omap_dfl t_hyp t_reflex h 

let t_subterms hfs = List.map t_subterm hfs

let t_trans info ht g =
  let hyps, concl = get_goal g in
  let hr = LDecl.fresh_id hyps "_" in
  let f,f' = destr_eq (LDecl.lookup_hyp_by_id ht hyps) in
  let f'', fn = destr_eq (fst (destr_imp concl)) in
  assert (f_equal f' f'');
  t_seq_subgoal (t_seq (t_intros_i [hr]) (t_cut (f_eq f fn)))
    [ t_seq_subgoal (t_transitivity f') [t_hyp ht; t_hyp hr];
      t_seq (t_clears [ht;hr]) (t_intros_eq info)] g 

let rec t_normalize info f g =
  if already_done info f then t_id None g
  else match norm_kind info f.f_ty with
  | NKring(cr,m)  -> t_normalize_ring info cr m f g
  | NKfield(cr,m) -> t_normalize_field info cr m f g
  | NKdefault     -> t_normalize_subterm info f g
      
and t_normalize_subterm info f g =
  match f.f_node with
  | Fapp(op, fs) ->
    let lt = List.map (t_normalize info) fs in
    let t_eq g =
      let hfs' = get_heqs info fs in
      let fs'  = List.map snd hfs' in
      let f' = f_app op fs' f.f_ty in
      if f_equal f f' then t_add_refl info f g
      else
        t_seq_subgoal (t_cut (f_eq f f')) 
          [ t_seq_subgoal (t_congr (op,op) (List.combine fs fs', f.f_ty))
              (t_reflex :: t_subterms hfs');
            t_intros_eq info] g in
    t_seq (t_lseq lt) t_eq g
  | Ftuple fs ->
    let lt = List.map (t_normalize info) fs in
    let t_eq g = 
      let hfs' = get_heqs info fs in
      let fs'  = List.map snd hfs' in
      let f' = f_tuple fs' in
      if f_equal f f' then t_add_refl info f g
      else
        t_seq_subgoal (t_cut (f_eq f f')) 
          [ t_seq_subgoal t_split (t_subterms hfs');
            t_intros_eq info] g in
    t_seq (t_lseq lt) t_eq g
  | _ -> t_add_refl info f g
      
and t_normalize_ring info cr rm f g = 
  let pe, rm' = toring cr !rm f in
  let fv = Sint.elements (EcRing.fv_pe pe) in
  let fs = List.map (fun i -> oget (RState.get i rm')) fv in
  let lt = List.map (t_normalize_subterm info) fs in
  let t_cut_ring_norm ht g = 
    let hyps = get_hyps g in
    let _, f' = destr_eq (LDecl.lookup_hyp_by_id ht hyps) in
    let pe, rm' = toring cr !rm f' in
    rm := rm';
    t_cut_ring_norm cr rm' [] pe g in
  let t_ring g =
    let hyps = get_hyps g in
    let ht = LDecl.fresh_id hyps "_" in
    t_lseq 
      [t_intros_i [ht];
       t_cut_ring_norm ht;
       t_trans info ht] g in
  let t_eq g =
    let hfs' = get_heqs info fs in
    let fs' = List.map snd hfs' in
    t_seq_subgoal (t_cut_ring_congr cr rm' pe fv fs')
      (t_subterms hfs' @ [t_ring]) g in
  t_seq (t_lseq lt) t_eq g


and t_normalize_field _info _cr _rm _f _g = assert false  

let t_alg_normalize f g =
  let env,_,_ = get_goal_e g in
  let info = init_info env in
  let t_end g =
    let hf = get_heq info f in
    let add_clear h s = 
      match h with
      | None -> s
      | Some h -> EcIdent.Sid.add h s in
    let toclear = 
      Hf.fold (fun _ (h,_) s -> add_clear h s) info.hyp_tbl EcIdent.Sid.empty in
    t_seq_subgoal (t_cut (f_eq f (snd hf)))
      [ t_subterm hf;
        t_clear_set toclear] g in
  t_on_last t_end (t_normalize info f g)


