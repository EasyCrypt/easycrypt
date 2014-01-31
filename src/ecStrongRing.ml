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
  {         i_env    : env;
            kind_tbl : norm_kind Hty.t;
    mutable i_juc    : judgment_uc;
            hyp_tbl  : (int * int list * LDecl.hyps * form) option Hf.t; 
    (* hyp_tbl f -> Some (n,ns,hyps,f') means that 
         n is a node proving : hyps |- f = f' 
         ns is the remaining subgoal of n
       hyp_tbl f -> None means that f is known to be in normal form *)
  }

let init_info env juc = 
  { i_env    = env;
    kind_tbl = Hty.create 23;
    i_juc    = juc;
    hyp_tbl  = Hf.create 523;
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
    match norm_kind info f.f_ty with
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
  let pe, rm' = toring cr !rm f in
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

