open EcParsetree
open EcUtils
open EcMaps
open EcIdent
open EcTypes
open EcFol

exception UnknownSubgoal of int
exception NotAnOpenGoal of int option
exception InvalidNumberOfTactic of int * int
exception StillOpenGoal of int
exception NotReducible

let pp_error fmt = function
  | StillOpenGoal i ->
      Format.fprintf fmt "Still open goal %i, please report" i
  | UnknownSubgoal i ->
      Format.fprintf fmt "Unknown subgoal %i, please report" i
  | NotAnOpenGoal (Some i) ->
      Format.fprintf fmt "Not a open goal %i, please report" i
  | InvalidNumberOfTactic(i1,i2) -> 
      Format.fprintf fmt 
        "Invalid number of tactic, %i tactics expected, %i given" i1 i2 
  | e -> raise e

let _ = EcPException.register pp_error

type local_kind =
  | LD_var   of ty * form option
  | LD_mem   of EcMemory.memtype
  | LD_modty of EcModules.module_type * EcPath.Sm.t
  | LD_hyp   of form  (* of type bool *)

type l_local = EcIdent.t * local_kind

type hyps = {
    h_tvar  : EcIdent.t list;
    h_local : l_local list;
  }

module LDecl = struct
  type error = 
    | UnknownSymbol   of EcSymbols.symbol 
    | UnknownIdent    of EcIdent.t
    | NotAVariable    of EcIdent.t
    | NotAHypothesis  of EcIdent.t
    | CanNotClear     of EcIdent.t * EcIdent.t
    | DuplicateIdent  of EcIdent.t
    | DuplicateSymbol of EcSymbols.symbol

  exception Ldecl_error of error

  let pp_error fmt = function
    | UnknownSymbol  s  -> 
        Format.fprintf fmt "Unknown symbol %s" s
    | UnknownIdent   id -> 
        Format.fprintf fmt "Unknown ident  %s, please report" 
          (EcIdent.tostring id)
    | NotAVariable   id ->
        Format.fprintf fmt "The symbol %s is not a variable" (EcIdent.name id)
    | NotAHypothesis id ->
        Format.fprintf fmt "The symbol %s is not a hypothesis" (EcIdent.name id)
    | CanNotClear (id1,id2) ->
        Format.fprintf fmt "Cannot clear %s it is used in %s"
          (EcIdent.name id1) (EcIdent.name id2)
    | DuplicateIdent id ->
        Format.fprintf fmt "Duplicate ident %s, please report" 
          (EcIdent.tostring id)
    | DuplicateSymbol s ->
        Format.fprintf fmt 
          "An hypothesis or a variable named %s already exists" s

  let _ = EcPException.register (fun fmt exn ->
    match exn with
    | Ldecl_error e -> pp_error fmt e 
    | _ -> raise exn)

  let error e = raise (Ldecl_error e)

  let lookup s hyps = 
    try 
      List.find (fun (id,_) -> s = EcIdent.name id) hyps.h_local 
    with _ -> error (UnknownSymbol s)

  let lookup_by_id id hyps = 
    try 
      List.assoc_eq EcIdent.id_equal id hyps.h_local 
    with _ -> error (UnknownIdent id)

  let get_hyp = function
    | (id, LD_hyp f) -> (id,f)
    | (id,_) -> error (NotAHypothesis id) 

  let get_var = function
    | (id, LD_var (ty,_)) -> (id, ty)
    | (id,_) -> error (NotAVariable id) 

  let lookup_hyp s hyps = get_hyp (lookup s hyps)

  let has_hyp s hyps = 
    try ignore(lookup_hyp s hyps); true
    with _ -> false

  let lookup_hyp_by_id id hyps = snd (get_hyp (id, lookup_by_id id hyps))

  let lookup_var s hyps = get_var (lookup s hyps) 

  let lookup_var_by_id id hyps = snd (get_var (id, lookup_by_id id hyps))

  let reducible_var id hyps = 
    try 
      match lookup_by_id id hyps with
      | LD_var(_, Some _) -> true
      | _ -> false
    with _ -> false

  let reduce_var id hyps =
    try 
      match lookup_by_id id hyps with
      | LD_var(_, Some f) -> f
      | _ -> raise NotReducible
    with _ -> raise NotReducible

  let has_symbol s hyps = 
    try ignore(lookup s hyps); true with _ -> false 

  let has_ident id hyps = 
    try ignore(lookup_by_id id hyps); true with _ -> false 

  let check_id id hyps = 
    if has_ident id hyps then error (DuplicateIdent id)
    else 
      let s = EcIdent.name id in
      if s <> "_" && has_symbol s hyps then error (DuplicateSymbol s) 

  let add_local id ld hyps = 
    check_id id hyps;
    { hyps with h_local = (id,ld)::hyps.h_local }

  let fresh_id hyps s = 
    let s = 
      if s = "_" || not (has_symbol s hyps) then s
      else 
        let rec aux n = 
          let s = s ^ string_of_int n in
          if has_symbol s hyps then aux (n+1) else s in
        aux 0 in
    EcIdent.create s
      
  let fresh_ids hyps s =
    let hyps = ref hyps in
    List.map (fun s -> 
      let id = fresh_id !hyps s in
      hyps := add_local id (LD_var(tbool,None)) !hyps;
      id) s

  let clear ids hyps = 
    let fv_lk = function
      | LD_var (_,Some f) | LD_hyp f -> f.f_fv
      | _ -> Mid.empty in
    let check (id,lk) = 
      if EcIdent.Sid.mem id ids then false
      else
        let fv = fv_lk lk in
        if Mid.set_disjoint ids fv then true
        else 
          let inter = Mid.set_inter ids fv in
          error (CanNotClear(Sid.choose inter, id)) in
    { hyps with h_local = List.filter check hyps.h_local }
end


(* -------------------------------------------------------------------- *)
(*    Basic construction for building the logic                         *)
(* -------------------------------------------------------------------- *)

type prover_info = unit (* FIXME *)

type tac_pos = int EcParsetree.doption

type i_pat =
  | IPpat
  | IPif of s_pat * s_pat
  | IPwhile of s_pat 
and s_pat = (int * i_pat) list        
        (* the int represent the number of instruction to skip) *)


type rnd_tac_info = form EcParsetree.rnd_tac_info

type rule_name = 
   (* Logical rules *)
  | RN_admit
  | RN_clear        of EcIdent.Sid.t 
  | RN_prover       of prover_info
  | RN_hyp          of EcIdent.t 
  | RN_glob         of EcPath.path * EcTypes.ty list
  | RN_apply        
  | RN_cut          
  | RN_intros       of EcIdent.t list 
  | RN_exists_elim  
  | RN_exists_intro 
(*| RN_tuple_intro  of EcIdent.t list *)
  | RN_conv    

    (* Phl rules *)    
  | RN_hl_fun_def 
  | RN_hl_fun_abs   of EcFol.form
  | RN_hl_fun_upto  of EcFol.form * EcFol.form * EcFol.form
  | RN_hl_skip
  | RN_hl_wp        of tac_pos
  (* append: bool indicates direction: true backwards *)
  | RN_hl_append    of bool * tac_pos * EcFol.form * EcFol.form option
  | RN_hl_rcond     of bool option * bool * int
  | RN_hl_case      of form
  | RN_hl_while     of EcFol.form * EcFol.form option * (EcFol.form * EcFol.form) option
  | RN_hl_fission   of bool option * codepos * (int * (int * int))
  | RN_hl_fusion    of bool option * codepos * (int * (int * int))
  | RN_hl_unroll    of bool option * codepos
  | RN_hl_splitwhile of EcTypes.expr *  bool option * codepos
  | RN_hl_call      of bool option * EcFol.form * EcFol.form
  | RN_hl_swap      of bool * int * int * int
  | RN_hl_inline    of bool option * s_pat 
  | RN_hl_alias     of bool option * codepos
  | RN_hl_hoare_rnd
  | RN_hl_equiv_rnd of rnd_tac_info
  | RN_hl_conseq 
  | RN_hl_hoare_equiv 
  | RN_hl_deno      

  | RN_bhl_rnd of (EcFol.form option * EcFol.form)

and rule_arg = 
  | RA_form of EcFol.form             (* formula             *)
  | RA_id   of EcIdent.t              (* local ident         *)
  | RA_mp   of EcPath.mpath           (* module              *)
  | RA_node of int                    (* sub-derivation      *)


type rule = {
    pr_name : rule_name;
    pr_hyps : rule_arg list
  }

type l_decl = hyps * form

type pre_judgment = {
    pj_decl : l_decl;
    pj_rule : (bool * rule) option;
  }

type judgment_uc = {
    juc_count  : int;
    juc_map    : pre_judgment Mint.t;
  }

type judgment = judgment_uc

type goals = judgment_uc * int list
type goal = judgment_uc * int 

type tactic = goal -> goals 

let new_goal juc decl =
  let n = juc.juc_count in
  let pj = { pj_decl = decl; pj_rule = None; } in
  let juc = 
    { juc_count = n + 1;
      juc_map   = Mint.add n pj juc.juc_map } in
  juc, n
        
let open_juc decl = 
  fst (new_goal { juc_count = 0; juc_map = Mint.empty } decl)
     
let get_goal (juc,n) =
  try Mint.find n juc.juc_map 
  with Not_found -> raise (UnknownSubgoal n)

let get_open_goal (juc,n) = 
  let g = get_goal (juc,n) in
  if g.pj_rule <> None then raise (NotAnOpenGoal (Some n));
  g
        
let upd_juc_map juc n pj = 
  { juc with juc_map = Mint.add n pj juc.juc_map }
    
let upd_done juc =
  let is_done juc = function
    | RA_node n ->
        begin match (get_goal (juc,n)).pj_rule with
        | Some(true, _) -> true
        | _ -> false 
        end
    | _ -> true in
  let rec upd juc n =
    let pj = get_goal (juc, n) in
    match pj.pj_rule with
    | None | Some(true, _) -> juc
    | Some(false,r) ->
        let juc = List.fold_left upd_arg juc r.pr_hyps in
        if List.for_all (is_done juc) r.pr_hyps then 
          upd_juc_map juc n { pj with pj_rule = Some(true,r)}
        else juc 
  and upd_arg juc = function
    | RA_node n -> upd juc n
    | _ -> juc in
  upd juc 0

let get_first_goal juc = 
  let rec aux n = 
    let pj = get_goal (juc, n) in
    match pj.pj_rule with
    | None -> juc, n 
    | Some(d, r) -> if d then raise (NotAnOpenGoal None) else auxs r.pr_hyps
  and auxs ns = 
    match ns with
    | [] -> raise (NotAnOpenGoal None) 
    | RA_node n :: ns -> (try aux n with _ -> auxs ns)
    | _ :: ns -> auxs ns in
  aux 0

let find_all_goals juc = 
  let juc = upd_done juc in
  let rec aux ns n = 
    let pj = get_goal (juc, n) in
    match pj.pj_rule with
    | None -> n :: ns
    | Some(d, r) -> if d then ns else List.fold_left auxa ns r.pr_hyps 
  and auxa ns = function
    | RA_node n -> aux ns n
    | _ -> ns in
  juc, List.rev (aux [] 0)

let close_juc juc =
  let juc = upd_done juc in
  try let (_,n) = get_first_goal juc in raise (StillOpenGoal n) 
  with (NotAnOpenGoal None) -> juc

let upd_rule d pr (juc,n as g) = 
  let pj = get_open_goal g in
  let sg = List.pmap (function RA_node n -> Some n | _ -> None) pr.pr_hyps in
  upd_juc_map juc n { pj with pj_rule = Some(d, pr) }, sg


let upd_rule_done = upd_rule true
let upd_rule      = upd_rule false

let t_id msg (juc,n) =
  oiter msg (fun x -> Printf.fprintf stderr "DEBUG: %s\n%!" x);
  (juc, [n])

let t_on_goals t (juc,ln) = 
  let juc,ln = 
    List.fold_left (fun (juc,ln) n ->
      let juc,ln' = t (juc,n) in
      juc,List.rev_append ln' ln) (juc,[]) ln in
  juc,List.rev ln
        
let t_seq t1 t2 g = t_on_goals t2 (t1 g)
        
let rec t_lseq lt = 
  match lt with
  | [] -> t_id None
  | t1::lt -> t_seq t1 (t_lseq lt)

let t_subgoal lt (juc,ln) =
  let len1 = List.length lt in
  let len2 = List.length ln in
  if len1 <> len2 then raise (InvalidNumberOfTactic(len2, len1));
  let juc, ln = 
    List.fold_left2 (fun (juc,ln) t n ->
      let juc, ln' = t (juc, n) in
      juc, List.rev_append ln' ln) (juc,[]) lt ln in
  juc, List.rev ln

let t_on_nth t n (juc,ln) = 
  let r,n,l = try List.split_n n ln with _ -> assert false in
  let juc,ln = t (juc,n) in
  juc, List.rev_append r (List.append ln l)
        
let t_on_first (_,ln as gs) t = 
  assert (ln <> []);
  t_on_nth t 0 gs 
        
let t_on_last (_,ln as gs) t = 
  assert (ln <> []);
  t_on_nth t (List.length ln - 1) gs 

let t_seq_subgoal t lt g = t_subgoal lt (t g)

let t_try t g =
  try t g 
  with _ (* FIXME catch only some exception ? *) -> 
    t_id None g

let t_repeat t g =
  let rec aux g =
    let r = try Some (t g) with _ -> None in
    match r with 
    | None -> t_id None g
    | Some (juc, ln) ->
      t_subgoal (List.map (fun _ -> aux) ln) (juc,ln) in
  aux g

let rec t_do n t =
  if n <= 0 then t_id None
  else t_seq t (t_do (n-1) t)
