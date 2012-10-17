open EcUtil
open Ast
open Global

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Logical goals} *)

type l_proof =
  | LPtrivial
  | LPprover  (* Eventually we can give a trace of the proof,
                 but we should modify WhyCmds *)
  | LPsimplify of Fol.pred * Fol.pred * Fol.pred (* idem *)

type l_goal = {
  l_g : Fol.pred; (* A proved predicate *)
  l_proof : l_proof
}

exception CanNotProve of Fol.pred


let l_implies p q =
  let pq = Fol.pimplies p q in
  if pq = Fol.Ptrue then {l_g = pq; l_proof = LPtrivial }
  else if WhyCmds.prove pq then 
    {l_g = pq; l_proof = LPprover }
  else
    raise (CanNotProve (Fol.pimplies p q))


let l_simplify stop_first p q =
  let q' = WhyCmds.simplify_post stop_first p q in
  { l_g = Fol.pimplies (Fol.pimplies p q') (Fol.pimplies p q);
    l_proof = LPsimplify(p, q, q') }, q'

(* WARNING: unsafe, be sure that applications are correct *)
let l_trivial p =
  { l_g = p; l_proof = LPtrivial }



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Hoare Logic goals} *)

type hl_certif =
  | Cempty
  | Crandom of Fol.lvar * hl_certif
  | Ccall of Fol.lvar list * int * hl_certif
  | Ccond of hl_certif * hl_certif * hl_certif
  | Cwhile of hl_certif * hl_certif


type hl_spec = {
  hl_id : int;
  hl_pre : Fol.pred;
  hl_f : Ast.fct;
  hl_post : Fol.pred;
  hl_proof : l_goal * hl_certif
}


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 pRHL goals} *)

type rhl_rule =
  | Runknown
  | Radmitted (** see [admit] *)

  (** Logical rules *)
  | Rsub
  | Rcase of Fol.pred
  | Rcond of ApiTypes.side
  | Rifsync of (int * int)
  | Rifneg of (int * ApiTypes.side)
  | Reqobs of EcTerm.Vset2.t * Fol.pred * int list
  | Rset of bool * int * var * exp (* side,position,fresh variable,expression *)
  | Rwhile of ApiTypes.side*Fol.pred
  | Rwhilerev of ApiTypes.side*Fol.pred
  | RwhileApp of Fol.term*Fol.term*Fol.term*Fol.term*Fol.term*Fol.pred
  | RwhileAppGen
  | Rpopspec of Fol.pop_spec
  | Rpop_aspec of Fol.pop_aspec
  | Rprhl 
  | Raprhl
  | Runroll of bool * int
  | Rsplitwhile of bool * int * Ast.exp
  | Rapp
  | Rwp_asgn (** see [wp_asgn] *)
  | Rwp_simpl (** see [wp_simpl] *)
  | Rwp_call of (Fol.lvar list * Fol.lvar list * int) (** see [wp_call_equiv] *)
  | Rrand of (Fol.lvar * ((Fol.lvar * Fol.term) AstLogic.rnd_info))
  | Rpre_false (** see [pre_false] *)
  | Rpost_true (** see [post_true] *)
  | Rnot_modify of Fol.pred
  | Rsp_simpl (** see [sp_simpl] *)

  (** Program transformation rules *)
  | Rinline of bool * EcInline.info (** see [pg_inline] *)
  | Rderandomize of bool (** see [pg_derandomize] *)
  | Rswap of AstLogic.swap_info (** see [pg_swap] *)
  | Rreduce of bool * bool (* side, branch *)


type goal = {
  rhl_pre : Fol.pred;
  rhl_env1 : Global.venv;
  rhl_stmt1 : Ast.stmt;
  rhl_env2 : Global.venv;
  rhl_stmt2 : Ast.stmt;
  rhl_post : Fol.pred;
  rhl_app : (Fol.term * Fol.term) option;
  rhl_created_id : int ;
  mutable rhl_updated_id : int;
  mutable rhl_rule : rhl_rule;
  mutable rhl_subgoal : goal list;
  mutable rhl_lsubgoal : l_goal list;
}




let rhl_cntr = ref 0
let fresh_rhl_cntr () = incr rhl_cntr;!rhl_cntr


type tactic = goal -> goal list


type eager_proof =
  | Eeag_equiv of goal
  | Eeag_adv of int list
  | Eeag_auto of EcEager.eager_trace

type eager_body =
    { eb_stmt : Ast.stmt * Ast.stmt;
      eb_head : goal;
      eb_cstmt : Ast.stmt * Ast.stmt;
      eb_trace: EcEager.eager_trace;
      eb_tail : goal
    }

type spec_proof =
  | Efct_sub of int * l_goal * l_goal
  | Efct_def of goal
  | Efct_def_by_eager of eager_body

  | Efct_eager of eager_proof

  | Efct_adv of Fol.pred * int list (* invariant, spec for oracles *)
  | Efct_adv_upto of Fol.pred * Fol.pred * Fol.pred *
      int list * int list * int list
(* bad1, bad2, inv, equiv_o, hl_o1 hl_o2 *)
(*
  equiv_o : o1 ~ o2 : !bad1<1> /\ !bad2<1> /\ eq_params o1 o2 /\ inv
  ==>
  (bad1<1> <-> bad2<2>) /\
  (!bad1<1> -> eq_res o1 o2 /\ inv) ~
  hl_o1 : {bad1} o1 {bad1}   hl_o2 : {bad2} o2 {bad2}
  -----------------------------------------------------------
  (a,o1) ~ (a,o2) : (bad1<1> <-> bad2<2>) /\
  (!bad1<1> -> eq_params (a,o1) (a,o2) /\ inv)
  ==>
  (bad1<1> <-> bad2<2>) /\
  (!bad1<1> -> eq_res (a,o1) (a,o2) /\ inv) ~
*)


type spec_kind =
  | Spec of Fol.pred * Fol.pred * (Fol.term * Fol.term) option
  | Eager of Ast.stmt * Ast.stmt

type spec_fct = {
  e_name : string;
  e_id : int;
  e_f1 : Ast.fct;
  e_f2 : Ast.fct;
  e_kind : spec_kind;
  mutable e_proof : spec_proof
}


let spec_id e = e.e_id

let spec_name e = e.e_name

let hl_spec_cntr = ref (-1)

type global_state = {
  mutable hl_spec : hl_spec list; (* proved property *)
  mutable proved_spec : spec_fct list; (* proved property *)
  mutable cur_spec : spec_fct list (* unproved property *)
}


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Finding/setting global state elements} *)

let global_state = {
  hl_spec = [];
  proved_spec = [];
  cur_spec = []
}

let _ = 
  let h = ref [] in
    let save n = h := (n,(global_state.hl_spec,global_state.proved_spec)) :: !h in
    let rec restore n = match !h with
      | [] -> begin global_state.hl_spec <- []; global_state.proved_spec <- [] end 
      | (i,_)::l when (i > n) -> begin h := l; restore n end
      | (_,l)::_ -> 
        begin 
          global_state.hl_spec <- fst l; 
          global_state.proved_spec <- snd l
        end in add_register save restore



let get_proof_depth () = List.length  global_state.cur_spec


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Printing} *)

let pp_vexp fmt e =
  PpAst.g_pp_exp Fol.pp_lvar Fol.pp_lvar 0 fmt e

let equiv_of_goal g =
  g.rhl_pre, g.rhl_env1, g.rhl_stmt1, g.rhl_env2, g.rhl_stmt2, g.rhl_post, g.rhl_app


let pp_goal_pred fmt p = Format.fprintf fmt "@[%a@]" Fol.pp_pred p

let pp_goal fmt g =
  let pre,_,s1,_,s2,post, app = equiv_of_goal g in
  Format.fprintf fmt "pre   = @[%a@]@\n" pp_goal_pred pre;
  Format.fprintf fmt "stmt1 = @[%a@]@\n" (PpAst.pp_stmt ~num:true)(List.rev s1);
  Format.fprintf fmt "stmt2 = @[%a@]@\n" (PpAst.pp_stmt ~num:true)(List.rev s2);
  Format.fprintf fmt "post  = @[%a@]@\n" pp_goal_pred post;
  match app with
    | Some (skew,slack) -> 
      Format.fprintf fmt "skew = @[%a@]@\n" pp_vexp skew;
      Format.fprintf fmt "slack = @[%a@]@\n" pp_vexp slack;
    | None -> ()
        


let pp_spec fmt e =
  match e.e_kind with
    | Spec(pre,post,Some(skew,slack)) ->
      Format.fprintf fmt "@[<hov>equiv %s : %a :@;<1 2>@[<hov 2>%a@ ==>[%a,%a]@ %a@]@]" 
        e.e_name
        PpAst.pp_fct_full_name e.e_f1
        pp_goal_pred pre
        pp_vexp skew
        pp_vexp slack
        pp_goal_pred post
    | Spec(pre,post,None) ->
      Format.fprintf fmt "@[<hov>equiv %s : %a ~ %a :@;<1 2>@[%a@ ==>@ %a@]@]" e.e_name
        PpAst.pp_fct_full_name e.e_f1
        PpAst.pp_fct_full_name e.e_f2
        pp_goal_pred pre
        pp_goal_pred post
    | Eager(s1,_) ->
      Format.fprintf fmt "@[<hov>eager %s@\n  s = %a@;<1 2>  (%a|s) = (s|%a)@]@\n"
        e.e_name
        (PpAst.pp_stmt ~num:false) s1
        PpAst.pp_fct_full_name e.e_f1
        PpAst.pp_fct_full_name e.e_f2





(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {3 Finding specifications} *)

let find_all_spec f1 f2 =
  let ok st = EcTerm.eq_fct f1 st.e_f1 && EcTerm.eq_fct f2 st.e_f2 in
  List.filter ok global_state.proved_spec


let find_named_spec name =
  try Some (List.find (fun p -> p.e_name = name) global_state.proved_spec)
  with Not_found -> None

let find_id_spec id =
  try Some (List.find (fun p -> p.e_id = id) global_state.proved_spec)
  with Not_found -> None

let spec_cntr = ref (-1)
let fresh_spec_cntr () = incr spec_cntr;!spec_cntr




let find_hl_inv_spec inv f =
  let ok s =
    EcTerm.eq_fct f s.hl_f &&
      Fol.eq_pred s.hl_pre inv &&
      Fol.eq_pred s.hl_post inv in
  try Some (List.find ok global_state.hl_spec)
  with Not_found -> None

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {3 Finding subgoal}                *)

exception NoMoreSubGoal

let rec next_subgoal sg =
  match sg with
    | [] -> raise NoMoreSubGoal
    | g :: sg -> try next_goal g with NoMoreSubGoal -> next_subgoal sg

and next_goal g =
  if g.rhl_rule = Runknown then g
  else next_subgoal g.rhl_subgoal

let proved_goal g =
  try let _ = next_goal g in false with NoMoreSubGoal -> true


let cur_spec () =
  match global_state.cur_spec with
    | [] -> cannot_apply "cur_spec" "no specification to prove"
    | e :: _ -> e


let cur_goal_opt () =
  match global_state.cur_spec with
    | [] -> None
    | e :: _ ->
      match e.e_proof with
        | Efct_def g ->
          (try Some (next_goal g) with NoMoreSubGoal -> None)
        | Efct_def_by_eager eb ->
          (try Some(next_goal eb.eb_head) with NoMoreSubGoal ->
            try Some(next_goal eb.eb_tail) with NoMoreSubGoal -> None)
        | Efct_eager (Eeag_equiv g) ->
          (try Some (next_goal g) with NoMoreSubGoal -> None)
        | _ -> bug "found equiv on adversary or sub in cur_equiv?"

let cur_goal () =
  match cur_goal_opt () with
    | Some g -> g
    | None -> cannot_apply "cur_goal" "no more subgoals"

(** Count open subgoals *)
let rec num_pending_subgoals g = 
  let aux = (fun g n -> (num_pending_subgoals g) + n) in
  let num = List.fold_right aux  g.rhl_subgoal 0 in
  if g.rhl_rule = Runknown then
    1 + num
  else
    num

(** Return the number of pending related with 'normal' equiv's *)
let num_goals e = 
  match e.e_proof with
    | Efct_def g                -> num_pending_subgoals g
    | Efct_def_by_eager eb      -> (num_pending_subgoals eb.eb_head) + (num_pending_subgoals eb.eb_tail)
    | Efct_eager (Eeag_equiv g) -> num_pending_subgoals g
    | _                         -> bug "found equiv on adversary or sub in cur_equiv?"

(** Return the number of pending goals related to eager proofs*)
let rec num_goals_eager xs =
  match xs with
    | [] -> 0
    | e :: es ->
      match e.e_proof with
        | Efct_def_by_eager eb -> 
          (if (num_pending_subgoals eb.eb_head)  = 0 
           then num_pending_subgoals eb.eb_head 
           else num_pending_subgoals eb.eb_tail)
        | Efct_eager (Eeag_equiv g) -> 
          (if (num_pending_subgoals g) = 0
           then num_pending_subgoals g
           else num_goals_eager es) 
        | _ -> 0
                    
(** We assume that never exists nested equiv-eagers and equiv-non-eagers
 * In this we can't know if we are inside an eager equiv or a non-eager equiv 
 * only checking the first spec *)
let inside_eager () = 
  match global_state.cur_spec with
    | []     -> false 
    | e :: _ ->
      match e.e_proof with
        | Efct_def _          -> false
        | Efct_def_by_eager _ -> true
        | Efct_eager (Eeag_equiv _)       -> true
        | _ -> bug "found equiv on adversary or sub in cur_equiv?"


(** Print pendings subgoals according to the kind of the equiv.*)
let print_pending_subgoals fmt () =
  let g = List.fold_right (fun b n -> n + (num_goals b)) global_state.cur_spec 0
  in
  if inside_eager () then
    let l = num_goals_eager global_state.cur_spec in
     Format.fprintf fmt "Pending subgoals: (local = %d, global = %d)@\n" l g
  else
    Format.fprintf fmt "Pending subgoals: %d@\n" g 
(**)

let cur_tac t = t (cur_goal ())

let fresh_name_spec name =
  if find_named_spec name = None then name
  else
    let rec aux n =
      let name = name^"_"^(string_of_int n) in
      if find_named_spec name = None then name else aux (n+1) in
    let name' = aux 1 in
    warning "There is already a property named %s; change name to %s"
      name name';
    name'


let unsafe_add_spec e =
  let name = fresh_name_spec e.e_name in
  let e = { e with e_name=name} in
  EcUtil.verbose "@[<hov 2>Proved specification@ @[%a@].@]@." pp_spec e;
  global_state.proved_spec <- e :: global_state.proved_spec;
  e

let find_eager s1 s2 f1 f2 =
  debug 2 "[find_eager]@\n %a@\n %a@\n %a@\n %a@\n"
    (PpAst.pp_stmt ~num:false) s1 (PpAst.pp_stmt ~num:false) s2
    PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2;
  let find e =
    match e.e_kind with
      | Eager (s1',s2') ->
          EcTerm.eq_fct f1 e.e_f1 &&
          EcTerm.eq_fct f2 e.e_f2 &&
          EcTerm.eq_stmt s1 s1' &&
          EcTerm.eq_stmt s2 s2'
      | _ -> false in
  List.find find global_state.proved_spec

let eager_name f1 f2 =
  Format.sprintf "eager_%s_%s_%s_%s"
    f1.f_game.g_name f1.f_name
    f2.f_game.g_name f2.f_name

let build_eager_trace (s1,s2) (c1,c2) =
  let sMod = EcTerm.modified_stmt s1 in
  let rec sIn = EcTerm.modified_stmt s1 in
  let rec on_fct f1 f2 =
    try (find_eager s1 s2 f1 f2).e_id
    with Not_found ->   
      match f1.f_body, f2.f_body with
        | FctAdv(a1,o1), FctAdv(a2,o2) when a1.adv_name = a2.adv_name ->
          let l = List.map2 on_fct o1 o2 in
          let id = fresh_spec_cntr () in
          let s = unsafe_add_spec { e_name = eager_name f1 f2;
                                    e_id = id;
                                    e_f1 = f1; e_f2 = f2;
                                    e_kind = Eager(s1,s2);
                                    e_proof = Efct_eager (Eeag_adv l) } in
          s.e_id
        | FctDef fd1, FctDef fd2 ->
          let t =
            EcEager.build_certif on_fct sIn sMod fd1.f_def fd2.f_def in
          let id = fresh_spec_cntr () in
          let s = unsafe_add_spec { e_name = eager_name f1 f2;
                                    e_id = id;
                                    e_f1 = f1; e_f2 = f2;
                                    e_kind = Eager(s1,s2);
                                    e_proof = Efct_eager (Eeag_auto t) } in
          s.e_id
        |_, _ -> cannot_apply "eager_fct" "" in
  EcEager.build_certif on_fct sIn sMod c1 c2

(* TODO: check this for approximate specs *)
let check_proved_spec e =
  match e.e_kind, e.e_proof with
    | Spec _, Efct_def g ->
      if not (proved_goal g) then
        cannot_apply "add_spec" "The proof of %s is incomplete" (e.e_name)
    | Spec _, Efct_def_by_eager eb ->
      if proved_goal eb.eb_head && proved_goal eb.eb_tail then
        let eb =
          { eb with eb_trace = build_eager_trace eb.eb_stmt eb.eb_cstmt} in
        e.e_proof <- (Efct_def_by_eager eb)
      else cannot_apply "add_spec" "The proof of %s is incomplete" (e.e_name)
    | Eager _, Efct_eager (Eeag_equiv g) ->
      if not (proved_goal g) then
        cannot_apply "add_spec" "The proof of %s is incomplete" (e.e_name)
    | Eager _, _ -> assert false
    | _ -> ()

let add_spec e =
  check_proved_spec e;
  unsafe_add_spec e

let add_hl_spec spec =
  global_state.hl_spec <- spec :: global_state.hl_spec

let rec save () =
  match global_state.cur_spec with
    | [] -> cannot_apply "save" "no current specification"
    | e :: s ->
      ignore(add_spec e); global_state.cur_spec <- s;
      match e.e_kind with
        | Spec _ -> ()
        | Eager _ -> try save () with _ -> ()

let rec abort () =
  match global_state.cur_spec with
    | [] -> cannot_apply "abort" "no current specification"
    | e::s ->
      global_state.cur_spec <- s;
      match e.e_kind with
        | Spec _ -> e.e_name
        | Eager _ -> try abort () with _ -> e.e_name



let pre_post_app spec =
  match spec.e_kind with
    | Spec(pre, post, app) -> pre, post, app
    | _ -> cannot_apply "pre_post_app" "eager kind"

let equiv_of_spec spec =
  match spec.e_kind with
    | Spec(pre, post, app) -> 
      (spec.e_f1, spec.e_f2, pre, post, app)
    | _ -> cannot_apply "equiv_of_spec" "eager kind"



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Hoare Logic} *)

let gen_wp_hl get_spec get_inv_w c post =
  let rec aux c post cert =
    let c,_,post =
      try EcWp.wp_asgn_fct c [] post
      with EcWp.Wp_no_asgn -> c, [], post in
    match c with
      | Ast.Sasgn _ :: _ ->
        let v, c, _, post, _ = EcWp.wp_rnd_disj_fct ApiTypes.Left c [] post None in
        aux c post (Crandom (v, cert))
      | Ast.Sif(e,c1,c2)::c ->
        let p1,cert1 = aux (List.rev c1) post Cempty in
        let p2,cert2 = aux (List.rev c2) post Cempty  in
        let e = Fol.term_of_exp Fol.FVleft e in
        let post = Fol.pif e p1 p2 in
        aux c post (Ccond(cert1, cert2, cert))
      | Ast.Scall(x,f,args)::c ->
        let spec = get_spec f in
        let (v, post) = EcWp.wp_call1 x f args spec.hl_pre spec.hl_post post in
        aux c post (Ccall(v, spec.hl_id, cert))
      | Ast.Swhile(e,body) as i :: c ->
        let inv = get_inv_w i in
        let modi = EcTerm.modified_stmt body in
        let wp_body, certb = aux (List.rev body) inv Cempty in
        let mk_forall =
          EcTerm.Vset.fold
            (fun x -> Fol.forall_pred (Fol.lvar_of_var x Fol.FVleft)) modi in
        let pe = Fol.pred_of_exp Fol.FVleft e in
        let cond1 = mk_forall (Fol.pimplies (Fol.pand pe inv) wp_body) in
        let cond2 =
          mk_forall (Fol.pimplies (Fol.pand (Fol.pnot pe) inv) post) in
        let post = Fol.pand inv (Fol.pand cond1 cond2) in
        aux c post (Cwhile(certb, cert))
      | Sassert _::_ -> 
        cannot_apply "gen_wp_hl" "assert statements are not supported"
      | [] -> post, cert

  in aux c post Cempty


let fresh_hl_id () = incr hl_spec_cntr;!hl_spec_cntr

(* TODO: Improve error messages *)
let rec wp_hl_inv inv c post =
  gen_wp_hl (wp_hl_inv_fct inv) (fun _ -> inv) (List.rev c) post
and wp_hl_inv_fct inv f =
  match find_hl_inv_spec inv f with
    | Some spec -> spec
    | None ->
       (* verbose "Start proving wp_hl : %a" PpAst.pp_fct_full_name f;*)
        let def = EcTerm.fct_def f in
        try
          let wp,cert = 
            try wp_hl_inv inv def.Ast.f_def inv 
            with _ -> 
              let _, r, c = EcDerandom.derandomize_stmt 
              (Global.fun_local_venv f) def.Ast.f_def in 
              wp_hl_inv inv (List.append r c) inv in
          let l = l_implies inv wp in
          let spec =
            { hl_id = fresh_hl_id ();
              hl_pre = inv;
              hl_f = f;
              hl_post = inv;
              hl_proof = l, cert } in
          add_hl_spec spec;
         (* verbose "End proving wp_hl : %a" PpAst.pp_fct_full_name f;*)
          spec
        with NotImplementedYet _ as e -> raise e
        | CanNotProve p -> cannot_apply "hl" "cannot prove pre@\n  %a" Fol.pp_pred p




(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Generic applications} *)




(** {3 Generic transformations exported} *)


let copy_goal g =
  { g with rhl_rule = Runknown; rhl_subgoal = []; rhl_lsubgoal = [];
  rhl_created_id = fresh_rhl_cntr (); rhl_updated_id = -1}

let update_parent_goal ~rule ?(subgoal=[]) ?(lsubgoal=[]) g =
  g.rhl_rule <- rule;
  g.rhl_subgoal <- subgoal;
  g.rhl_lsubgoal <- lsubgoal;
  g.rhl_updated_id <- fresh_rhl_cntr ()

let init_goal pre env1 c1 env2 c2 post app =
  { rhl_pre = pre;
    rhl_env1 = env1;
    rhl_stmt1 = List.rev c1;
    rhl_env2 = env2;
    rhl_stmt2 = List.rev c2;
    rhl_post = post;
    rhl_app = app;
    rhl_rule = Runknown;
    rhl_subgoal = [];
    rhl_lsubgoal = [];
    rhl_created_id = fresh_rhl_cntr (); 
    rhl_updated_id = -1
  }


(** {3 Generic transformations (not exported)} *)


(** Copy the goal without rule information *)

let apply_tac_fct (f:tactic) (g:goal) =
  assert_bug (g.rhl_rule = Runknown)
    "a rule has already been applied on the goal";
  assert_bug (g.rhl_subgoal = [])
    "a Runknown rule cannot have rhl children";
  assert_bug (g.rhl_lsubgoal = [])
    "a Runknown rule cannot have logical children";
  f g


let new_spec_def ?(cur=false) name (f1,f2,pre,post,app) =
      EcTyping.check_pre f1 f2 pre;
      EcTyping.check_post f1 f2 post;
      let res =
        match f1.Ast.f_body, f2.Ast.f_body with
          | Ast.FctDef fd1, Ast.FctDef fd2 ->
            let env1 = Global.fun_local_venv f1 in
            let env2 = Global.fun_local_venv f2 in
            let s1, s2 = fd1.Ast.f_def, fd2.Ast.f_def in
            let post' =
              EcWp.wp_return Fol.FVright f2.Ast.f_res fd2.Ast.f_return post in
            let post' =
              EcWp.wp_return Fol.FVleft f1.Ast.f_res fd1.Ast.f_return post' in
            let g = init_goal pre env1 s1 env2 s2 post' app in
            { e_name = name;
              e_id = fresh_spec_cntr ();
              e_f1 = f1;
              e_f2 = f2;
              e_kind = Spec(pre,post,app);
              e_proof = Efct_def g
            }, g
          | _, _ -> cannot_apply "new_spec_def" "functions are not defined" in
      if cur then
        global_state.cur_spec <-  (fst res) :: global_state.cur_spec;
      res




let check_saved_spec spec =
  if find_id_spec (spec.e_id) = None then
    cannot_apply "check_saved" "the specification %a is not saved"
      pp_spec spec


let new_spec_sub fname spec pre post app =
  check_saved_spec spec;
  EcTyping.check_pre (spec.e_f1) (spec.e_f2) pre;
  EcTyping.check_post (spec.e_f1) (spec.e_f2) post;
  try
    let epre, epost, eapp = pre_post_app spec in
    let lpre = l_implies pre epre in
    let cond = Fol.pimplies epost post in
    let cond =
      List.fold_left (fun p v -> Fol.forall_pred (Fol.lvar_of_var v Fol.FVleft) p) 
        cond (spec.e_f1.Ast.f_res :: spec.e_f1.Ast.f_modify) in
    let cond =
      List.fold_left (fun p v -> Fol.forall_pred (Fol.lvar_of_var v Fol.FVright) p)
        cond (spec.e_f2.Ast.f_res :: spec.e_f2.Ast.f_modify) in
    let lpost = l_implies pre cond in
    begin
    match app, eapp with
      | Some (skew,slack), Some(eskew,eslack) ->
        ignore (l_implies pre (Fol.ple_real eskew skew));
        ignore (l_implies pre (Fol.ple_real eslack slack));
      | None , None -> ()
      | None, Some(skew,slack) ->
        ignore (l_implies pre (Fol.peq Global.rone skew));
        ignore (l_implies pre (Fol.peq Global.rzero slack));
      | Some(skew,slack), None -> 
        ignore (l_implies pre (Fol.ple_real Global.rone skew));
        ignore (l_implies pre (Fol.ple_real Global.rzero slack));
    end;
    { spec with
      e_name = fname ();
      e_id = fresh_spec_cntr ();
      e_kind = Spec(pre,post,app);
      e_proof = Efct_sub(spec.e_id, lpre, lpost)
    }
  with CanNotProve p -> 
    cannot_apply "new_spec_sub" "cannot prove %a" Fol.pp_pred p


let check_inv f1 f2 inv =
  match inv with
    | AstLogic.Inv_global inv ->
      EcTyping.check_pre f1 f2 inv;
      EcTyping.check_post f1 f2 inv
    | AstLogic.Inv_upto(bad1, bad2, inv) ->
      (* TODO: do this properly, i.e. bad1 only left bad2 only right *)
      EcTyping.check_pre f1 f2  (Fol.pand bad1 (Fol.pand bad2 inv));
      EcTyping.check_post f1 f2 (Fol.pand bad1 (Fol.pand bad2 inv))

let build_adv_proof inv o_spec =
  let ids = List.map (fun e -> e.e_id) o_spec in
  match inv with
    | AstLogic.Inv_global inv -> Efct_adv(inv, ids)
    | AstLogic.Inv_upto(bad1,bad2,inv) ->
      let os1 = List.map (fun e -> e.e_f1) o_spec in
      let os2 = List.map (fun e -> e.e_f2) o_spec in
      let hl_o1 = List.map (fun o -> (wp_hl_inv_fct bad1 o).hl_id) os1 in
      let bad2_left = Fol.set_left bad2 in
      let hl_o2 = List.map (fun o -> (wp_hl_inv_fct bad2_left o).hl_id) os2 in
      Efct_adv_upto(bad1,bad2,inv,ids, hl_o1, hl_o2)

let new_spec_adv name inv f1 f2 o_spec =
  check_inv f1 f2 inv;
  match f1.Ast.f_body, f2.Ast.f_body with
    | Ast.FctAdv (a1,os1), Ast.FctAdv(a2,os2) when
        a1.Ast.adv_name = a2.Ast.adv_name ->
      let rec check_oracles os1 os2 o_spec =
        match os1, os2, o_spec with
          | [], [], [] -> ()
          | o1::os1, o2::os2, spec::o_spec ->
            let spre,spost,_ = pre_post_app spec in
            let pre, post = FunLogic.build_inv_oracle_spec inv o1 o2 in
            if not (EcTerm.eq_fct o1 spec.e_f1 &&
                      EcTerm.eq_fct o2 spec.e_f2 &&
                      Fol.eq_pred pre spre &&
                      Fol.eq_pred post spost) then
              cannot_apply "new_spec_adv"
                "found specification %a@\ninstead of %a"
                pp_spec spec
                pp_spec {spec with e_f1=o1;e_f2=o2;e_kind = Spec(pre,post,None) };
            check_saved_spec spec;
            check_oracles os1 os2 o_spec

          | _, _, _ ->
            cannot_apply "new_spec_adv" "wrong number of proofs for oracles" in
      check_oracles os1 os2 o_spec;
      let pre, post = FunLogic.build_inv_spec inv f1 f2 in
      let proof = build_adv_proof inv o_spec in
      { e_name = name;
        e_id = fresh_spec_cntr ();
        e_f1 = f1;
        e_f2 = f2;
        e_kind = Spec (pre,post,None);
        e_proof = proof
      }
    | _, _ ->
      cannot_apply "new_spec_adv" "not the same abstract procedure"


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {3 Generic tactics exported} *)

let id_tac g = [g]

let fail_tac msg _g = cannot_apply "fail_tac" "%s" msg

let reset_tac g =
  g.rhl_rule <- Runknown;
  g.rhl_subgoal <- [];
  g.rhl_lsubgoal <- [];
  g.rhl_updated_id <- -1;
  [g]


let set_proof_fct gp gu =
  if copy_goal gp <> gu then
    cannot_apply "set_proof" "the two goals are different";
  gu.rhl_rule <- gp.rhl_rule;
  gu.rhl_subgoal <- gp.rhl_subgoal;
  gu.rhl_lsubgoal <- gp.rhl_lsubgoal;
  []

let set_proof_tac gp = apply_tac_fct (set_proof_fct gp)

let try_tac t g =
  try t g with CannotApply _ -> reset_tac g

let or_tac t1 t2 g =
  try t1 g with CannotApply _ -> ignore (reset_tac g); t2 g

let seq_tac t1 t2 g =
  List.flatten (List.map t2 (t1 g))

let on_subgoal_tac t lg =
  List.flatten (List.map t lg)

let subgoal_tac lt lg =
  if List.length lt = List.length lg then
    List.flatten (List.map2 (fun t g -> t g) lt lg)
  else cannot_apply "[EcDeriv.subgoal_tac]" "wrong number of tactics"

let seq_subgoal_tac t lt g =
  subgoal_tac lt (t g)

let rec repeat_tac t g =
  try_tac (seq_tac t (repeat_tac t)) g

let rec do_tac n t g =
  if n <= 0 then [g]
  else try_tac (seq_tac t (do_tac (n-1) t)) g

let admit_fct g = update_parent_goal g ~rule:Radmitted; []

let admit_tac = apply_tac_fct admit_fct

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {3 tactics implementing pRHL rules} *)

(** sub-rule *)
(*  gh = c1 ~ c2 : hpre ==> hpost    |-pre => hpre   |- hpost => post      *)
(*  ----------------------------------------------------------------- sub  *)
(*            gc = c1 ~ c2 : pre => post                                   *)

(*
let sub_fct pre post gc =
  let gh = { (copy_goal gc) with 
    rhl_pre = pre; 
    rhl_post = post }
  in
  let l1 =
    try l_implies gc.rhl_pre gh.rhl_pre
    with CanNotProve p ->
      cannot_apply "sub" "cannot prove pre@\n  %a" Fol.pp_pred p in
  let l2 =
    try l_implies gh.rhl_post gc.rhl_post
    with CanNotProve p ->
      cannot_apply "sub" "cannot prove post@\n  %a" Fol.pp_pred p in
  (* let cond_skew, cond_slack = match gh.rhl_app, gc.rhl_app with *)
  (*   | None, None -> Fol.Ptrue, Fol.Ptrue *)
  (*   | Some (gc_skew,gc_slack), Some (gh_skew,gh_slack) -> *)
  (*     ... *)


  match gh.rhl_app, gc.rhl_app with
    | None, None -> 
      let sg = [gh] in
      update_parent_goal gc ~rule:Rsub ~subgoal:sg ~lsubgoal:[l1;l2];
      sg
    | Some (gc_skew,gc_slack), Some (gh_skew,gh_slack) ->
      let l3 =
        let cond = Fol.ple_real gh_skew gc_skew in
        try l_implies gh.rhl_pre cond
        with CanNotProve p ->
          cannot_apply "sub" "cannot prove @\n  %a" Fol.pp_pred p in
      let l4 =
        let cond = Fol.ple_real gh_slack gc_slack in
        try l_implies gh.rhl_pre cond
        with CanNotProve p ->
          cannot_apply "sub" "cannot prove @\n  %a" Fol.pp_pred p in
      let sg = [gh] in
      update_parent_goal gc ~rule:Rsub ~subgoal:sg ~lsubgoal:[l1;l2;l3;l4];
      sg
    | _, _ ->
      (* TODO: other option is casting non-app to app in this case *)
      cannot_apply "sub" "cannot apply subsumption over heterogeneous goals@\n"

let sub_tac pre post = apply_tac_fct (sub_fct pre post)
*)



(** case-rule *)
(*    c1 ~ c2 : P /\ e ==> Q    c1 ~ c2 : P /\ !e ==> Q        *)
(*  ----------------------------------------------------- case *)
(*                 c1 ~ c2 : P ==> Q                           *)

let case_fct side e g =
  let env1, env2 = g.rhl_env1, g.rhl_env2 in
  let mk_pe pg_side env =
    let e, t = EcTyping.mk_var_exp env e in
    if not (EcTerm.is_var_exp e) then
      bug "Case rule: the expression should not contain random sampling";
    Unification.raise_unify_type t Ast.Tbool dummy_pos "case tactic";
    Fol.pred_of_exp pg_side e in
  let pe, npe =
    match side with
    | ApiTypes.Left -> 
        let pe = mk_pe Fol.FVleft env1 in
        pe, Fol.pnot pe
    | ApiTypes.Right -> 
        let pe = mk_pe Fol.FVright env2 in
        pe, Fol.pnot pe
    | ApiTypes.Both ->
        let pe1 = mk_pe Fol.FVleft env1 in
        let pe2 = mk_pe Fol.FVright env2 in
        Fol.pand pe1 pe2, Fol.pand (Fol.pnot pe1) (Fol.pnot pe2) in
  let pre = g.rhl_pre in
  let p_and_e = Fol.pand pre pe in
  let p_and_not_e = Fol.pand pre npe in
  let g1 =  { (copy_goal g) with rhl_pre = p_and_e } in
  let g2 =  { (copy_goal g) with rhl_pre = p_and_not_e } in
  let lg = [g1;g2] in
  update_parent_goal g ~rule:(Rcase(pe)) ~subgoal:lg;
  lg

   

let case_tac (side, e) = apply_tac_fct (case_fct side e)




let termination_goal vnt side g e inv =
  let lvenv = Global.empty_lvenv () in
  let env1 = g.rhl_env1 in
  let env2 = g.rhl_env2 in
  (* TODO: improve this ad-hoc strategy *)
  let fe,upper_bound = match vnt,e with
    | Some(fe,bd),_ -> 
      let fe, t = EcTyping.mk_var2_exp lvenv env1 env2 fe in
      (* Normally mk_var2_exp does not contain random expression ... *)
      if not (EcTerm.is_var_exp fe) then
        cannot_apply "termination_goal" 
          "the expression must not contain random sampling";
      Unification.raise_unify_type t Ast.Tint dummy_pos "case tactic";
      let bd, t = EcTyping.mk_var2_exp lvenv env1 env2 bd in
      if not (EcTerm.is_var_exp bd) then
        cannot_apply "termination_goal" 
          "the expression must not contain random sampling";
      Unification.raise_unify_type t Ast.Tint dummy_pos "case tactic";
      fe,bd
    | None, Eapp(op,[e1;e2]) when EcTerm.is_op Ast.INT_LT op ->
      let e1,e2 = Fol.term_of_exp side e1, Fol.term_of_exp side e2 in
      Eapp(Global.op_int_sub,[e2;e1]), Ecnst (Eint 0)
    | None, Eapp(op,[e1;e2]) when EcTerm.op_why op = "gt_int" ->
      let e1,e2 = Fol.term_of_exp side e1, Fol.term_of_exp side e2 in
      Eapp(Global.op_int_sub,[e1;e2]), Ecnst (Eint 0)
    | None, Eapp(op,[e1;e2]) when EcTerm.is_op Ast.INT_LE op ->
      let e1,e2 = Fol.term_of_exp side e1, Fol.term_of_exp side e2 in
      Eapp(Global.op_int_sub,[e2;e1]), Ecnst (Eint (-1))
    | None, Eapp(op,[e1;e2]) when EcTerm.op_why op = "ge_int" ->
      let e1,e2 = Fol.term_of_exp side e1, Fol.term_of_exp side e2 in
      Eapp(Global.op_int_sub,[e1;e2]), Ecnst (Eint (-1))
    | _ ->
      cannot_apply "termination_goal" "cannot prove loop termination for guard %a" PpAst.pp_exp e;
  in
  (* "variant decreases" goal *)
  let env1',vrnt = Global.fresh_var env1 "vrnt" Ast.Tint in
  let env1',bnd = Global.fresh_var env1' "bnd" Ast.Tint in
  let vrnt = Ast.Ebase (Fol.lvar_of_var vrnt Fol.FVleft) in
  let bnd = Ast.Ebase (Fol.lvar_of_var bnd Fol.FVleft) in
  let eq = Fol.peq fe vrnt in
  let lt = Fol.plt_int fe vrnt in
  let bnd_is_inv = Fol.peq bnd upper_bound in
  let e =  Fol.term_of_exp side e in
  let pe = Fol.pred_of_term e in
  let term_cond = Fol.pnot (Fol.plt_int upper_bound fe) in
  Format.printf "Proving %a\n" Fol.pp_pred (Fol.pimplies (Fol.pand inv term_cond) (Fol.pnot pe));
  let l_term = try l_implies (Fol.pand inv term_cond) (Fol.pnot pe)
    with CanNotProve p ->
      cannot_apply "termination_goal" "cannot prove@\n %a"
        Fol.pp_pred p in
  (* gdec,l_term *)
  env1',bnd_is_inv,eq,lt,l_term

let mk_exists m side =
  EcTerm.Vset.fold
    (fun x -> Fol.exists_pred (Fol.lvar_of_var x side)) m 


let while_fct (side, inv, vnt) g =
  match g.rhl_app with 
    | Some _ ->
      cannot_apply "while_fct" 
        "tactic cannot be applied to approximate goals"
    | None ->
      let pre = g.rhl_pre in
      let env1 = g.rhl_env1 in
      let env2 = g.rhl_env2 in
      let inv = EcTyping.mk_pred env1 env2 inv in
      let s1 = List.rev g.rhl_stmt1 in
      let s2 = List.rev g.rhl_stmt2 in
      let ex_pre, inv, guard, s1', s2', ss1, ss2, 
        env1',bnd_is_inv,eq,lt, lgoal =
        match side, s1, s2 with
          | ApiTypes.Left, Ast.Swhile (e,c)::cs, _ ->
            let pe = Fol.pred_of_exp Fol.FVleft e in
            let env1',bnd_is_inv,eq,lt,l_term = termination_goal vnt Fol.FVleft g e inv in
            let modif = EcTerm.modified_stmt c in
            let ex_pre = mk_exists modif Fol.FVleft pre in
            ex_pre, inv, pe, List.rev c, [], List.rev cs, List.rev s2, 
            env1',bnd_is_inv,eq,lt, [l_term]
          | ApiTypes.Right, _, Ast.Swhile (e,c)::cs ->
            let pe = Fol.pred_of_exp Fol.FVright e in
            let env1',bnd_is_inv,eq,lt,l_term = termination_goal vnt Fol.FVright g e inv in
            let modif = EcTerm.modified_stmt c in
            let ex_pre = mk_exists modif Fol.FVright pre in
            ex_pre, inv, pe, [], List.rev c, List.rev s1, List.rev cs, 
            env1',bnd_is_inv,eq,lt, [l_term]
          | ApiTypes.Both, Ast.Swhile(e1,c1)::cs1, Ast.Swhile(e2,c2)::cs2 ->
            let e1 = Fol.term_of_exp Fol.FVleft e1 in
            let e2 = Fol.term_of_exp Fol.FVright e2 in
            let p1 = Fol.pred_of_term e1 in
            let inv = Fol.pand (Fol.peq e1 e2) inv in
            let modif1 = EcTerm.modified_stmt c2 in
            let modif2 = EcTerm.modified_stmt c1 in
            let ex_pre = mk_exists modif1 Fol.FVleft (mk_exists modif2 Fol.FVright pre) in
            ex_pre, inv, p1, List.rev c1, List.rev c2, List.rev cs1, List.rev cs2,
            env1,Fol.Ptrue,Fol.Ptrue,Fol.Ptrue,[]
          | ApiTypes.Left, _, _ -> 
            cannot_apply "while_tac" 
              "not a while statement on the left-hand side"
          | ApiTypes.Right, _, _ -> 
            cannot_apply "while_tac" 
              "not a while statement on the right-hand side"
          | _ -> 
            cannot_apply "while_tac" 
              "not a pair of while statements"
      in
      let l =
        try l_implies pre inv
        with CanNotProve _ ->
          cannot_apply "while" "cannot prove@\n  (%a) =>@\n       (%a) "
            Fol.pp_pred pre Fol.pp_pred inv in

      let g1 = { (copy_goal g) with
        rhl_env1 = env1';
        rhl_pre =  Fol.pand (Fol.pand bnd_is_inv  eq) (Fol.pand ex_pre (Fol.pand inv guard));
        rhl_stmt1 = s1';
        rhl_stmt2 = s2';
        rhl_post = Fol.pand (Fol.pand bnd_is_inv lt) inv } in
      let g2 = { (copy_goal g) with
        rhl_pre = Fol.pand ex_pre (Fol.pand inv (Fol.pnot guard));
        rhl_stmt1 = ss1;
        rhl_stmt2 = ss2;} in
      let sg = [g1;g2] in
      update_parent_goal g ~rule:(Rwhile(side,inv)) ~subgoal:sg ~lsubgoal:([l]@lgoal);
      sg



let while_tac (side, inv, vnt) = apply_tac_fct (while_fct (side, inv, vnt))






let cast_goal_to_appgoal g =
  match g.rhl_app with
    | Some _ -> 
      bug "Wrong application of cast_goal_to_appgoal"
    | None ->
      { (copy_goal g) with
        rhl_app = Some (Global.rone,Global.rzero);
      }


let mk_forall m side =
  EcTerm.Vset.fold
    (fun x -> Fol.forall_pred (Fol.lvar_of_var x side)) m 

(* This tactic can be applied to non-app goals, but it's too strong *)
let whileapp_fct (alpha, delta, var, lower, upper, inv) g =
  let lvenv = Global.empty_lvenv () in
  let env1 = g.rhl_env1 in
  let env2 = g.rhl_env2 in
  let s1 = g.rhl_stmt1 in
  let s2 = g.rhl_stmt2 in
  begin match s1,s2 with
    | Ast.Swhile (guard1,c1)::s1' , Ast.Swhile (guard2,c2)::s2' ->
      
      let var, t = EcTyping.mk_var2_exp lvenv env1 env2 var in
      Unification.raise_unify_type t Ast.Tint dummy_pos "whileapp tactic";
      let lower, t = EcTyping.mk_var2_exp lvenv env1 env2 lower in
      Unification.raise_unify_type t Ast.Tint dummy_pos "whileapp tactic";
      let upper, t = EcTyping.mk_var2_exp lvenv env1 env2 upper in
      Unification.raise_unify_type t Ast.Tint dummy_pos "whileapp tactic";

      let alpha, t = EcTyping.mk_var2_exp lvenv env1 env2 alpha in
      Unification.raise_unify_type t Ast.Treal dummy_pos "whileapp tactic";
      let delta, t = EcTyping.mk_var2_exp lvenv env1 env2 delta in
      Unification.raise_unify_type t Ast.Treal dummy_pos "whileapp tactic";

      (* ghost expression for variant *)
      let venv',varnt_ghost_exp = 
        let venv',varnt_ghost = Global.fresh_var g.rhl_env1 "varnt" Ast.Tint in
        venv', Ast.Ebase (Fol.lvar_of_var varnt_ghost Fol.FVleft)
      in
      (* ghost expression for lower bound *)
      let venv',lowerb_ghost_exp = 
        let venv', lowerb_ghost = Global.fresh_var venv' "lowerb" Ast.Tint in
        venv', Ast.Ebase (Fol.lvar_of_var lowerb_ghost Fol.FVleft)
      in
      (* ghost expression for upper bound *)
      let venv',upperb_ghost_exp = 
        let venv',upperb_ghost = Global.fresh_var venv' "upperb" Ast.Tint in
        venv', Ast.Ebase (Fol.lvar_of_var upperb_ghost Fol.FVleft)
      in

      
      let eq_varnt = Fol.peq var varnt_ghost_exp in
      let plusone_varnt = Fol.peq var 
        (Eapp(Global.op_int_add,[varnt_ghost_exp;Ecnst(Eint 1)])) in

      let eq_lowerb = Fol.peq lower lowerb_ghost_exp in
      let eq_upperb = Fol.peq upper upperb_ghost_exp in

      let guard1 = Fol.term_of_exp Fol.FVleft guard1 in
      let guard2 = Fol.term_of_exp Fol.FVright guard2 in
      let p1 = Fol.pred_of_term guard1 in
      let inv = EcTyping.mk_pred env1 env2 inv in

      let sync_cond = Fol.peq guard1 guard2 in

      let inv = Fol.pand sync_cond inv in

      (* invariant preservation, variant increase, invariance of lower/upper bounds *)
      let g1 = { (copy_goal g) with
        rhl_env1 = venv';
        rhl_pre = Fol.pand inv (Fol.pand p1 (Fol.pand eq_lowerb (Fol.pand eq_upperb eq_varnt)));
        rhl_post = Fol.pand inv (Fol.pand eq_lowerb (Fol.pand eq_upperb plusone_varnt));
        rhl_stmt1 = List.rev c1;
        rhl_stmt2 = List.rev c2;
        rhl_app = Some(alpha,delta);} 
      in
      (* var >= upper -> not guard *)
      let term_cond =  Fol.pimplies (Fol.pnot (Fol.plt_int var upper)) (Fol.pnot p1) in

      let n = Eapp(Global.op_int_sub,[upper;lower]) in
      let n = Eapp(Global.op_real_of_int,[n]) in
      let skew' = Eapp(Global.op_real_pow,[alpha;n]) in
      let slack' = Eapp(Global.op_real_mul,[n;delta]) in


      let mod1 = EcTerm.modified_stmt c1 in
      let mod2 = EcTerm.modified_stmt c2 in
      let eq_var_lower = Fol.peq var lower in
      let post =
        Fol.pand inv ( Fol.pand term_cond (Fol.pand eq_var_lower (
          mk_forall mod1 Fol.FVleft (
            mk_forall mod2 Fol.FVright
                 (Fol.pimplies inv (* redundant? does it help smts? *)
                    (Fol.pimplies (Fol.pnot p1) g.rhl_post))))))
      in
      let g' = { (copy_goal g) with
        rhl_stmt1 = s1';
        rhl_stmt2 = s2';
        rhl_post = post;
        rhl_app = EcWp.reduce_app g.rhl_app (Some (skew',slack'))
      }
      in
      let sg = [g';g1] in

      update_parent_goal g 
        ~rule:(RwhileApp (alpha, delta, var, lower, upper, inv))
        ~subgoal:sg 
      ;
      sg
    | _ -> cannot_apply "whileapp_tac" "not a pair of while statements"
  end


let whileapp_tac (alpha, delta, var, lower, upper, inv) = 
  apply_tac_fct (whileapp_fct (alpha, delta, var, lower, upper, inv)) 



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


let whileappgen_fct ((_pos,v),alpha1, alpha2, var, lower, upper, p1, p2, inv) g = 
  (* TODO: lower and upper are constants. Remember to require invariance when
   * generalized to any expression
   *)

  (* TODO: check for the casting to app as in whileapp_fct *)

  match g.rhl_stmt1,g.rhl_stmt2 with
    | Ast.Swhile (guard1,c1)::s1 , Ast.Swhile (guard2,c2)::s2 ->
      let lvenv = Global.empty_lvenv () in
      let env1 = g.rhl_env1 in
      let env2 = g.rhl_env2 in

      (* type-checking: *)
      let var, t = EcTyping.mk_var2_exp lvenv env1 env2 var in
      Unification.raise_unify_type t Ast.Tint dummy_pos "whileapp tactic";
      let lvenv',lv = Global.add_lvar lvenv v Tint in
      let alpha1, t = EcTyping.mk_var2_exp lvenv' env1 env2 alpha1 in
      Unification.raise_unify_type t Ast.Treal dummy_pos "whileapp tactic";
      let alpha2, t = EcTyping.mk_var2_exp lvenv env1 env2 alpha2 in
      Unification.raise_unify_type t Ast.Treal dummy_pos "whileapp tactic";
      let inv = EcTyping.mk_pred env1 env2 inv in
      let guard1 = Fol.term_of_exp Fol.FVleft guard1 in
      let guard2 = Fol.term_of_exp Fol.FVright guard2 in
      let pguard1 = Fol.pred_of_term guard1 in
      let p1, t = EcTyping.mk_var_exp env1 p1 in
      if not (EcTerm.is_var_exp p1) then
        bug "Case rule: the expression should not contain random sampling";
      Unification.raise_unify_type t Ast.Tbool dummy_pos "whileappgen tactic";
      let p2, t = EcTyping.mk_var_exp env2 p2 in
      if not (EcTerm.is_var_exp p2) then
        bug "Case rule: the expression should not contain random sampling";
      Unification.raise_unify_type t Ast.Tbool dummy_pos "whileappgen tactic";
      let t1 = Fol.term_of_exp Fol.FVleft p1 in
      let t2 = Fol.term_of_exp Fol.FVright p2 in
      let pt1 = Fol.pred_of_term t1 in


      (* building alpha *)
      let rec fold f z n = if n<0 then z else fold f (f z n) (n-1) in
      let f z n = 
        let subst j v = if (Fol.eq_lvar v lv) then Some (Ecnst (Eint j))  else None in
        Ast.Eapp(op_real_mul,[z;Fol.change_vars_in_var_exp (subst n) alpha1])
      in
      let alpha = fold f alpha2 (upper - lower) in


      (* invariant strengthening *)
      let inv = Fol.pand (Fol.peq guard1 guard2) inv in
      let inv = Fol.pand (Fol.peq t1 t2) inv in

      let eq_var_lower = Fol.peq var (Ecnst (Eint lower)) in
      let term_cond = Fol.pimplies 
        (Fol.plt_int (Ecnst (Eint upper))  var) (Fol.pnot pguard1)
      in


      let eq_delta_zero = match g.rhl_app with 
          Some (_,delta) -> Fol.peq Global.rzero delta | _ -> Fol.Ptrue 
      in

      let (&&&) p1 p2 = Fol.pand p1 p2 in
      let (==>) p1 p2 = Fol.pimplies p1 p2 in
      let mod1 = EcTerm.modified_stmt c1 in
      let mod2 = EcTerm.modified_stmt c2 in
      let post = 
        inv
        &&&
        eq_var_lower
        &&&
        term_cond
        &&&
        eq_delta_zero
        &&&
          mk_forall mod1 Fol.FVleft (
            mk_forall mod2 Fol.FVright (
              inv &&& (Fol.pnot pguard1) ==> g.rhl_post))
      in



      let g' = { (copy_goal g) with
        rhl_stmt1 = s1;
        rhl_stmt2 = s2;
        rhl_post = post;
        rhl_app = EcWp.reduce_app (g.rhl_app) (Some (alpha,Global.rzero))
      }
      in
      (* variant increased by one, invariant preservation, P1 preservation *)
      let venv',varnt_ghost = Global.fresh_var g.rhl_env1 "varnt" Ast.Tint in
      let varnt_ghost_exp = Ast.Ebase (Fol.lvar_of_var varnt_ghost Fol.FVleft) in

      let eq = Fol.peq var varnt_ghost_exp in
      let eqplusone = Fol.peq var 
        (Eapp(Global.op_int_add,[varnt_ghost_exp;Ecnst(Eint 1)])) in
      let g1 = { (copy_goal g) with
        rhl_env1 = venv';
        rhl_pre = Fol.pand pt1 (Fol.pand eq (Fol.pand pguard1 inv));
        rhl_post = Fol.pand pt1 (Fol.pand eqplusone inv);
        rhl_stmt1 = List.rev c1;
        rhl_stmt2 = List.rev c2;
        rhl_app = None;}
      in


      
      (* case analyses *)
      let pre = Fol.pand (Fol.pnot pt1) (Fol.pand eq (Fol.pand pguard1 inv)) in
      let post = Fol.pand eqplusone inv in
      let subst v = if (Fol.eq_lvar v lv) then (Some varnt_ghost_exp) else None in
      let alpha1_j = Fol.change_vars_in_var_exp subst alpha1 in
      let g2 = { (copy_goal g) with
        rhl_env1 = venv';
        rhl_pre = pre;
        rhl_post = post;
        rhl_stmt1 = (Sassert (Ast.Eapp(Global.bool_not,[p1]))) :: List.rev c1;
        rhl_stmt2 = (Sassert (Ast.Eapp(Global.bool_not,[p2]))) :: List.rev c2;
        rhl_app = Some(alpha1_j, Global.rzero);}
      in
      let g3 = { (copy_goal g) with
        rhl_env1 = venv';
        rhl_pre = pre;
        rhl_post = post;
        rhl_stmt1 = (Sassert p1) :: List.rev c1;
        rhl_stmt2 = (Sassert p2) :: List.rev c2;
        rhl_app = Some(alpha2, Global.rzero);}
      in
      let sg = [g';g1;g2;g3] in
      update_parent_goal g  ~rule:RwhileAppGen (* TODO: fill this *)
         ~subgoal:sg
      ;
      sg
    | _ -> cannot_apply "whileapp_tac" "not a pair of while statements"

let whileappgen_tac info = 
  apply_tac_fct (whileappgen_fct info) 



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let prhl_fct g = 
  let alpha, delta = match g.rhl_app with
    | None ->
      cannot_apply "pRHL"  "Wrong tactic application"
    | Some (alpha,delta) -> alpha, delta
  in
  let lalpha = 
    try l_implies g.rhl_pre (Fol.peq Global.rone alpha)
    with CanNotProve p ->
      cannot_apply "while" "cannot prove@\n    %a\n"
        Fol.pp_pred p
  in
  let ldelta = 
    try l_implies g.rhl_pre (Fol.peq Global.rzero delta)
    with CanNotProve p ->
      cannot_apply "while" "cannot prove@\n    %a\n"
        Fol.pp_pred p
  in
  let g1 = { (copy_goal g) with 
    rhl_app = None }
  in
  update_parent_goal g ~rule:Rprhl ~subgoal:[g1] ~lsubgoal:[lalpha;ldelta];
  [g1]


let prhl_tac = apply_tac_fct prhl_fct


let aprhl_fct g = 
  begin
    match g.rhl_app with
      | None -> ()
      | Some _ -> 
        cannot_apply "pRHL"  "Wrong tactic application" ;
  end;
  let g1 = cast_goal_to_appgoal g in
  update_parent_goal g ~rule:Raprhl ~subgoal:[g1];
  [g1]



let aprhl_tac = apply_tac_fct aprhl_fct





(* 
   input: side:Fol.lv_side , t:Fol.term 
   output: Some e:Ast.exp option if Fol.term_of_exp side e
*)
let rec exp_of_term side (t:Fol.term) = 
  let exp_of_term_list ts =
    let e_opt_s = List.map (exp_of_term side) ts in
    List.fold_right 
      (fun z opt -> match z,opt with Some e,Some es -> Some (e::es) | _ -> None)
      e_opt_s (Some [])
  in
  match t with
    | Ecnst c -> Some (Ecnst c)
    | Ebase lv ->
      begin
        match lv.Fol.lv_base with
          | Fol.FVpgVar (v,side') when side'=side -> Some (Ebase v)
          | _ -> None
      end
    | Ernd _ -> bug "exp_of_term: expression must be var expression"
    | Elet ([v], t1, t2) ->
      exp_of_term side (Fol.subst_var_in_term v t1 t2)
    | Elet (lvs, Epair ts, t) when List.length lvs = List.length ts ->
      exp_of_term side (List.fold_left 
                          (fun t' (lv,t) -> Fol.subst_var_in_term lv t t')
                          t (List.combine lvs ts))
    | Epair ts ->
      (begin
        let es_opt = exp_of_term_list ts in
        match es_opt with None -> None | Some es -> Some (Epair es)
       end: Ast.exp option)
    | Eif (t1,t2,t3) ->
      begin
        match exp_of_term side t1, exp_of_term side t2, exp_of_term side t3 with
          | Some (e1:Ast.exp), Some (e2:Ast.exp), Some (e3:Ast.exp) -> 
            Some (Eif(e1,e2,e3))
          | _ -> None
      end
    | Eapp (op,ts) -> 
      begin
        let es_opt = exp_of_term_list ts in
        match es_opt with None -> None | Some es -> Some (Eapp(op,es))
      end
    | _ -> None



let twosided_popspec ((_pos,name),args) g =
  let s1 = g.rhl_stmt1 in
  let s2 = g.rhl_stmt2 in
  let popspec = 
    try Global.find_popspec name
    with _ -> 
      cannot_apply "popspec_fct"
        "popspec could not be found with that name"
  in
  let (largvars,argvars),
    (x1,pexp1,cond1),
    (x2,pexp2,cond2),
    (pre,post,app) = popspec in
  let argtypes = List.map Fol.lv_type largvars in
  if (List.length args <> List.length argvars) then
    cannot_apply "popspec_fct" "wrong number of arguments";
  let lvenv = Global.empty_lvenv () in
  let env1,env2 = g.rhl_env1,g.rhl_env2 in
  let check_argtype (pos,arg) t =
    let arg',t' = EcTyping.mk_var2_exp lvenv env1 env2 (pos,arg) in
    if not (EcTerm.is_var_exp arg') then cannot_apply "popspec" 
      "the expression should not contain probabilist expressions";
    Unification.raise_unify_type t t' pos "parameter types do not unify";
    arg'
  in
  let l_args = List.map2 check_argtype args argtypes in
  let l_subst = List.combine largvars l_args in

  let app = 
    match app with
      | Some (alpha,delta) ->
        let alpha = 
          List.fold_left (fun t (lv,t') -> Fol.subst_var_in_term lv t' t) 
            alpha l_subst
        in
        let delta = 
          List.fold_left (fun t (lv,t') -> Fol.subst_var_in_term lv t' t) 
            delta l_subst
        in
        Some (alpha,delta)
      | _ -> None
  in

  let substL = List.fold_left 
    (fun s (v,e_opt)-> match e_opt with Some e -> (v,e)::s | _ -> s ) []
    (List.combine argvars (List.map (exp_of_term Fol.FVleft) l_args))
  in
  let substR = List.fold_left 
    (fun s (v,e_opt)-> match e_opt with Some e -> (v,e)::s | _ -> s ) []
    (List.combine argvars (List.map (exp_of_term Fol.FVright) l_args))
  in


  begin
    match s1,s2,cond1,cond2 with
      | Ast.Sasgn(Ltuple [l1],e1) :: s1 , Ast.Sasgn(Ltuple [l2],e2) :: s2,
    None, None ->
        let l_subst = 
          (x1,Fol.term_of_exp Fol.FVleft (Ebase l1)) :: 
            (x2,Fol.term_of_exp Fol.FVright (Ebase l2)) :: l_subst 
        in
        let do_subst p (v,e) = Fol.let_pred [v] e p in
        let pre = List.fold_left do_subst pre l_subst in
        let post = List.fold_left do_subst post l_subst in

        (* check that the expressions coincide and/or generate eq condition*)
        let pexp1 = EcTerm.subst_exp substL pexp1 in
        let pexp2 = EcTerm.subst_exp substR pexp2 in
        if ((EcTerm.eq_exp pexp1 e1 && EcTerm.eq_exp pexp2 e2) =false) then
          cannot_apply "popspec" "Conditions %a=%a or %a=%a do not match"
            PpAst.pp_exp pexp1 PpAst.pp_exp e1 
            PpAst.pp_exp pexp2 PpAst.pp_exp e2;


        let rem_app = EcWp.reduce_app g.rhl_app app in


        let post_imp_post =
          let p = Fol.pimplies post g.rhl_post in
          let p = snd (Fol.forall_pred_with_var ~fresh:true 
                         (Fol.lvar_of_var l1 Fol.FVleft) p) in
          snd (Fol.forall_pred_with_var ~fresh:true 
                 (Fol.lvar_of_var l2 Fol.FVright) p)
        in
        let g1 = { (copy_goal g) with
          rhl_post = Fol.pand pre post_imp_post;
          rhl_app = rem_app;
          rhl_stmt1 = s1;
          rhl_stmt2 = s2;
        } in

        update_parent_goal g ~rule:(Rpopspec (popspec))
            ~subgoal:[g1];
        [g1]


      (* Version with asserts *)
      | Ast.Sassert cond1' :: Ast.Sasgn(Ltuple [l1],e1) :: s1,
        Ast.Sassert cond2' :: Ast.Sasgn(Ltuple [l2],e2) :: s2,
        Some cond1,
        Some cond2 ->


        let l_subst = 
          (x1,Fol.term_of_exp Fol.FVleft (Ebase l1)) :: 
            (x2,Fol.term_of_exp Fol.FVright (Ebase l2)) :: l_subst 
        in
        let do_subst p (v,e) = Fol.let_pred [v] e p in
        let pre = List.fold_left do_subst pre l_subst in
        let post = List.fold_left do_subst post l_subst in
        
        (* check that the expressions coincide *)
        let pexp1 = EcTerm.subst_exp substL pexp1 in
        let pexp2 = EcTerm.subst_exp substR pexp2 in
        if ((EcTerm.eq_exp pexp1 e1 && EcTerm.eq_exp pexp2 e2) =false) then
          cannot_apply "popspec" "Assigned expressions do not match";

        let rem_app = EcWp.reduce_app g.rhl_app app in

        let cond1 = EcTerm.subst_exp substL cond1 in
        let cond2 = EcTerm.subst_exp substR cond2 in
        let cond1 = Fol.pred_of_exp Fol.FVleft cond1 in
        let cond2 = Fol.pred_of_exp Fol.FVright cond2 in
        let cond1' = Fol.pred_of_exp Fol.FVleft cond1' in
        let cond2' = Fol.pred_of_exp Fol.FVright cond2' in


        let post_imp_post =
          let p = Fol.pimplies post g.rhl_post in
          let p = Fol.pand (Fol.piff cond1 cond1') p in
          let p = Fol.pand (Fol.piff cond2 cond2') p in
          let p = snd (Fol.forall_pred_with_var ~fresh:true 
                         (Fol.lvar_of_var l1 Fol.FVleft) p) in
          snd (Fol.forall_pred_with_var ~fresh:true 
                 (Fol.lvar_of_var l2 Fol.FVright) p)
        in
        let g1 = { (copy_goal g) with
          rhl_post = Fol.pand pre post_imp_post;
          rhl_app = rem_app;
          rhl_stmt1 = s1;
          rhl_stmt2 = s2;
        } in

        update_parent_goal g ~rule:(Rpopspec (popspec))
            ~subgoal:[g1];
        [g1]

      | _ ->
        cannot_apply "popspec_fct" "wrong specification application"
  end

(* One sided variants of the above *)
let onesided_popspec (side,(_pos,name),args) g =
  let s1 = g.rhl_stmt1 in
  let s2 = g.rhl_stmt2 in
  let env1, env2 = g.rhl_env1, g.rhl_env2 in
  let pop_aspec = 
    try Global.find_pop_aspec name
    with _ -> 
      cannot_apply "popspec_fct"
        "popspec could not be found with that name"
  in
  let (argvars,argtypes),
    (x,op',params),
    (pre,post) = pop_aspec in
  if (List.length args <> List.length argvars) then
    cannot_apply "popspec_fct" "wrong number of arguments";

  let check_argtype (pos,arg) t =
    let lvenv = Global.empty_lvenv () in
    let arg',t' = EcTyping.mk_var2_exp lvenv env1 env2 (pos,arg) in
    if not (EcTerm.is_var_exp arg') then
      cannot_apply "popspec" 
        "the expression should not contain random sampling";
    Unification.raise_unify_type t t' pos "parameter types do not unify";
    arg'
  in
  let args = List.map2 check_argtype args argtypes in
  let subst = List.combine argvars args in

  let do_subst p (v,e) = Fol.let_pred [v] e p in
  let do_subst_exp exp (v,e) =
    Fol.change_vars_in_var_exp (fun x ->
      if Fol.eq_lvar x v then Some e else None) exp
  in

  let l,op,args',s1',s2' = match side,s1,s2 with
    | ApiTypes.Left, Ast.Sasgn(Ltuple [l],Ernd(Ast.Rapp(op,args'))) :: s1', s2'
    | ApiTypes.Right, s1', Ast.Sasgn(Ltuple [l],Ernd(Ast.Rapp(op,args'))) :: s2'
      -> l,op,args',s1',s2'
    | _ ->
      cannot_apply "popspec_fct" "expecting probabilistic operator"
  in
  let side = match side with 
    | ApiTypes.Left -> Fol.FVleft 
    | ApiTypes.Right -> Fol.FVright 
    | ApiTypes.Both -> assert false
  in


  if (EcTerm.eq_op op op')=false then
    cannot_apply "popspec_fct" "operators do not coincide";
  (* let subst = (x,Fol.term_of_exp side (Ebase l)) :: subst in *)
  let pre = List.fold_left do_subst pre subst in

  let lres = Fol.logic_lvar "l" (l.v_type) in

  let post = Fol.let_pred [x] (Ebase lres) post in
  let post = List.fold_left do_subst post subst in
  let g_rhl_post = Fol.let_pred [Fol.lvar_of_var l side] (Ebase lres) g.rhl_post in

  (* check that the arguments coincide *)
  let params = List.map (fun v -> (Ebase v)) params in
  let params' = 
    List.map (fun v -> List.fold_left do_subst_exp v subst) params in
  let args' = List.map (Fol.term_of_exp side) args' in 
  let params_coincide = List.for_all2 Fol.eq_term args' params' in
  if (params_coincide) = false then
    cannot_apply "popspec" "Operator arguments (%a) do not match (%a)"
      (pp_list ~sep:", " (Fol.pp_term 0)) args'
      (pp_list ~sep:", " (Fol.pp_term 0)) params';

  let _,post_imp_post =
    let p = Fol.pimplies post g_rhl_post in
    Fol.forall_pred_with_var ~fresh:true lres p
  in

  let g1 = { (copy_goal g) with
    rhl_post = (Fol.pand pre (post_imp_post));
    rhl_stmt1 = s1';
    rhl_stmt2 = s2';
  } in

  update_parent_goal g ~rule:(Rpop_aspec (pop_aspec)) ~subgoal:[g1];
  [g1]



let popspec_fct (side,(_pos,name),args) g =
  match side with 
    | ApiTypes.Both -> twosided_popspec ((_pos,name),args) g
    | _ -> onesided_popspec (side,(_pos,name),args) g


let popspec_tac name = 
  apply_tac_fct (popspec_fct name) 




(* TODO: weakening tactic + strengthen tactic  *)

(* TODO: empty -> generalize to affect conditional statements *)





(* TODO: reverse version of synwhile_fct. Merge *)
let whilerev_fct (side, inv, vnt) g =
  match g.rhl_app with 
    | Some _ ->
      cannot_apply "while tactic" 
        "tactic cannot be applied to approximate goals"
    | None ->
      let env1 = g.rhl_env1 in
      let env2 = g.rhl_env2 in
      let inv = EcTyping.mk_pred env1 env2 inv in
      let s1 = g.rhl_stmt1 in
      let s2 = g.rhl_stmt2 in
      let sync_cond, guard1, guard2, s1, s2, ss1, ss2,
        env1',bnd_is_inv,eq,lt,lgoal = 
        match side, s1, s2 with
          | ApiTypes.Left, Ast.Swhile (e,c)::cs, _ ->
            let guard = Fol.pred_of_exp Fol.FVleft e in
            let env1',bnd_is_inv,eq,lt,l_term = termination_goal vnt Fol.FVleft g e inv in
            Fol.Ptrue, guard, Fol.Ptrue, List.rev c, [], cs, s2, 
            env1',bnd_is_inv,eq,lt, [l_term]
          | ApiTypes.Right, _, Ast.Swhile (e,c)::cs ->
            let guard = Fol.pred_of_exp Fol.FVright e in
            let env1',bnd_is_inv,eq,lt,l_term = termination_goal vnt Fol.FVright g e inv in
            Fol.Ptrue, Fol.Ptrue, guard, [], List.rev c, s1, cs, 
            env1',bnd_is_inv,eq,lt, [l_term]
          | ApiTypes.Both, Ast.Swhile(e1,c1)::cs1, Ast.Swhile(e2,c2)::cs2 ->
            let e1 = Fol.term_of_exp Fol.FVleft e1 in
            let e2 = Fol.term_of_exp Fol.FVright e2 in
            let guard1 = Fol.pred_of_term e1 in
            let guard2 = Fol.pred_of_term e2 in
            let equi = Fol.peq e1 e2 in
            equi, guard1, guard2, List.rev c1, List.rev c2, cs1, cs2, 
            env1, Fol.Ptrue, Fol.Ptrue, Fol.Ptrue, []
          | ApiTypes.Left, _, _ -> 
            cannot_apply "whilerev_tac" 
              "not a while statement on the left-hand side"
          | ApiTypes.Right, _, _ -> 
            cannot_apply "whilerev_tac" 
              "not a while statement on the right-hand side"
          | _ -> 
            cannot_apply "whilerev_tac" "not a pair of while statements"
      in
      let mod1 = EcTerm.modified_stmt s1 in
      let mod2 = EcTerm.modified_stmt s2 in
      let post =
        Fol.pand inv (Fol.pand sync_cond (
          mk_forall mod1 Fol.FVleft (
            mk_forall mod2 Fol.FVright
              (Fol.pimplies inv
                (Fol.pimplies (Fol.pnot guard1)
                  (Fol.pimplies (Fol.pnot guard2) g.rhl_post))))))
      in
      let g1 = { (copy_goal g) with
        rhl_env1 = env1';
        rhl_pre = Fol.pand (Fol.pand bnd_is_inv eq) 
                   (Fol.pand (Fol.pand inv guard1) guard2);
        rhl_stmt1 = s1;
        rhl_stmt2 = s2;
        rhl_post = Fol.pand (Fol.pand bnd_is_inv lt) (Fol.pand sync_cond inv) } in
      let g2 = { (copy_goal g) with
        rhl_stmt1 = ss1;
        rhl_stmt2 = ss2;
        rhl_post = post;} in
      let sg = [g1;g2] in
      update_parent_goal g ~rule:(Rwhilerev (side, inv))
          ~subgoal:sg ~lsubgoal:lgoal;
      sg


(* TODO: reverse version of synwhile_tac. Merge *)
let whilerev_tac (side,inv,vnt) = apply_tac_fct (whilerev_fct (side,inv,vnt))




(** Unrolling of while *)
let unroll_fct s k g =
  if k < 1 then cannot_apply "unroll_fct:" "position start at 1";
  let c1,c4 = 
    list_shop (k-1) (List.rev (if s then g.rhl_stmt1 else g.rhl_stmt2)) in
  let e,c2 = 
    match c4 with
      | Ast.Swhile(e,c2)::_ -> (e,c2)
      | _ -> 
        cannot_apply 
          "unroll_fct:" "the %ith instruction is not a while" k in
  let c = List.rev (c1 @ (Ast.Sif(e,c2,[])::c4)) in
  let sg = [ { (copy_goal g) with
    rhl_stmt1 = if s then c else g.rhl_stmt1;
    rhl_stmt2 = if s then g.rhl_stmt2 else c
  } ] in
  update_parent_goal g 
    ~rule:(Runroll(s,k))
        ~subgoal: sg;
  sg

let unroll_tac side k g =
  apply_tac_fct (unroll_fct side k) g




let splitwhile_fct s k e g =
  if k < 1 then cannot_apply "splitw:" "position start at 1";
  let c1,c3 = 
    list_shop (k-1) 
      (List.rev (if s then g.rhl_stmt1 else g.rhl_stmt2)) in        
  let env = if s then g.rhl_env1 else  g.rhl_env2 in
  let e, t = EcTyping.mk_var_exp env e in
  if not (EcTerm.is_var_exp e) then
    cannot_apply "splitw" 
      "the expression must not contain random sampling";
  Unification.raise_unify_type t Ast.Tbool dummy_pos "splitw tactic";
  let i = 
    try List.hd c3 
    with _ -> 
      cannot_apply "splitw:" "the %ith instruction is not a loop" k in
  let e',c2 = 
    match i with
      | Ast.Swhile(e,c2) -> e, c2
      | _ -> 
        cannot_apply "splitw:" "the %ith instruction is not a loop" k in
  let i = Ast.Swhile(Ast.Eapp (Global.bool_and,[e;e']),c2) in
  let c = List.rev (c1 @ i :: c3) in 
  let sg = 
    [ { (copy_goal g) with
      rhl_stmt1 = if s then c else g.rhl_stmt1;
      rhl_stmt2 = if s then g.rhl_stmt2 else c
    } ] in
  update_parent_goal g ~rule:(Rsplitwhile(s,k,e)) ~subgoal:sg;
  sg

let splitwhile_tac side k e = apply_tac_fct (splitwhile_fct side k e)


(** introduce a new variable *)

let set_fct s k (pos,name) typ pe g = 
  if k < 1 then cannot_apply "set_fct:" "position start at 1";
  let c1,c2 = 
    list_shop (k-1) (List.rev (if s then g.rhl_stmt1 else g.rhl_stmt2)) in
  let env = if s then g.rhl_env1 else g.rhl_env2 in
  let tv = EcTyping.mk_type_exp pos typ in
  let env',v = Global.fresh_var env name tv in
  let e, te = EcTyping.mk_rnd_exp env pe in
  let msg = "assigned expression must have the same type as the variable" in
  Unification.raise_unify_type tv te dummy_pos msg;
  let c = List.rev (c1@(Sasgn(Ltuple [v], e)::c2)) in
  let g1 = { (copy_goal g) with
             rhl_env1 = if s then env' else g.rhl_env1;
             rhl_env2 = if s then g.rhl_env2 else env';
             rhl_stmt1 = if s then c else g.rhl_stmt1;
             rhl_stmt2 = if s then g.rhl_stmt2 else c;
           } in
  let sg = [g1] in
  update_parent_goal g ~rule:(Rset(s,k,v,e) ) ~subgoal:sg ;
  sg

let set_tac side k name typ e g =
  apply_tac_fct (set_fct side k name typ e) g

  


(** one sided conditionnal rule                                 *)
(*  c1 ~ [] : P ==> e<1>  c1;c2;c4 ~ c : P ==> Q                *)
(*  --------------------------------------------rcond_true_left *)
(*   c1;if e then c2 else c3;c4 ~ c : P ==> Q                   *)
(* Remark the condition c1 ~ [] : P ==> e<1> stand for:         *)
(*   forall m1 m2, P m1 m2 -> range ([[c1]]m1) e                *)
(* It is in fact stronger, since the condition implies that     *)
(* c1 is loseless, which is not the case for range              *)
(* The other rules are symetric                                 *)

(* TODO : use hoare goal instead of relationnal goal *)
let reduce_cond_fct s k b g =
  if k < 1 then cannot_apply "reduce_cond:" "position start at 1";
  let c1,c3 = 
    list_shop (k-1) (List.rev (if s then g.rhl_stmt1 else g.rhl_stmt2)) in
  let e,c2 = 
    match c3 with
      | Ast.Sif(e,c2,c3)::c4 -> 
        e, if b then c2@c4 else c3@c4
      | Ast.Swhile(e,c2)::c4 ->
        e, if b then c2@c3 else c4
      | _ -> 
        cannot_apply 
          "reduce_cond:" "the %ith instruction is not a conditionnal" k in
  let side = if s then Fol.FVleft else Fol.FVright in
  let pe = Fol.pred_of_exp side e in
  let pe = if b then pe else Fol.pnot pe in
  let g2 = { (copy_goal g) with
    rhl_stmt1 = if s then List.rev (c1@c2) else g.rhl_stmt1;
    rhl_stmt2 = if s then g.rhl_stmt2 else List.rev (c1@c2)
  } in
  let sg = 
    if c2 = [] then [{ (copy_goal g2)
    with rhl_post = Fol.pand pe g2.rhl_post}] 
    else
      let g1 = { (copy_goal g) with
        rhl_stmt1 = if s then List.rev c1 else [];
        rhl_stmt2 = if s then [] else List.rev c1;
        rhl_post = pe
      } in
      [g1;g2] in
  update_parent_goal g ~rule:(Rreduce(s,b)) ~subgoal:sg;
  sg



let reduce_cond_tac side k b g =
  apply_tac_fct (reduce_cond_fct side k b) g

(** cond-rules *)
(*        c1;c3 ~ c4 : P /\ e<1> ==> Q                             *)
(*        c2;c3 ~ c4 : P /\ !e<1> ==> Q                            *)
(*  -------------------------------------------------- rcond-left  *)
(*        if e then c1 else c2; c3 ~ c4 : P ==> Q                  *)

(*        c1 ~ c2;c4 : P /\ e<2> ==> Q                             *)
(*        c1 ~ c3;c4 : P /\ !e<2> ==> Q                            *)
(*  -------------------------------------------------- rcond-right *)
(*        c1 ~ if e then c2 else c3;c4 : P ==> Q                   *)

(*        c1;c3 ~ c4;c6 : P /\ e1<1> /\ e2<2> ==> Q                *)
(*        c2;c3 ~ c5;c6 : P /\ !e1<1> /\ !e2<2> ==> Q              *)
(*        |- P => e1<1> = e2<2>                                    *)
(*  -------------------------------------------------- rcond-both  *)
(*        if e then c1 else c2; c3 ~                               *)
(*        if e2 then c4 else c5;c6 : P ==> Q                       *)


let cond_fct side g =
  let pre = g.rhl_pre in
  match side, g.rhl_app with
    | ApiTypes.Left, Some _ ->
      cannot_apply "cond_fct" "synchronization required for approximate goals"
    | ApiTypes.Left, None ->
      let s1 = List.rev g.rhl_stmt1 in
      begin match s1 with
        | Ast.Sif(e,c1,c2)::c3 ->
          let e = Fol.pred_of_exp Fol.FVleft e in
          let g1 = { (copy_goal g) with
            rhl_pre = Fol.pand pre e; 
            rhl_stmt1 = List.rev (c1@c3) } in
          let g2 = { (copy_goal g) with
            rhl_pre = Fol.pand pre (Fol.pnot e);
            rhl_stmt1 = List.rev (c2@c3) } in
          let sg = [g1;g2] in
          update_parent_goal g ~rule:(Rcond side) ~subgoal:sg;
          sg
        | _ -> cannot_apply "cond_fct" "not a conditionnal"
      end
    | ApiTypes.Right, Some _ ->
      cannot_apply "cond_fct" "synchronization required for approximate goals"
    | ApiTypes.Right, None ->
      let s2 = List.rev g.rhl_stmt2 in
      begin match s2 with
        | Ast.Sif (e, c2, c3)::c4 -> 
          let e = Fol.pred_of_exp Fol.FVright e in
          let g1 = { (copy_goal g) with
            rhl_pre = Fol.pand pre e; 
            rhl_stmt2 = List.rev (c2@c4) } in
          let g2 = { (copy_goal g) with
            rhl_pre = Fol.pand pre (Fol.pnot e);
            rhl_stmt2 = List.rev (c3@c4) } in
          let sg = [g1;g2] in
          update_parent_goal g ~rule:(Rcond side) ~subgoal:sg ;
          sg
        | _ -> cannot_apply "cond_fct" "not a conditionnal"
      end
    | ApiTypes.Both, _ ->
      let s1 = List.rev g.rhl_stmt1 in
      let s2 = List.rev g.rhl_stmt2 in
      begin match s1, s2 with
        | Ast.Sif(e1, c1, c2)::c3, Ast.Sif(e2, c4, c5)::c6 ->
          let e1 = Fol.term_of_exp Fol.FVleft e1 in
          let e2 = Fol.term_of_exp Fol.FVright e2 in
          let p1 = Fol.pred_of_term e1 in
          let p2 = Fol.pred_of_term e2 in
          let l =
            try l_implies pre (Fol.piff p1 p2)
            with CanNotProve p ->
              cannot_apply "cond_fct" "cannot prove@\n  %a" Fol.pp_pred p in
          let g1 = { (copy_goal g) with
            rhl_pre = Fol.pand pre (Fol.pand p1 p2);
            rhl_stmt1 = List.rev (c1@c3);
            rhl_stmt2 = List.rev (c4@c6)
          } in
          let g2 = { (copy_goal g) with
            rhl_pre = 
              Fol.pand pre (Fol.pand (Fol.pnot p1) (Fol.pnot p2));
            rhl_stmt1 = List.rev (c2@c3);
            rhl_stmt2 = List.rev (c5@c6)
          } in
          let sg = [g1;g2] in
          update_parent_goal g ~rule:(Rcond side) ~subgoal:sg ~lsubgoal:[l];
          sg
        | _ -> cannot_apply "cond_fct" "not a conditionnal"
      end

let cond_tac side = apply_tac_fct (cond_fct side)



(******************************************************************************)
(** If-sync rule                                                              *)
(*                                                                            *)
(*        c1;assert(e);c2;c4 ~ d1;assert(f)d2;d4 : P ==> Q                    *)
(*        c2;assert(!e);c3;c4 ~ d1;assert(!f)d3;d4 : P ==> Q                  *)
(*        c1~d1 : P ==> e<1> <=> f<2>)                                        *)
(*  ------------------------------------------------------------- if-sync     *)
(*      c1; if e then c2 else c3; c4 ~  d1; if f then d2 else d3; d4: P ==> Q *)
(*                                                                            *)
(******************************************************************************)

let ifsync_fct k1 k2 g = 
  if (k1 < 1 || k2 < 1) then cannot_apply "ifsync:" 
    "position start at 1"; 
  match (list_shop (k1-1) (List.rev g.rhl_stmt1),
         list_shop (k2-1) (List.rev g.rhl_stmt2)) with
	    ((c1,(ifStmt1::c4)), (d1,(ifStmt2::d4))) -> 
	      begin
	        match (ifStmt1, ifStmt2) with
	          | Ast.Sif(e, c2, c3), Ast.Sif(f, d2, d3) ->
		          let g1 = { (copy_goal g) with
		            rhl_stmt1 = List.rev (c1@[Ast.Sassert e]@c2@c4);
		            rhl_stmt2 = List.rev (d1@[Ast.Sassert f]@d2@d4);
		          } in
		          let g2 = { (copy_goal g) with
		            rhl_stmt1 = List.rev 
		              (c1@[Ast.Sassert 
			                    (Ast.Eapp(Global.bool_not,[e]))]@c3@c4);
		            rhl_stmt2 = List.rev 
		              (d1@[Ast.Sassert 
			                    (Ast.Eapp(Global.bool_not,[f]))]@d3@d4);
		          } in
		          let g3 = { (copy_goal g) with
		            rhl_stmt1 = List.rev c1;
		            rhl_stmt2 = List.rev d1;
		            rhl_post = (Fol.peq (Fol.term_of_exp Fol.FVleft e) 
				                      (Fol.term_of_exp Fol.FVright f));
		          } in
		          let sg = [g1;g2;g3] in
		          update_parent_goal g ~rule:(Rifsync (k1,k2)) ~subgoal:sg;
		          sg;
	          | _ -> cannot_apply "ifsync" 
		          "wrong position for ifs"
	      end
	  | _ -> cannot_apply "ifsync" 
	    "wrong position for ifs"


let ifsync_tac k1 k2 = apply_tac_fct (ifsync_fct k1 k2)

(******************************************************************************)
(** If-neg rule                                                               *)
(*                                                                            *)
(*      c1; if ~ e then c3 else c2; c4 ~  d : P ==> Q                         *)
(*  ------------------------------------------------------------- if-negL     *)
(*      c1; if e then c2 else c3; c4 ~  d : P ==> Q                           *)
(*                                                                            *)
(******************************************************************************)

(* TODO : move this *)
let tnot e = 
  match e with
  | Ast.Eapp (op, [e]) when EcTerm.is_op Ast.NOT op -> e
  | Ast.Eapp (op, [e1;e2]) when EcTerm.is_op Ast.INT_LT op ->
      Ast.Eapp(Global.op_int_le, [e2;e1])
  | Ast.Eapp (op, [e1;e2])  when EcTerm.is_op Ast.INT_LE op ->
      Ast.Eapp(Global.op_int_lt, [e2;e1])
  | _ -> Ast.Eapp(Global.bool_not,[e]) 

let ifneg_fct side k g =
  if (k < 1) then cannot_apply "ifneg:" "position start at 1";
  let stmt = List.rev (if side then g.rhl_stmt1 else g.rhl_stmt2) in 
  match list_shop (k-1) stmt with
    | c1, Ast.Sif(e, c2, c3)::c4 ->
	    let e' = tnot e in
	    let g' = if side then
	        { (copy_goal g) with 
	          rhl_stmt1 = List.rev (c1@(Ast.Sif(e', c3, c2)::c4))} else 
	        { (copy_goal g) with 
	          rhl_stmt2 = List.rev (c1@(Ast.Sif(e', c3, c2)::c4))} in
	    let sg = [g'] in
	    update_parent_goal g 
	      ~rule:(Rifneg (k,if side then ApiTypes.Left else ApiTypes.Right)) 
	          ~subgoal:sg;
	    sg;
    | _ -> cannot_apply "ifneg" "no if statement at pos %i" k

let ifneg_tac b k = apply_tac_fct (ifneg_fct b k)
(** EqObs_in *)

let in_eqs side l eqs = 
  match l with
  | Ltuple l -> 
      List.exists 
        (fun u ->
          EcTerm.Vset2.exists (fun (v,v') -> 
            EcTerm.eq_var u (if side then v else v')) eqs)
        l
  | Lupd(u,_) -> 
      EcTerm.Vset2.exists (fun (v,v') -> EcTerm.eq_var u (if side then v else v')) eqs 

let in1_eqs = in_eqs true 
let in2_eqs = in_eqs false 

let rec add_eqs e1 e2 eqs = 
  match e1, e2 with
  | Ecnst _, Ecnst _ ->
      if EcTerm.eq_exp e1 e2 then eqs
      else user_error "eqobs_in does not apply" 
  | Ebase x1, Ebase x2 -> EcTerm.Vset2.add (x1, x2) eqs
  | Ernd r1, Ernd r2 -> addr_eqs r1 r2 eqs 
  | Eapp (op1, args1), Eapp(op2,args2) ->
      if EcTerm.eq_op op1 op2 then adds_eqs args1 args2 eqs
      else user_error "eqobs_in does not apply" 
  | Elet (l1,e11,e12), Elet(l2,e21,e22) ->
      let eqs = add_eqs e12 e22 eqs in
      let l1, l2 = Ltuple l1, Ltuple l2 in
      let eqs = remove_eqs l1 l2 eqs in
      if in1_eqs l1 eqs || in2_eqs l2 eqs then
        user_error "eqobs_in does not apply" 
      else add_eqs e11 e21 eqs 
  | Epair le1, Epair le2 -> adds_eqs le1 le2 eqs
  | Eif(e1,e11,e12), Eif(e2,e21,e22) ->
      let eqs1 = add_eqs e11 e21 eqs in
      let eqs2 = add_eqs e12 e22 eqs in
      add_eqs e1 e2 (EcTerm.Vset2.union eqs1 eqs2)
  | _, _ -> user_error "eqobs_in does not apply" 
and adds_eqs l1 l2 eqs = 
  List.fold_left2 (fun eqs e1 e2 -> add_eqs e1 e2 eqs) eqs l1 l2
(*  match l1, l2 with
  | [], [] -> eqs
  | e1::l1, e2::l2 -> adds_eqs l1 l2 (add_eqs e1 e2 eqs)
  | _, _ -> user_error "eqobs_in does not apply" *)
and addr_eqs r1 r2 eqs =
  match r1, r2 with
  | Rinter(e11,e12), Rinter(e21,e22) ->
      add_eqs e11 e21 (add_eqs e12 e22 eqs)
  | Rbool, Rbool -> eqs
  | Rbitstr e1, Rbitstr e2 -> add_eqs e1 e2 eqs
  | Rexcepted (r1,e1), Rexcepted(r2,e2) -> add_eqs e1 e2 (addr_eqs r1 r2 eqs)
  | Ast.Rapp(op1,args1), Ast.Rapp(op2,args2) ->
      if EcTerm.eq_op op1 op2 then adds_eqs args1 args2 eqs
      else user_error "eqobs_in does not apply"
  | _, _ -> user_error "eqobs_in does not apply" 
and remove_eqs l1 l2 eqs =
  let rec aux l1 l2 eqs = 
    match l1, l2 with
    | [], [] -> eqs
    | v1::l1, v2::l2 ->
        if EcTerm.seq_type v1.v_type v2.v_type then
          aux l1 l2 (EcTerm.Vset2.remove (v1,v2) eqs)
        else user_error "eqobs_in does not apply"
    | _, _ -> user_error "eqobs_in does not apply" in
  match l1, l2 with
  | Ltuple l1, Ltuple l2  -> aux l1 l2 eqs
  | Lupd(u1,e1), Lupd(u2,e2) -> add_eqs e1 e2 (aux [u1] [u2] eqs) 
  | _, _ -> user_error "eqobs_in does not apply" 

let eqobs_in on_call inv c1 c2 eqs =
  let in_fv fv l = 
    match l with
    | Ltuple l  -> List.exists (fun u -> EcTerm.Vset.mem u fv) l
    | Lupd(u,_) -> EcTerm.Vset.mem u fv in
  let fv1, fv2 = Fol.fv_pred inv in
  let in_fv1 = in_fv fv1 in
  let in_fv2 = in_fv fv2 in
  
  let rec eqobs_in c1 c2 eqs =
    match c1, c2 with
    | Sasgn(l1,_) :: c1 , c2 when not (in1_eqs l1 eqs) && not (in_fv1 l1) ->
        eqobs_in c1 c2 eqs
    | c1, Sasgn(l2,_)::c2 when not (in2_eqs l2 eqs) && not (in_fv2 l2) ->
        eqobs_in c1 c2 eqs
    | [], _ -> c1,c2,eqs
    | _, [] -> c1,c2,eqs
    | i1::c1', i2::c2' ->
        match eqobs_in_i i1 i2 eqs with
        | Some eqs -> eqobs_in c1' c2' eqs
        | _ -> c1, c2, eqs

  and eqobs_in_i i1 i2 eqs =
    match i1, i2 with
    | Sasgn(l1,e1), Sasgn(l2,e2) when 
        not (in_fv1 l1 || in_fv2 l2) ->
          begin 
            try Some (add_eqs e1 e2 (remove_eqs l1 l2 eqs))
            with _ -> None
          end
    | Sif(e1,c11,c12), Sif(e2,c21,c22) ->
        let res1 = eqobs_in (List.rev c11) (List.rev c21) eqs in
        let res2 = eqobs_in (List.rev c12) (List.rev c22) eqs in
        begin 
          try match res1, res2 with
          | ([],[],eqs1), ([],[],eqs2) ->
              let eqs = EcTerm.Vset2.union eqs1 eqs2 in
              Some (add_eqs e1 e2 eqs)
          | _, _ -> None
          with _ -> None 
        end
    | Swhile(e1,c11), Swhile(e2,c21) ->
        let c11, c21 = List.rev c11, List.rev c21 in
        let rec aux eqs1 = 
          match eqobs_in c11 c21 eqs1 with
          | ([],[],eqs2) ->
              if EcTerm.Vset2.subset eqs2 eqs1 then Some eqs1
              else aux (EcTerm.Vset2.union eqs2 eqs1) 
          | _ -> None in
        begin match try Some (add_eqs e1 e2 eqs) with _ -> None with
        | Some eqs -> aux eqs
        | _ -> None
        end
    | Scall(l1,f1,args1), Scall(l2,f2,args2)
      when not (in_fv1 l1 || in_fv2 l2) ->
        begin 
          try
            let gin,gout = on_call f1 f2 in
            let out = remove_eqs l1 l2 eqs in
            let other = EcTerm.Vset2.diff out gout in
            if in1_eqs (Ltuple f1.f_modify) other 
               || in2_eqs (Ltuple f2.f_modify) other then
              raise Not_found;
            let eqs = EcTerm.Vset2.union gin other in 
            Some (adds_eqs args1 args2 eqs)
          with _ -> None
        end
    | Sassert e1, Sassert e2 ->
        begin 
          try Some (add_eqs e1 e2 eqs) with _ -> None
        end
    | _, _ -> None in
  eqobs_in c1 c2 eqs    

let rec get_eqs p eqs =
  match p with
  | Fol.Papp(op,[Ast.Ebase v1;Ast.Ebase v2]) when Fol.is_eq_pred op ->
      begin match v1.Fol.lv_base, v2.Fol.lv_base with
        | Fol.FVpgVar(x1,Fol.FVleft), Fol.FVpgVar(x2,Fol.FVright) when x1.v_glob && x2.v_glob ->
            EcTerm.Vset2.add (x1,x2) eqs
        | Fol.FVpgVar(x2,Fol.FVright), Fol.FVpgVar(x1,Fol.FVleft) when x1.v_glob && x2.v_glob ->
            EcTerm.Vset2.add (x1,x2) eqs
        | _ -> eqs 
      end
  | Fol.Pand (p1, p2) -> get_eqs p1 (get_eqs p2 eqs)
  | _ -> eqs

let eqobs_in_fct info (eqs, inv) g =
  let pred_of_eqs s =
    EcTerm.Vset2.fold (fun (v1, v2) eqs ->
      let t1 = Fol.term_of_exp Fol.FVleft (Ebase v1) in
      let t2 = Fol.term_of_exp Fol.FVright (Ebase v2) in
      Fol.pand (Fol.peq t1 t2) eqs) s Fol.Ptrue in
  let post' = Fol.pand (pred_of_eqs eqs) inv in
  let lg = ref [l_implies post' g.rhl_post] in
  let mk_info id = 
    match find_id_spec id with
    | None -> user_error "eqobs_in does not apply"
    | Some s -> 
        let pre,post = 
          match s.e_kind with
          | Spec(pre,post,None) -> pre,post
          | _ -> user_error "eqobs_in does not apply" in
        let gin = get_eqs pre EcTerm.Vset2.empty in
        let gout = get_eqs post EcTerm.Vset2.empty in
        let _, post' = 
          FunLogic.build_inv_spec 
            (AstLogic.Inv_global (Fol.pand (pred_of_eqs gout) inv)) s.e_f1 s.e_f2 in
        let pre', _ = 
          FunLogic.build_inv_spec 
            (AstLogic.Inv_global (Fol.pand (pred_of_eqs gin) inv)) s.e_f1 s.e_f2 in
        try 
          lg := (l_implies pre' pre) :: (l_implies post post') :: !lg;
          ((s.e_f1,s.e_f2), (gin,gout))
        with CanNotProve p -> 
          user_error "eqobs_in does not apply : can not proof %a" Fol.pp_pred p in
  let info' = List.map mk_info info in
  let on_call f1 f2 =
    let test ((f1',f2'),_) = 
      EcTerm.eq_fct f1 f1' && EcTerm.eq_fct f2 f2' in
    snd (List.find test info') in
  let (c1,c2,eqs) = eqobs_in on_call inv g.rhl_stmt1 g.rhl_stmt2 eqs in
  let g1 = { (copy_goal g) with
             rhl_stmt1 = c1; 
             rhl_stmt2 = c2;
             rhl_post = Fol.pand (pred_of_eqs eqs) inv
           } in
  let sg = [g1] in
  update_parent_goal g ~rule:(Reqobs(eqs,inv,info)) 
    ~lsubgoal:!lg ~subgoal:sg;
  sg

let eqobs_in_tac info_call info = 
  apply_tac_fct (eqobs_in_fct info_call info)
  





(** app-rule *)
(*  c1~c3 : P ==> Q    c2~c4 : Q ==> R
    ----------------------------------
    c1;c2 ~ c3;c4 : P => R            *)

let app_fct (k1,k2) q app g =
  (* TODO: check that q is well-typed in g *)
  let app1,app2,lsgoals = 
    match g.rhl_app, app with
      | Some(alpha,delta), Some(alpha1,delta1,alpha2,delta2) ->
        let lvenv = Global.empty_lvenv () in
        let env1 = g.rhl_env1 in
        let env2 = g.rhl_env2 in
        let alpha1, t = EcTyping.mk_var2_exp lvenv env1 env2 alpha1 in
        Unification.raise_unify_type t Ast.Treal dummy_pos "app tactic";
        let delta1, t = EcTyping.mk_var2_exp lvenv env1 env2 delta1 in
        Unification.raise_unify_type t Ast.Treal dummy_pos "app tactic";
        let alpha2, t = EcTyping.mk_var2_exp lvenv env1 env2 alpha2 in
        Unification.raise_unify_type t Ast.Treal dummy_pos "app tactic";
        let delta2, t = EcTyping.mk_var2_exp lvenv env1 env2 delta2 in
        Unification.raise_unify_type t Ast.Treal dummy_pos "app tactic";

        let alpha' = Eapp(Global.op_real_mul,[alpha1;alpha2]) in
        let l_alpha = 
          try l_implies Fol.Ptrue (Fol.ple_real alpha' alpha)
          with CanNotProve p ->
            cannot_apply "app" "cannot prove@\n    %a\n"
              Fol.pp_pred p
        in
        let delta' = Eapp(Global.op_real_add,[delta1;
                          Eapp(Global.op_real_mul,[alpha1;delta2])])
        in
        let delta'' = Eapp(Global.op_real_add,[delta2;
                           Eapp(Global.op_real_mul,[alpha2;delta1])])
        in
        let l_delta = 
          try l_implies Fol.Ptrue (Fol.pand (Fol.ple_real delta' delta) 
                                     (Fol.ple_real delta'' delta))
          with CanNotProve p ->
            cannot_apply "app" "cannot prove@\n    %a\n"
              Fol.pp_pred p
        in
        Some(alpha1,delta1),Some(alpha2,delta2),[l_alpha;l_delta]
      | None, None ->
        None, None, []
      | _ -> cannot_apply "app" "wrong tactic arguments"
  in
  let c1, c2 = list_shop k1 (List.rev (g.rhl_stmt1)) in
  let c3, c4 = list_shop k2 (List.rev (g.rhl_stmt2)) in
  let g1 = { (copy_goal g) with
    rhl_stmt1 = List.rev c1;
    rhl_stmt2 = List.rev c3;
    rhl_post = q;
    rhl_app = app1
  } in
  let g2 = { (copy_goal g) with
    rhl_stmt1 = List.rev c2;
    rhl_stmt2 = List.rev c4;
    rhl_pre = q;
    rhl_app = app2
  } in
  let sg = [g1;g2] in
  update_parent_goal g ~rule:Rapp ~subgoal:sg ~lsubgoal:lsgoals;
  sg

let app_tac k q app = apply_tac_fct (app_fct k q app)



(** wp_asgn-rule *)
let gen_wp_fct ?(pos=None) wp rule g =
  let c1, c2, c1', c2' = match pos with 
    | None -> [], [], g.rhl_stmt1, g.rhl_stmt2
    | Some (pos1,pos2) -> 
      let c1,c2 = List.rev g.rhl_stmt1, List.rev g.rhl_stmt2 in
      if pos1<1 || pos2<1 then cannot_apply "wp:" "position starts at 1";
      let c1,c1' = list_shop pos1 c1 in
      let c2,c2' = list_shop pos2 c2 in
      List.rev c1, List.rev c2, List.rev c1', List.rev c2'
  in
  let c1', c2', post = wp c1' c2' g.rhl_post in
  let g1 = { (copy_goal g) with
    rhl_stmt1 = c1' @ c1;
    rhl_stmt2 = c2' @ c2;
    rhl_post = post } in
  let sg = [g1] in
  update_parent_goal g ~rule:rule ~subgoal:sg;
  sg




let gen_wp_fct_info wp rule g =
  let info, c1, c2, post, app = wp g.rhl_stmt1 g.rhl_stmt2 g.rhl_post g.rhl_app in
  let g1 = { (copy_goal g) with
    rhl_stmt1 = c1;
    rhl_stmt2 = c2;
    rhl_post = post;
    rhl_app = app } in
  let sg = [g1] in
  update_parent_goal g ~rule:(rule info) ~subgoal:sg;
  sg

let wp_asgn_fct g =
  match g.rhl_app with 
    | Some _ ->
      cannot_apply "gen_wp_fct" "cannot be applied to approximate goals"
    | None ->
      try gen_wp_fct EcWp.wp_asgn_fct Rwp_asgn g
      with EcWp.Wp_no_asgn ->
        cannot_apply "wp_asgn" "no assignments to process"

let wp_asgn_tac = apply_tac_fct wp_asgn_fct


(** wp_simpl-rule *)

let wp_simpl_fct ?(pos=None) g =
  let wp = match g.rhl_app with
    | Some _ -> EcWp.wp_simpl_fct_app
    | None -> EcWp.wp_simpl_fct 
  in
  try gen_wp_fct ~pos wp Rwp_simpl g
  with EcWp.Wp_nothing_done ->
    cannot_apply "wp_simpl" "nothing to do"

let wp_simpl_tac ?(pos=None) = apply_tac_fct (wp_simpl_fct ~pos)



(** sp_simpl-rule *)

let gen_sp_fct ?(pos=None) sp rule g =
  let c1,c2 = List.rev g.rhl_stmt1, List.rev g.rhl_stmt2 in
  let c1, c2, c1', c2' = match pos with 
    | None -> c1, c2, [], []
    | Some (pos1,pos2) -> 
      if pos1<0 || pos2<0 then cannot_apply "sp:" "only positive arguments are accepted";
      let c1,c1' = list_shop pos1 c1 in
      let c2,c2' = list_shop pos2 c2 in
      c1, c2, c1', c2'
  in
  let c1, c2, pre = sp c1 c2 g.rhl_pre in
  let g1 = { (copy_goal g) with
    rhl_stmt1 = List.rev (c1@c1');
    rhl_stmt2 = List.rev (c2@c2');
    rhl_pre = pre } in
  let sg = [g1] in
  update_parent_goal g ~rule:rule ~subgoal:sg;
  sg

let gen_sp_fct_info sp rule g =
  let c1,c2 = List.rev g.rhl_stmt1, List.rev g.rhl_stmt2 in
  let info, c1, c2, pre, app = sp c1 c2 g.rhl_pre g.rhl_app in
  let g1 = { (copy_goal g) with
    rhl_pre = pre;
    rhl_stmt1 = List.rev c1;
    rhl_stmt2 = List.rev c2;
    rhl_app = app } in
  let sg = [g1] in
  update_parent_goal g ~rule:(rule info) ~subgoal:sg;
  sg

let sp_simpl_fct ?(pos=None) g =
  let sp = match g.rhl_app with
    | Some _ -> not_implemented "EcWp.sp_simpl_fct_app"
    | None -> EcWp.sp_simpl_fct 
  in
  try gen_sp_fct ~pos sp Rsp_simpl g
  with EcWp.Sp_nothing_done ->
    cannot_apply "sp_simpl" "nothing to do"

let sp_simpl_tac ?(pos=None) = apply_tac_fct (sp_simpl_fct ~pos)



(** call-rule *)

let wp_call_fct id g =
  let e =
    match find_id_spec id with
      | Some e -> e
      | None -> cannot_apply "wp_call" "no '%i' id property" id in
  let equiv = equiv_of_spec e in
  try gen_wp_fct_info (EcWp.wp_call_equiv_fct equiv)
        (fun (l1,l2) -> Rwp_call (l1,l2,id)) g
  with
    | EcWp.Wp_no_calls -> cannot_apply "wp_call" "no calls"
    | EcWp.Wp_wrong_equiv ((f1', f2'), (f1, f2)) ->
      cannot_apply "wp_call"
        "the equivalence relation %s refers to %a and %a, while it should \
         refer to %a and %a"
        e.e_name
        PpAst.pp_fct_full_name f1' PpAst.pp_fct_full_name f2'
        PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2

let wp_call_tac id = apply_tac_fct (wp_call_fct id)


(** rnd-rule *)

let rec wp_rnd_fct info g =
  let env1, env2 = g.rhl_env1, g.rhl_env2 in
  match info, g.rhl_app with
    | AstLogic.RIdisj _, Some _
    | AstLogic.RIpara AstLogic.RIidempotant _, Some _ 
    | AstLogic.RIpara AstLogic.RIbij _, Some _ ->
      cannot_apply "wp_rnd_fct" "cannot be applied to approximate goals"
    | AstLogic.RIdisj side, _ ->
      begin try
              gen_wp_fct_info (EcWp.wp_rnd_disj_fct side)
                (fun v -> (Rrand (v, AstLogic.RIdisj side))) g
        with EcWp.Wp_no_random ->
          cannot_apply "wp_rnd_disj" "no random statements"
      end
    | AstLogic.RIpara info, _ ->
      let nt = 
        match g.rhl_stmt2 with
          | Sasgn (Ltuple[v], Ernd _) :: _ -> Some v.v_name, v.v_type 
          | Sasgn (_, Ernd r) :: _ -> None, EcTerm.type_of_random r
          | _ -> 
            cannot_apply
              "wp_rnd_fct" "the instruction should be a random assigment" in
      let info = EcTyping.mk_rnd_info env1 env2 nt info in
      try 
        gen_wp_fct_info (EcWp.wp_rnd_fct info) 
          (fun v -> (Rrand (v,AstLogic.RIpara info))) g
      with EcWp.Wp_no_random -> 
        cannot_apply "wp_rnd" "no random statements"
          
    

let wp_rnd_tac info = apply_tac_fct (wp_rnd_fct info)

let wp_rnd_disj_tac side = wp_rnd_tac (AstLogic.RIdisj side)




(** rnd-rule forward *)

let rec sp_rnd_fct info g = 
  let env1, env2 = g.rhl_env1, g.rhl_env2 in
  match info, g.rhl_app with
    | AstLogic.RIdisj _, Some _
    | AstLogic.RIpara AstLogic.RIidempotant _, Some _ 
    | AstLogic.RIpara AstLogic.RIbij _, Some _ ->
      cannot_apply "sp_rnd_fct" "cannot be applied to approximate goals"
    | AstLogic.RIdisj side, _ ->
      begin try
              gen_sp_fct_info (EcWp.sp_rnd_disj_fct side)
                (fun v -> (Rrand (v, AstLogic.RIdisj side))) g
        with EcWp.Sp_no_random ->
          cannot_apply "sp_rnd_disj" "no random statements"
      end
    | AstLogic.RIpara info, _ ->
      let nt = 
        match List.rev g.rhl_stmt2 with
          | Sasgn (Ltuple[v], _) :: _ -> Some v.v_name, v.v_type 
          | Sasgn (_, Ernd r) :: _ -> None, EcTerm.type_of_random r
          | _ -> 
            cannot_apply
              "sp_rnd_fct" "not a random assigment" in
      let info = EcTyping.mk_rnd_info env1 env2 nt info in
      try 
        gen_sp_fct_info (EcWp.sp_rnd_fct info) 
          (fun v -> (Rrand (v,AstLogic.RIpara info))) g
      with EcWp.Sp_no_random -> 
        cannot_apply "sp_rnd" "no random statements"

let sp_rnd_tac info = apply_tac_fct (sp_rnd_fct info)


(** false-rule -- c1 ~ c2 : False ==> Q *)

let pre_false_fct g =
  match g.rhl_pre with
  | Fol.Pfalse -> update_parent_goal g ~rule:Rpre_false ;[]
    | pre ->
      cannot_apply "pre_false"
        "the precondition is not 'false': %a" Fol.pp_pred pre

let pre_false_tac = apply_tac_fct pre_false_fct

(** true-rule -- c1 ~ c2 : P ==> True
    * c1 and c2 should be lossless *)

(* TODO how to deal with while *)

  
let is_lossless_goal g =
  EcTerm.is_lossless_stmt g.rhl_stmt1 &&
  EcTerm.is_lossless_stmt g.rhl_stmt2

let post_true_fct g =
  match g.rhl_post with
  | Fol.Ptrue when is_lossless_goal g ->
    begin
      match g.rhl_app with
        | None -> 
          update_parent_goal g ~rule:Rpost_true ;[]
        | Some (alpha,delta) ->
          try 
            ignore(l_implies g.rhl_pre 
                     (Fol.pand (Fol.ple_real Global.rone alpha) (Fol.ple_real Global.rzero delta)));
            update_parent_goal g ~rule:Rpost_true; []
          with CanNotProve p ->
            cannot_apply "while" "cannot prove@\n    %a\n"
              Fol.pp_pred p
    end
  | post ->
      cannot_apply "post_true"
        "the postcondition %a is not trivially true or the statements cannot be proven lossless" Fol.pp_pred post

let post_true_tac = apply_tac_fct post_true_fct

(** not-modify rule:
    *  P => M                  (1)
    * (M => Q') => (M => Q)    (2)

    *   P ==> Q'
    * -------------------------------- sub
    *   P /\ M ==> Q'
    * -------------------- not-modify
    *   P /\ M ==> M /\ Q'  |- P => M (1)    |- M /\ Q' => Q  (2)
    * ----------------------------------------------------------------- sub
    *                         P ==> Q
*)

let gen_not_modify_fct stop_first m l1 g =
  let l2, q' = l_simplify stop_first m g.rhl_post in
(*  let q' = Fol.remove_let q' in *)
  let sg = [ { (copy_goal g) with rhl_post = q' } ] in
  update_parent_goal g ~rule:(Rnot_modify m) ~subgoal:sg ~lsubgoal:[l1;l2];
  sg

let not_modify_fct stop_first m g =
  let mod1 = EcTerm.modified_stmt g.rhl_stmt1 in
  let mod2 = EcTerm.modified_stmt g.rhl_stmt2 in
  let dep1, dep2 = Fol.fv_pred m in
  let i1 = EcTerm.Vset.inter mod1 dep1 in
  if not (EcTerm.Vset.is_empty i1) then
    cannot_apply "not_modify"
      "predicate %a depend of %a in 1 which are modified"
      Fol.pp_pred m PpAst.pp_vset i1;
  let i2 = EcTerm.Vset.inter mod2 dep2 in
  if not (EcTerm.Vset.is_empty i2) then
    cannot_apply "not_modify"
      "predicate %a depend of %a in 2 which are modified"
      Fol.pp_pred m PpAst.pp_vset i2;
  let l1 = l_implies g.rhl_pre m in
  gen_not_modify_fct stop_first m l1 g


let not_modify_tac stop_first m = apply_tac_fct (not_modify_fct stop_first m)


(** simplify and prove *)

let simplify_tac stop_first g =
  let pre = g.rhl_pre in
  let mod1 = EcTerm.modified_stmt g.rhl_stmt1 in
  let mod2 = EcTerm.modified_stmt g.rhl_stmt2 in
  let m = Fol.remove_dep mod1 mod2 pre in
  let l1 = l_trivial (Fol.pimplies pre m) in
  gen_not_modify_fct stop_first m l1 g


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {3 Program transformations} *)

(** inlining *)
let inline_fct side cond g =
  let env, s =
    if side then g.rhl_env1, List.rev g.rhl_stmt1
    else g.rhl_env2, List.rev g.rhl_stmt2 in
  let i, env, s = EcInline.inline env cond s in
  let sg =
    [ if side then { (copy_goal g) with rhl_env1 = env; rhl_stmt1 = List.rev s }
      else { (copy_goal g) with rhl_env2 = env; rhl_stmt2 = List.rev s } ] in
  update_parent_goal g ~rule:(Rinline(side,i)) ~subgoal:sg ;
  sg

let inline_tac side cond = apply_tac_fct (inline_fct side cond)

(** Derandomization *)

let derandomize_fct side g =
  match g.rhl_app with 
    | Some _ ->
      cannot_apply "derandomize_fct" "cannot be applied to approximate goals"
    | None ->
        let env, rs = 
          if side then g.rhl_env1, g.rhl_stmt1 
          else g.rhl_env2, g.rhl_stmt2 in
        let env,r,s = 
          EcDerandom.derandomize_stmt env (List.rev rs) in
      let sg = 
        if side then 
          [ {(copy_goal g) with rhl_env1 = env; rhl_stmt1 = List.rev (r@s)} ]
        else
          [ {(copy_goal g) with rhl_env2 = env; rhl_stmt2 = List.rev (r@s)} ] in
      update_parent_goal g ~rule:(Rderandomize side) ~subgoal:sg;
      sg

let derandomize_tac side = apply_tac_fct (derandomize_fct side)

(** swap *)

let swap_fct (side, info) g =
  let f ns s =
    if side = ns then s
    else
      try EcSwap.pg_swap_fct info s
      with EcSwap.CanNotSwap msg -> cannot_apply "pg_swap" "%s" msg in
  let sg = [ { (copy_goal g) with
    rhl_stmt1 = f ApiTypes.Right g.rhl_stmt1;
    rhl_stmt2 = f ApiTypes.Left  g.rhl_stmt2 } ] in
  update_parent_goal g ~rule:(Rswap (side,info)) ~subgoal:sg ;
  sg

let swap_tac info = apply_tac_fct (swap_fct info)

(* unfold *)

let unfold_fct l gc =
  let pre = Fol.unfold_pred l gc.rhl_pre in
  let post = Fol.unfold_pred l gc.rhl_post in
  let gh = { (copy_goal gc) with rhl_pre = pre; rhl_post = post } in
  let l1 = { l_g = Fol.pimplies gc.rhl_pre pre; l_proof = LPtrivial } in
  let l2 = { l_g = Fol.pimplies post gc.rhl_post; l_proof = LPtrivial } in
  let sg = [gh] in
  update_parent_goal gc ~rule:Rsub ~subgoal:sg ~lsubgoal:[l1;l2];
  sg


let unfold_tac l = apply_tac_fct (unfold_fct l)






(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Printing} *)

let pp_cur_goal fmt no_more =
  match cur_goal_opt () with
    | None -> if no_more then Format.fprintf fmt "QED" else ()
    | Some g -> 
      Format.fprintf fmt "Current goal@\n%a%a" 
      print_pending_subgoals ()
      pp_goal g

let pp_cur_spec fmt () =
  pp_spec fmt (cur_spec ())








(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Eager } *)

let mk_eq_vars f1 f2 env1 env2 =
  let l1, l2 = f1.f_param, f2.f_param in
  let eq_glob = ref Fol.Ptrue in
  let eq_local = ref Fol.Ptrue in
  let eq_params = ref Fol.Ptrue in
  Global.iter_venv (fun s v1 ->
    let v2 = Global.find_var env2 s in
    if v1.Ast.v_glob <> v2.Ast.v_glob then
      bug "[tac_eager] two variables with same name and different v_glob";
    let eq = Fol.peq_vars v1 v2 in
    if v1.Ast.v_glob then
      eq_glob := Fol.pand !eq_glob eq
    else
      if List.mem v1 l1 then
        if List.mem v2 l2 then
          eq_params := Fol.pand !eq_params eq
        else
          user_error "parameter should be the same"
      else
        if List.mem v2 l2 then
          user_error "parameter should be the same"
        else
          eq_local := Fol.pand !eq_local eq) env1;
  !eq_glob, !eq_params, !eq_local

let mk_eager_goal eq_glob s1 s2 (f1, f2) =
  let pre = Fol.pand eq_glob (Fol.mkeq_params f1 f2) in
  let post = Fol.pand eq_glob (Fol.mkeq_result f1 f2) in
  let _, g = new_spec_def ~cur:false "eager" (f1,f2,pre,post,None) in
  match g.rhl_app with 
    | Some _ ->
      cannot_apply "mk_eager_goal" "cannot be applied to approximate goals"
    | None ->
      let g = {(copy_goal g) with
        rhl_stmt1 = List.rev ((List.rev g.rhl_stmt1)@s1);
        rhl_stmt2 = List.rev (s2 @ List.rev g.rhl_stmt2) } in
      { e_name = fresh_name_spec (eager_name f1 f2);
        e_id = fresh_spec_cntr ();
        e_f1 = f1;
        e_f2 = f2;
        e_kind = Eager(s1,s2);
        e_proof = Efct_eager (Eeag_equiv g) }

let pre_eager s1 s2 sIn sMod c1 c2 =
  let todo = ref [] in
  let in_todo f1 f2 = 
    List.exists (fun (f1',f2') -> EcTerm.eq_fct f1 f1' && EcTerm.eq_fct f2 f2') 
      !todo in
  let rec aux f1 f2 =
    try ignore (find_eager s1 s2 f1 f2);0
    with _ ->
      if in_todo f1 f2 then 0
      else
        match f1.f_body, f2.f_body with
        | FctAdv(a1,o1), FctAdv(a2,o2) when a1.adv_name = a2.adv_name ->
          begin
            try ignore (List.map2 aux o1 o2); 0
            with _ -> cannot_apply "eager_fct" ""
          end
        | FctDef fd1, FctDef fd2 ->
          begin
            try
              let todo' = ref [] in
              let aux1 f1 f2 =
                todo' := (f1,f2)::!todo'; 0 in
              ignore
                (EcEager.build_certif aux1 sIn sMod fd1.f_def fd2.f_def);
              while !todo' <> [] do
                let (f1,f2) = List.hd !todo' in
                todo' := List.tl !todo';
                ignore(aux f1 f2)
              done
            with _ ->
              todo := (f1,f2)::!todo
          end; 0
        |_, _ -> cannot_apply "pre_fct" "" in
  ignore (EcEager.build_certif aux sIn sMod c1 c2);
  !todo

let equiv_eager name equiv (s1,s2) =
  let spec,g = new_spec_def name equiv in
  match g.rhl_app with 
    | Some _ ->
      cannot_apply "equiv_eager" "cannot be applied to approximate goals"
    | None ->
      let f1,f2,env1,env2,pre,_ =
        spec.e_f1, spec.e_f2, g.rhl_env1, g.rhl_env2, g.rhl_pre, g.rhl_post in
      if (not (Global.eq_env env1 env2)) then
        user_error "Eager sampling: the two games should have the same variables";
      let fd1, fd2 = EcTerm.fct_def f1, EcTerm.fct_def f2 in
      let eq_glob, eq_params, eq_local = mk_eq_vars f1 f2 env1 env2 in
      let eq_all = Fol.pand eq_params (Fol.pand eq_local eq_glob) in
      let (hd1, c1, tl1), (hd2, c2, tl2) =
        try
          EcEager.find_sample_stmt fd1.Ast.f_def s1 s2 fd2.Ast.f_def
        with _ -> 
          user_error "eager: could not find the given re-sampling statement" in
      let sMod, sIn = EcEager.check_sample_stmt s1 s2 in
      let eq_code =
        EcEager.eq_stmt_name (fun _ _ -> cannot_apply "eager" "1") in
      if not (eq_code s1 s2) then cannot_apply "eager" "2";
      let todo = pre_eager s1 s2 sIn sMod c1 c2 in
      let gh = init_goal (Fol.pand eq_local pre) env1 hd1 env2 hd2 eq_all None in
      let gt = init_goal eq_all env1 tl1 env2 tl2 g.rhl_post None in
      let eb = {
        eb_stmt = s1,s2;
        eb_head = gh;
        eb_tail = gt;
        eb_cstmt = c1, c2;
        eb_trace = EcEager.ETempty
      } in
      spec.e_proof <-  Efct_def_by_eager eb;
      global_state.cur_spec <-
        (List.map (mk_eager_goal eq_glob s1 s2) todo) @
        (spec::global_state.cur_spec);
      gh,gt












(** Remove all the nodes in the tree greater than n*)
let rec forget_all_from_aux n g = match n with
  | n when ((g.rhl_created_id = n) ||  (g.rhl_updated_id > n)) -> ignore (reset_tac g)
  | n when (List.length g.rhl_subgoal > 0) ->
      g.rhl_subgoal <- (forget_subgoals n g.rhl_subgoal);
      if (((List.length g.rhl_subgoal) + (List.length g.rhl_lsubgoal)) = 0) then
        ignore(reset_tac g)
  | _ -> ()    
 
and forget_subgoals n = function 
  | [] -> []
  | x :: xs when (x.rhl_created_id > n)->  forget_subgoals n xs 
  | x :: xs ->  (forget_all_from_aux n x); (x :: forget_subgoals n xs)

(* Check if we need to remove the root of the proof *)
(* If not the case, call to 'cut' the tree if its 
 * necesary *)
let rec forget_all_specs_from n e = match e.e_proof with
  | Efct_def g when (g.rhl_created_id > n)-> 
    ignore(abort ())
  | Efct_def g ->
    forget_all_from_aux n g;
  | Efct_eager (Eeag_equiv g) when (g.rhl_created_id > n) -> 
    ignore(abort ()) 
  | Efct_eager (Eeag_equiv g) -> 
    forget_all_from_aux n g 
  | Efct_def_by_eager eb ->
    forget_all_from_aux n eb.eb_head;
    forget_all_from_aux n eb.eb_tail
  | _ -> ()


(** Remove all the nodes greater than n *)
let forget_all_from n =
  rhl_cntr :=  n;
  List.iter (forget_all_specs_from n) global_state.cur_spec

let rec unsave_aux xs = function
  | 0 -> xs
  | n -> 
    match xs with
      | [] -> []
      | e :: ys -> 
        match e.e_proof with
          | Efct_eager (Eeag_equiv _)->
            global_state.cur_spec <- e :: global_state.cur_spec;
            unsave_aux ys (n-1)
          | _ -> e :: (unsave_aux ys n)

let un_save = function
  | 0 -> global_state.cur_spec <- []
  | n when (n > List.length global_state.cur_spec )-> 
     let k = n - List.length global_state.cur_spec in
     global_state.proved_spec <- unsave_aux (global_state.proved_spec) k
  | _ -> ()

