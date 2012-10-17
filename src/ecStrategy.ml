(** TODO: first of all, try to use only EcDeriv tactics in this file,
    * and then, it should probably be moved into [UsrTac] module *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

open EcUtil

module T = EcDeriv

let lseq_tac lt = List.fold_right T.seq_tac lt T.id_tac
let lor_tac lt = List.fold_right T.or_tac lt (T.fail_tac "lor_tac")

let find_at cond l = 
  let rec aux n s = 
    match s with
    | [] -> raise Not_found
    | a::l -> if cond a then n else aux (n+1) l in
  aux 0 l

let is_while i = match i with Ast.Swhile _ -> true | _ -> false  
let is_if i = match i with Ast.Sif _ -> true | _ -> false

(* s is in reverse order *)
let find_first_while s = 
  try 1 + find_at is_while (List.rev s) 
  with Not_found -> cannot_apply "find_first_while" "no while statement"

(* s is in reverse order *)
let find_last_while s =
  try List.length s - find_at is_while s
  with Not_found -> cannot_apply "find_last_while" "no while statement"

let find_first_if s = 
  try 1 + find_at is_if (List.rev s) 
  with Not_found -> cannot_apply "find_first_if" "no if statement"

let find_last_if s =
  try List.length s - find_at is_if s
  with Not_found -> cannot_apply "find_last_if" "no if statement"

let find_first_while_or_if s = 
  try 1 + find_at (fun i -> is_if i || is_while i) (List.rev s) 
  with Not_found -> cannot_apply "find_first_while_or_if" "no if or while statement"

let find_last_while_or_if s =
  try List.length s - find_at (fun i -> is_if i || is_while i) s
  with Not_found -> cannot_apply "find_last_while_or_if" "no if of while statement"


(* by_tac: apply a tactic, if it doesn't solve current goal, fail             *)
let by_tac t = 
  T.seq_tac t (T.fail_tac "by: doesn't kill all goals")

(* short cup for random *)
let rnd_tac   = T.wp_rnd_tac (AstLogic.RIpara AstLogic.RIid)
let rnd_l_tac = T.wp_rnd_tac (AstLogic.RIdisj ApiTypes.Left) 
let rnd_r_tac = T.wp_rnd_tac (AstLogic.RIdisj ApiTypes.Right)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let open_equiv name equiv =
  (*  debug 1 "apply [open_equiv]@."; *)
  ignore (T.new_spec_def ~cur:true name equiv)



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Trivial  *)

let prove_tac b = 
  T.seq_tac (T.simplify_tac b) (T.try_tac T.post_true_tac)

let nil_tac b g =
  let _,_,s1,_,s2,_,_ = T.equiv_of_goal g in
  match s1, s2 with
    | [],[] -> prove_tac b g
    | _,_ -> T.id_tac g

let trivial_tac b =
  T.seq_tac
    (T.repeat_tac 
       (lor_tac [T.wp_simpl_tac; rnd_tac; rnd_l_tac; rnd_r_tac]))
    (nil_tac b)

let intern_trivial_tac = trivial_tac true
let by_nil_tac = by_tac (nil_tac true)

(* For the user *)
let trivial_tac = trivial_tac false
let prove_tac = prove_tac false 

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Inlining *)

let stmt_goal_bool side g =
  let _,_,s1,_,s2,_,_ = T.equiv_of_goal g in
  if side then s1 else s2

let side_tac side t =
  match side with
    | ApiTypes.Both -> T.seq_tac (t true) (t false)
    | ApiTypes.Left -> t true
    | ApiTypes.Right -> t false

let reduce_cond_tac (side, pos, b) =
  let t sd g = 
    let l = 
      match pos with
      | AstLogic.At_empty -> 
          [find_first_while_or_if (stmt_goal_bool sd g)]
      | AstLogic.At_pos l -> 
          List.sort (fun x y -> y - x) l 
      | AstLogic.At_last -> 
          [find_last_while_or_if (stmt_goal_bool sd g)] in
    let f (g,sg) p = 
      match T.reduce_cond_tac sd p b g with
      | [g1;g2] -> 
          let sg' = nil_tac true g1 in
          (g2, sg'@ sg)
      | [g2] -> (g2,sg) 
      | _ -> assert false in
    List.fold_left f (g,[]) l in
  fun g ->
    try 
      match side with
      | ApiTypes.Left -> let g,sd = t true g in List.rev_append sd [g]
      | ApiTypes.Right -> let g, sd = t false g in List.rev_append sd [g]
      | ApiTypes.Both -> 
          let (g,sd) = t true g in
          let (g,sd') = t false g in
          List.rev_append sd (List.rev_append sd' [g])
    with e -> 
      ignore (T.reset_tac g);
      raise e


let ifneg_tac (side, pos) g =
  let t sd g =
    let l = 
      match pos with
      | AstLogic.At_empty -> [find_first_if (stmt_goal_bool sd g)]
      | AstLogic.At_pos l -> 
          List.sort (fun x y -> y - x) l 
      | AstLogic.At_last -> [find_last_if (stmt_goal_bool sd g)] in
    List.fold_left (fun sg p -> 
      match sg with
      | [g] -> T.ifneg_tac sd p g
      | _ -> assert false) [g] l in
  try side_tac side t g
  with e -> ignore (T.reset_tac g); raise e


let unroll_tac (side, pos) g = 
  let t sd g = 
    let l = 
      match pos with
      | AstLogic.At_empty -> 
          [find_first_while (stmt_goal_bool sd g)]
      | AstLogic.At_pos l -> 
          List.sort (fun x y -> y - x) l 
      | AstLogic.At_last -> 
          [find_last_while (stmt_goal_bool sd g)] in
    List.fold_left (fun sg p -> 
      match sg with
      | [g] -> T.unroll_tac sd p g
      | _ -> assert false) [g] l in
  try side_tac side t g
  with e -> ignore (T.reset_tac g); raise e

let inline_tac (side,info) = 
  let f info side =
    match info with
    | AstLogic.IKat AstLogic.At_last ->
        fun g ->
          let s = stmt_goal_bool side g in
          begin match s with
          | Ast.Scall(_,f,_)::_ ->
              if EcTerm.is_defined_fct f then
                let s = List.rev s in
                let pos = EcInline.last_pos s in
                T.inline_tac side (fun k _ _ _ -> k = pos) g
              else
                cannot_apply "[ecStrategy.inline]"
                  "the last instruction is a call to %a which is not a defined function"
                  PpAst.pp_fct_full_name f
            | _ ->
                cannot_apply "[ecStrategy.inline]"
                  "the last instruction of statement %i is not a call"
                  (if side then 1 else 2)
          end

    | AstLogic.IKat AstLogic.At_pos lpos ->
        let lpos = ref lpos in
        let cond k _ f _ = 
          let test = EcTerm.is_defined_fct f && List.mem k !lpos in
          if test then lpos := List.filter ((<>) k) !lpos;
          test in
        fun g ->
          let gs = T.inline_tac side cond g in
          if !lpos <> [] then begin
            ignore (T.reset_tac g);
            cannot_apply "inline_tac" "found no call at position%s %a"
              (if (List.length !lpos) > 1 then "s" else "")
              (pp_list ~sep:", " Format.pp_print_int) !lpos
          end;
          gs

    | AstLogic.IKat AstLogic.At_empty ->
        let f g =
          let s = stmt_goal_bool side g in
          if EcInline.as_defined_call s then
            let cond _ _ f _ = EcTerm.is_defined_fct f in
            T.inline_tac side cond g
          else cannot_apply "inline_tac" "nothing to inline" in
        T.repeat_tac f
    
    | AstLogic.IKfct lf ->
        let f g =
          let s = stmt_goal_bool side g in
          if EcInline.as_defined_call_in lf s then
            let cond _ _ f _ =
              EcTerm.is_defined_fct f && List.mem f.Ast.f_name lf in
            T.inline_tac side cond g
          else cannot_apply "inline_tac" "nothing to inline" in
        T.repeat_tac f
  in
  side_tac side (f info)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Try to sort the assignment by sorting the name of the variables           *)

let sort_assign side g =
  let sid = if side then ApiTypes.Left else ApiTypes.Right in
  let s = ref (List.rev (stmt_goal_bool side g)) in
  let get_var () =
    match !s with
    | (Ast.Sasgn(Ast.Ltuple [x],_))::s' -> s := s'; x
    | _ ->
        cannot_apply
          "[EcStrategy.sort_assign]"
          "the statement should contain only assignment to a single variable" in
  let insert_at x r =
    let rec aux s r =
      match r with
        | y::r' ->
          if y.Ast.v_name <= x.Ast.v_name then
            (List.length s, List.rev_append s (x::r))
          else aux (y::s) r'
        | [] -> (List.length s, List.rev_append s [x]) in
    aux [] r in
  let rec aux r k g =
    if !s = [] then [g]
    else
      let x = get_var () in
      let delta, r = insert_at x r in
      if delta = 0 then aux r (k+1) g
      else
        T.seq_tac
          (EcDeriv.swap_tac (sid, AstLogic.SKswap(k,1,-delta)))
          (aux r (k+1)) g in
  aux [] 0 g


let sort_tac side = side_tac side sort_assign

let sort_random_tac g = 
  let _,_,_,_,_,post,_ = T.equiv_of_goal g in
  let post = Fol.remove_let post in
  let find_pos s v = 
    let rec aux n s = 
      match s with
      | (Ast.Sasgn(Ast.Ltuple [x],_))::s' ->
          if EcTerm.eq_var x v then Some(List.length s', n)
          else aux (n+1) s' 
      | _ -> None in
    aux 0 s in
  let acc = ref (try Fol.find_same post with _ -> []) in
  let rec push_end g = 
    if !acc = [] then T.id_tac g else
    let v1,v2 = List.hd !acc in
    acc := List.tl !acc;
    let _,_,s1,_,s2,_,_ = T.equiv_of_goal g in
    let swap_tac side k d  = 
      if d = 0 then T.id_tac 
      else EcDeriv.swap_tac (side, AstLogic.SKswap(k,1,d)) in
    match find_pos s1 v1, find_pos s2 v2 with
    | Some (k1,d1), Some(k2,d2) ->
        lseq_tac 
          [swap_tac ApiTypes.Left k1 d1;
           swap_tac ApiTypes.Right k2 d2;
           rnd_tac; push_end] g
    | None, None -> push_end g
    | _, _ -> cannot_apply "sort_random_tac" "" in
  lseq_tac [push_end;
            T.repeat_tac rnd_l_tac;
            T.repeat_tac rnd_r_tac;
            by_nil_tac] g

    
  
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Try to apply automatically the random rules                                *)
(* This function should be called after sort_tac                              *)

let auto_rnd_tac g =
  let _,_,s1,_,s2,_,_ = T.equiv_of_goal g in
  match s1, s2 with
  | Ast.Sasgn(Ast.Ltuple[x1], Ast.Ernd r1)::_,
    Ast.Sasgn(Ast.Ltuple[x2], Ast.Ernd r2)::_ ->
      if x1.Ast.v_name = x2.Ast.v_name then
        if EcTerm.eq_random r1 r2 && EcTerm.is_cnst_rnd r1 then rnd_tac g
        else cannot_apply "auto_rnd_tac" ""
      else
        if x1.Ast.v_name < x2.Ast.v_name then rnd_r_tac g
        else rnd_l_tac g
  | Ast.Sasgn(Ast.Ltuple[_x1], Ast.Ernd _r1)::_, _ -> rnd_l_tac g
  | _, Ast.Sasgn(Ast.Ltuple[_x2], Ast.Ernd _r2)::_ -> rnd_r_tac g
  | _, _ -> cannot_apply "auto_rnd_tac" ""


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let app_tac k q app g =
  let _,env1, _, env2,_,_,_ = T.equiv_of_goal g in
  let q = EcTyping.mk_pred env1 env2 q in
  T.app_tac k q app g

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** EqObs_in *)

let intern_eqobs_in_tac on_call inv eqs g =
  let (_,_,c1,_,c2,_,_) = T.equiv_of_goal g in
  let info_call = ref [] in
  let on_call f1 f2 = 
    let (res,info) = on_call f1 f2 in
    info_call := T.spec_id res :: !info_call;
    info in
  let _ = T.eqobs_in on_call inv c1 c2 eqs in
  T.eqobs_in_tac !info_call (eqs,inv) g


let split_inv p =
  let rec aux p eqs inv =
    match p with
    | Fol.Pand(p1,p2) -> 
        let (eqs,inv) = aux p2 eqs inv in
        aux p1 eqs inv
    | Fol.Papp(op,[Ast.Ebase v1;Ast.Ebase v2]) when Fol.is_eq_pred op ->
        let xx = 
          match v1.Fol.lv_base, v2.Fol.lv_base with
          | Fol.FVpgVar(x1,Fol.FVleft), Fol.FVpgVar(x2,Fol.FVright) ->
              (x1,x2) 
          | Fol.FVpgVar(x2,Fol.FVright), Fol.FVpgVar(x1,Fol.FVleft) ->
              (x1,x2) 
          | _ -> user_error "eqobs_in does not apply" in
        EcTerm.Vset2.add xx eqs, inv
    | _ -> eqs, Fol.pand p inv in
  aux p EcTerm.Vset2.empty Fol.Ptrue

let get_ret_exp f = 
  match (EcTerm.fct_def f).Ast.f_return with
  | None -> raise Not_found
  | Some e -> e

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** wp_fct *)

let gen_call_tac on_both_call g = 
  let _, _, s1, _, s2, _,_ = T.equiv_of_goal g in
  match s1, s2 with
    | Ast.Scall(_, f1, _)::_, Ast.Scall(_, f2, _)::_ ->
      on_both_call f1 f2 g
    | Ast.Scall (_, f1, _)::_, _ when EcTerm.is_defined_fct f1 ->
      inline_tac (ApiTypes.Left, AstLogic.IKat AstLogic.At_last) g
    | _, Ast.Scall (_, f2, _)::_ when EcTerm.is_defined_fct f2 ->
      inline_tac (ApiTypes.Right, AstLogic.IKat AstLogic.At_last) g
    | _, _ -> cannot_apply "call_tac" "no call or only one call to an adversary"

let rec gen_progress_tac on_both_call g =
  T.seq_tac
    (T.try_tac T.wp_simpl_tac)
    (T.or_tac
       (T.seq_tac
          (gen_call_tac on_both_call)
          (gen_progress_tac on_both_call))
       (nil_tac true)) g

let derandomize_tac side = side_tac side T.derandomize_tac

let gen_wp_fct_body on_both_call =
  let else_tac g = 
    verbose 
      "finding the random permutation using names fail try to use the postcondition";
    sort_random_tac g in
  let first_tac = 
    by_tac (T.seq_tac
      (T.try_tac 
         (T.seq_tac (sort_tac ApiTypes.Both) (T.repeat_tac auto_rnd_tac)))
      (nil_tac true)) in
  lseq_tac
    [ inline_tac (ApiTypes.Both, AstLogic.IKat AstLogic.At_empty);
      T.try_tac (derandomize_tac ApiTypes.Both);
      gen_progress_tac on_both_call;
      T.try_tac (T.or_tac first_tac else_tac)  ]


let inferred_cntr = ref (-1)

let inferred_name f1 f2 =
  incr inferred_cntr;
  Format.sprintf "inferred_%s_%s_%s_%s_%i"
    f1.Ast.f_game.Ast.g_name f1.Ast.f_name
    f2.Ast.f_game.Ast.g_name f2.Ast.f_name
    !inferred_cntr

let make_spec_name name f1 f2 =
  match name with
    | None -> inferred_name f1 f2
    | Some name -> name

let find_spec_implies ?(name=None) f1 f2 pre post app =
  let all = T.find_all_spec f1 f2 in
  let check_eq s =
    let (_,_,spre,spost,_) = T.equiv_of_spec s in
    Fol.eq_pred pre spre && Fol.eq_pred post spost in
  let spec_sub s =
    verbose "try to use %s for %a %a" (T.spec_name s) 
      PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2;
    let s = 
      T.new_spec_sub (fun _ -> make_spec_name name f1 f2) s pre post app in
    T.add_spec s in
  try
    let spec = List.find check_eq all in
    if name = None then spec else spec_sub spec
  with Not_found ->
    let rec aux all =
      match all with
        | [] -> raise Not_found
        | s::all -> 
            try spec_sub s 
            with _ ->
              verbose "fail to use %s try another strategy" (T.spec_name s);
              aux all in
    aux all

let check_mod ginv g =
  let check_l fv l =
    match l with
    | Ast.Ltuple l  -> List.exists (fun u -> EcTerm.Vset.mem u fv) l
    | Ast.Lupd(u,_) -> EcTerm.Vset.mem u fv in
  let rec check_i fv i = 
    match i with
    | Ast.Sasgn(l,_) | Ast.Scall(l,_,_) -> 
        if check_l fv l then cannot_apply "check_mod" " "
    | Ast.Sif(_,s1,s2) -> check_s fv s1; check_s fv s2
    | Ast.Swhile(_, s) -> check_s fv s
    | Ast.Sassert _ -> ()
  and check_s fv s = List.iter (check_i fv) s in
  let _,_,s1,_,s2,_,_ = T.equiv_of_goal g in
  let fv1, fv2 = Fol.fv_pred ginv in
  check_s fv1 s1;
  check_s fv2 s2


let rec equiv_fct ?(find=true) ?(name=None) inv f1 f2 pre post =
(*  verbose "start equiv_fct %a ~ %a : %a ==> %a"
    PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2
    Fol.pp_pred pre Fol.pp_pred post;  *)
  try 
    if not find then raise Not_found;
    let res = find_spec_implies ~name f1 f2 pre post None in
(*    verbose "find_spec_implies success"; *)
    res
  with Not_found ->
    match f1.Ast.f_body, f2.Ast.f_body with
    | Ast.FctDef _fd1, Ast.FctDef _fd2 ->
        equiv_fct_def ~name inv f1 f2 pre post
    | Ast.FctAdv (a1, _o1), Ast.FctAdv (a2, _o2) ->
      if a1.Ast.adv_name = a2.Ast.adv_name then
        equiv_fct_adv ~name inv f1 f2 pre post
      else cannot_apply "equiv_fct" "the procedures %a and %a do not correspond to the same adversary"
          PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2
    | Ast.FctAdv _ , _ ->
        cannot_apply "equiv_fct" "the procedures %a is abtract and but not %a"
          PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2
    | _, Ast.FctAdv _ ->
        cannot_apply "equiv_fct" "the procedures %a is abtract and but not %a"
          PpAst.pp_fct_full_name f2 PpAst.pp_fct_full_name f1


and equiv_inv_fct ?(name=None) (inv,l) f1 f2 =
(*  verbose "start equiv_inv_fct %a %a"
    PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2; *)
  let all = T.find_all_spec f1 f2 in
  try List.find (fun s -> List.mem (T.spec_name s) l) all
  with Not_found ->
    let pre, post = FunLogic.build_inv_spec inv f1 f2 in
    equiv_fct ~name (inv,l) f1 f2 pre post

and equiv_fct_def ?(name=None) inv f1 f2 pre post =
(*   verbose "start equiv_fct_def %a %a" PpAst.pp_fct_full_name f1
      PpAst.pp_fct_full_name f2; *)
  let name = make_spec_name name f1 f2 in
  let spec,g = T.new_spec_def ~cur:false name (f1,f2,pre,post,None) in
  let on_both_call f1 f2 g =
    let spec = equiv_inv_fct inv f1 f2 in
    verbose "use spec named %s for %a and %a@."
      (T.spec_name spec) PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2;
    T.wp_call_tac (T.spec_id spec) g in
  let default_tac g = gen_wp_fct_body on_both_call g in
  let tactic =
    let try_eqobs = ref false in
    match inv with
    | AstLogic.Inv_upto _,_ -> default_tac 
    | AstLogic.Inv_global p,_ -> fun g ->
        try
          let glob, ginv = split_inv p in
          let eqs, _ = split_inv post in
          let check eqs = 
            if EcTerm.Vset2.exists 
                (fun (v,_)->EcTerm.eq_var f1.Ast.f_res v) eqs then
              raise Not_found;
            if EcTerm.Vset2.exists 
                (fun (_,v)->EcTerm.eq_var f1.Ast.f_res v) eqs then
              raise Not_found in
          let eqs = 
            if EcTerm.Vset2.mem (f1.Ast.f_res, f2.Ast.f_res) eqs then
              let eqs = EcTerm.Vset2.remove (f1.Ast.f_res, f2.Ast.f_res) eqs in
              check eqs;
              let e1, e2 = get_ret_exp f1, get_ret_exp f2 in
              T.add_eqs e1 e2 eqs
            else (check eqs;eqs) in
          check_mod ginv g;
          try_eqobs := true;
          by_tac 
            (T.seq_tac 
               (intern_eqobs_in_tac (eqobs_in_inv glob inv) ginv eqs)
               (gen_wp_fct_body on_both_call)) g 
        with _ -> 
          if !try_eqobs then
            verbose "eqobs_in fail for %s try to use the default strategy"
              name;
          ignore (T.reset_tac g); default_tac g in
  let sg = tactic g in
  match sg with
  | [] -> T.add_spec spec
  | _ ->
      cannot_apply "equiv_fct_def"
        "can not prove specification:@\n   %a@\nstill goal:@\ %a"
        T.pp_spec spec (fun fmt -> List.iter (T.pp_goal fmt)) sg

and eqobs_in_inv glob inv f1 f2 = 
  equiv_inv_fct inv f1 f2, (glob,glob)
   
and equiv_fct_adv ?(name=None) inv f1 f2 pre post =
  let o1,o2 =
    match f1.Ast.f_body, f2.Ast.f_body with
    | Ast.FctAdv (a1, o1), Ast.FctAdv (a2, o2)
        when a1.Ast.adv_name = a2.Ast.adv_name -> o1,o2
    | _, _ -> cannot_apply
          "equiv_fct_adv" "the two functions should be the same adversary" in
  let equiv_o f1 f2 =
    let pre,post = FunLogic.build_inv_oracle_spec (fst inv) f1 f2 in
    equiv_fct inv f1 f2 pre post in
  let o_spec = List.map2 equiv_o o1 o2 in
  let pre', post' = FunLogic.build_inv_spec (fst inv) f1 f2 in
  let spec =
    if Fol.eq_pred pre pre' && Fol.eq_pred post post' then
      T.new_spec_adv (make_spec_name name f1 f2) (fst inv) f1 f2 o_spec
    else
      let spec1 =
        T.new_spec_adv (make_spec_name None f1 f2) (fst inv) f1 f2 o_spec in
      let spec1 = T.add_spec spec1 in
      T.new_spec_sub (fun _ -> make_spec_name name f1 f2) spec1 pre post None in
  let spec = T.add_spec spec in
  spec

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Call *)

(* Add more info like give the pre post or the global invariant *)
let wp_call_tac info g = 
  match info with
  | (None, [name]) ->
      begin match T.find_named_spec name with
      | Some e -> T.wp_call_tac (T.spec_id e) g
      | None -> cannot_apply "EcStrategy.wp_call" "no '%s' property" name
      end
  | _ -> 
      let _, _, s1, _, s2, _, _ = T.equiv_of_goal g in
      match s1, s2 with
      | Ast.Scall(_, f1, _)::_, Ast.Scall(_, f2, _)::_ ->
          let inv = EcTyping.mk_info f1 f2 info in
          let spec = equiv_inv_fct inv f1 f2 in
          T.wp_call_tac (T.spec_id spec) g
      | _, _ -> cannot_apply "wp_call_tac" "found no pair of functions" 

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** While *)
let while_tac (side, way, p, e) = 
  match way with
  | AstLogic.Forwards -> T.while_tac (side,p,e)
  | AstLogic.Backwards -> T.whilerev_tac (side,p,e)

let splitwhile_tac (side, pos, e) = 
  let t b = 
    match pos with
    | AstLogic.At_last ->
        fun g -> 
          let s = stmt_goal_bool b g in
          T.splitwhile_tac b (find_last_while s) e g 
    | AstLogic.At_pos l -> 
        fun g ->
          let l = List.sort (fun x y -> y - x) l in
          begin 
            try 
              List.fold_left (fun sg n ->
                match sg with
                | [g] -> T.splitwhile_tac b n e g
                | _ -> assert false) [g] l
            with e -> ignore(T.reset_tac g); raise e
          end
    | AstLogic.At_empty ->
        fun g ->
          let s = stmt_goal_bool b g in
          T.splitwhile_tac b (find_first_while s) e g in
  side_tac side t 


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Rnd *)

let rnd_tac (way,info) = match way with
  | AstLogic.Backwards -> T.wp_rnd_tac info
  | AstLogic.Forwards ->  T.sp_rnd_tac info

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Set *)

let set_tac (side,pos,name,t,e) =
  let t b g = 
    let k =  
      match pos with
      | AstLogic.At_last -> List.length (stmt_goal_bool b g)
      | AstLogic.At_pos [k] -> k 
      | AstLogic.At_pos _ -> 
          not_implemented "EcStrategy.set_tac many position"
      | AstLogic.At_empty -> 1 in
    T.set_tac b k name t e g in
  side_tac side t
          
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Auto *)
let auto_tac inv =
  let on_both_call f1 f2 g =
    let inv = EcTyping.mk_info f1 f2 inv in
    let spec = equiv_inv_fct inv f1 f2 in
    T.wp_call_tac (T.spec_id spec) g in
  gen_progress_tac on_both_call

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Proba} *)

let proba check name (rcmp, hint) =
  let find name =
    match T.find_named_spec name with
      | Some p -> T.equiv_of_spec p
      | None -> cannot_apply "proba" "property %s does not exist" name in
  EcProba.check_and_add check find name rcmp hint

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Eager Sampling *)

let eager name equiv s12 =
  let _gh,_gt = T.equiv_eager name equiv s12 in
  ()


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** If guard synchronization                                                  *) 
(* Given two arbitrary programs, take the first ifs and decide whther the     *)
(* guards can be synchronised. if so, apply if-sync rule, otherwise, fail.    *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let rec find_first_if s = match s with
  | [] -> 0
  | (Ast.Sif _)::_ -> 0
  | _::ss -> 1 + find_first_if ss
    
let ifsync_noarg_tac g =  
  let k1 = find_first_if (List.rev (stmt_goal_bool true g)) in
  let k2 = find_first_if (List.rev (stmt_goal_bool false g)) in
  T.ifsync_tac (k1+1) (k2+1) g

let ifsync_tac info = 
  match info with
  | None -> ifsync_noarg_tac
  | Some(k1,k2) -> T.ifsync_tac k1 k2

let ifneg_noargs_tac sd g =  
  let stmt = stmt_goal_bool sd g in
  let k = find_first_if (List.rev stmt) in
  T.ifneg_tac sd (k+1) g

let autosync_tac = 
  let aux =
    let kill_equiv = 
      by_tac (lseq_tac
		[T.aprhl_tac; T.wp_simpl_tac; T.prhl_tac; intern_trivial_tac] )
    in T.seq_subgoal_tac (ifsync_tac None) [T.id_tac; T.id_tac; kill_equiv ]
  in
  T.or_tac aux (T.seq_tac (ifneg_noargs_tac true) aux)


let rec get_eqs p eqs =
  match p with
    | Fol.Ptrue -> EcTerm.Vset2.empty
    | Fol.Papp(op,[Ast.Ebase v1;Ast.Ebase v2]) when Fol.is_eq_pred op ->
      let xx = 
        match v1.Fol.lv_base, v2.Fol.lv_base with
          | Fol.FVpgVar(x1,Fol.FVleft), Fol.FVpgVar(x2,Fol.FVright) ->
            (x1,x2) 
          | Fol.FVpgVar(x2,Fol.FVright), Fol.FVpgVar(x1,Fol.FVleft) ->
            (x1,x2) 
          | _ -> user_error "expecting left/right equalities in %a" Fol.pp_pred p in
      EcTerm.Vset2.add xx eqs 
    | Fol.Pand (p1, p2) -> get_eqs p1 (get_eqs p2 eqs)
    | _ -> user_error "expecting left/right equalities in %a" Fol.pp_pred p

let eqobs_in_tac glob inv concl l g =
  let (_,venv1,_,venv2,_,_,_) = T.equiv_of_goal g in
  let glob = EcTyping.mk_pred venv1 venv2 glob in
  let inv = EcTyping.mk_pred venv1 venv2 inv in
  let concl = EcTyping.mk_pred venv1 venv2 concl in
  let geqs = get_eqs glob EcTerm.Vset2.empty in
  let eqs = get_eqs concl EcTerm.Vset2.empty in
  let on_call f1 f2 = 
    let info = (AstLogic.Inv_global (Fol.pand glob inv), l) in 
    eqobs_in_inv geqs info f1 f2 in
  intern_eqobs_in_tac on_call inv eqs g  


