open EcUtil
open Ast
open EcTerm

type eager_trace =
  | ETempty
  | ETcall of int * eager_trace
  | ETif of eager_trace * eager_trace * eager_trace
  | ETwhile of eager_trace * eager_trace

let eq_var_name v1 v2 = v1.v_name = v2.v_name
let eq_exp_name = EcTerm.g_eq_exp eq_var_name eq_var_name

let eq_lasgn_name l1 l2 =
  match l1, l2 with
    | Ltuple l1, Ltuple l2 ->
      (try List.for_all2 eq_var_name l1 l2 with _ -> false)
    | Lupd(x1,e1), Lupd(x2,e2) ->
      eq_var_name x1 x2 && eq_exp_name e1 e2
    | _, _ -> false


let check_certif check sIn sMod c1 c2 t =
  let rec aux c1 c2 t =
    match c1,c2,t with
      | [], [], _ -> true
      | Sasgn(l1,e1) as i ::c1, Sasgn(l2,e2) :: c2, _ ->
          eq_lasgn_name l1 l2 &&
          eq_exp_name e1 e2 &&
          EcTerm.Vset.disjoint (read_stmt [i]) sMod &&
          EcTerm.Vset.disjoint (modified_stmt [i]) sIn &&
          aux c1 c2 t
      | Sif(e,c1,c2)::c,Sif(e',c1',c2')::c', ETif(t1,t2,t) ->
          eq_exp_name e e' &&
          EcTerm.Vset.disjoint (fv_exp e) sMod &&
          aux c1 c1' t1 && aux c2 c2' t2 && aux c c' t
      | Scall(l,f,args)::c, Scall(l',f',args')::c', ETcall(i,t) ->
          check f f' i &&
          eq_lasgn_name l l' &&
          (try List.for_all2 eq_exp_name args args' with _ -> false) &&
          EcTerm.Vset.disjoint (fv_args args) sMod &&
          EcTerm.Vset.disjoint (read_lasgn l) sMod &&
          EcTerm.Vset.disjoint (modified_lasgn l) sIn &&
          aux c c' t
      | _, _, _ -> false
  in aux c1 c2 t

exception CanNotSwap

let build_certif check sIn sMod c1 c2 =
  let rec aux c1 c2 =
    match c1,c2 with
      | [], [] -> ETempty
      | Sasgn(l1,e1) as i :: c1, Sasgn(l2,e2) :: c2 ->
        if eq_lasgn_name l1 l2 &&
           eq_exp_name e1 e2 &&
           EcTerm.Vset.disjoint (read_stmt [i]) sMod &&
           EcTerm.Vset.disjoint (modified_stmt [i]) sIn
        then aux c1 c2
        else raise CanNotSwap
      | Sif(e,c1,c2)::c,Sif(e',c1',c2')::c' ->
        if eq_exp_name e e' &&
          EcTerm.Vset.disjoint (fv_exp e) sMod
        then ETif(aux c1 c1', aux c2 c2', aux c c')
        else raise CanNotSwap
      | Swhile(e,c1)::c,Swhile(e',c1')::c' ->
        if eq_exp_name e e' &&
          EcTerm.Vset.disjoint (fv_exp e) sMod
        then ETwhile(aux c1 c1', aux c c')
        else raise CanNotSwap   
      | Scall(l,f,args)::c, Scall(l',f',args')::c' ->
        let i = check f f' in
        if eq_lasgn_name l l' &&
          (try List.for_all2 eq_exp_name args args' with _ -> false) &&
          EcTerm.Vset.disjoint (fv_args args) sMod &&
          EcTerm.Vset.disjoint (read_lasgn l) sMod &&
          EcTerm.Vset.disjoint (modified_lasgn l) sIn
        then ETcall(i, aux c c')
        else raise CanNotSwap
      | _, _ -> raise CanNotSwap
  in aux c1 c2

(** {2 Equality of two stmt modulo name of variables (not uid)} *)

let rec eq_instr_name on_fct i1 i2 =
  match i1, i2 with
    | Sasgn(l1,e1), Sasgn(l2,e2) ->
      eq_lasgn_name l1 l2 && eq_exp_name e1 e2
    | Sif(e1,c11,c12),Sif(e2,c21,c22) ->
        eq_exp_name e1 e2 &&
        eq_stmt_name on_fct c11 c21 &&
        eq_stmt_name on_fct c12 c22
    | Scall(l1,f1,args1), Scall(l2,f2,args2) ->
      eq_lasgn_name l1 l2 &&
        (try List.for_all2 eq_exp_name args1 args2 with _ -> false) &&
        on_fct f1 f2
    | Swhile(e1,c1), Swhile(e2,c2) ->
        eq_exp_name e1 e2 &&
        eq_stmt_name on_fct c1 c2
    | _, _ -> false

and eq_stmt_name on_fct c1 c2 =
  try List.for_all2 (eq_instr_name on_fct) c1 c2 with _ -> false




let check_sample_stmt s1 s2 =
  let sMod1 = modified_stmt s1 in
  let sIn1 = modified_stmt s1 in
  let sMod2 = modified_stmt s2 in
  let sIn2 = modified_stmt s2 in
  let check_global x =
    if not (Vset.for_all (fun v -> v.v_glob) x) then
      user_error
        "The sample statement should depend only on global variables" in
  check_global sMod1; check_global sIn1;
  check_global sMod2; check_global sIn2;
  sMod1, sIn1

(* [get_postfix s c] return tl if c = s @ tl,
   raise Not_found otherwise *)
let rec get_postfix eq_i s c =
  match s, c with
    | [], _ -> c
    | i1::s, i2::c when eq_i i1 i2 -> get_postfix eq_i s c
    | _ -> raise Not_found

(* [get_pre_postfix s c] return hd, tl if c = hd @ s @ tl,
   raise Not_found otherwise *)
let get_pre_postfix eq_i s c =
  let rec aux rhd c =
    try
      let tl = get_postfix eq_i s c in List.rev rhd, tl
    with Not_found ->
      match c with
        | i::c -> aux (i::rhd) c
        | _ -> raise Not_found in
  aux [] c

let get_hd_tl eq_i c1 c2 =
  let rec aux r1 c1 =
    try
      let tl2 = get_postfix eq_i c1 c2 in List.rev r1, c1, tl2
    with Not_found ->
      match c1 with
        | i::c1 -> aux (i::r1) c1
        | _ -> raise Not_found in
  aux [] c1

let find_sample_stmt c1 s1 s2 c2 =
  (* We try to see c1 as hd1;c1';s1;tl1
   * and           c2 as hd2;s2;c2';tl2
   * with c1' = c2' *)
  let eq_instr = eq_instr_name (fun f1 f2 -> f1.f_name = f2.f_name) in
  let hd1c,tl1 = get_pre_postfix eq_instr s1 c1 in
  let hd2,ctl2 = get_pre_postfix eq_instr s2 c2 in
  let hd1,c1',tl2 = get_hd_tl eq_instr hd1c ctl2 in
  let c2' = list_hdn (List.length c1') ctl2 in
  (hd1,c1',tl1),(hd2,c2',tl2)

