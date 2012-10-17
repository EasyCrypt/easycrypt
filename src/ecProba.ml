open Ast
open EcUtil
open Global

module Vset = EcTerm.Vset

(* (string * (Ast.real_exp * Ast.cmp_real * Ast.real_exp)) list *)

let pr_list :  (bool ref * (string * real_exp)) list ref  = ref [] 
let pr_list_export = ref []

let _ = 
  let h = ref [] in

  let save n = 
    h := (n, List.map (fun (a,(b,c)) -> (!a,(b,c))) !pr_list) 
         :: !h in

  let rec restore n =
    match !h  with
      | [] -> pr_list := []
      | (i,_)::l when (i > n) -> begin h := l;restore n end
      | (_,l)::_ ->
        pr_list   :=   List.map (fun (a,(b,c)) -> (ref a, (b,c))) l in
    add_register save restore

  
let pp_real_cmp fmt rcmp =
  match rcmp with
    | Ast.Eapp(op,[e1;e2]) when EcTerm.is_op EQ op ->
      Format.fprintf fmt "%a@ =@ %a"
        PpAst.pp_real_exp e1 PpAst.pp_real_exp e2
    | Ast.Eapp(op,[e1;e2]) when EcTerm.is_op REAL_LE op ->
      Format.fprintf fmt "%a@ <=@ %a"
        PpAst.pp_real_exp e1 PpAst.pp_real_exp e2
    | _ -> assert false

(* TODO check that the name is also different than axioms name and v.s *)
let add_Pr name (rcmp:real_exp) hint =
  check_not_in_list "claim" (List.map snd !pr_list) name dummy_pos;
  EcUtil.verbose "@[<hov 2>Proved claim %s@ :@ @[%a@].@]@." name pp_real_cmp rcmp;
  pr_list := (ref true,(name, rcmp)):: !pr_list;
  pr_list_export := (ref true,(name, rcmp, hint))::!pr_list_export

let unset_Pr l =
  List.iter (fun (r,(s,_)) -> if List.mem s l then r := false) !pr_list

let set_Pr l =
  List.iter (fun (r,(s,_)) -> if List.mem s l then r := true) !pr_list

let reset () = pr_list := []


(* {2 Computation of probability } *)
type p_base =
  | Pint of var_exp
  | Ppred of bool * var_exp
  | Prandom of var * (oper,var_exp) g_random * p_exp
  | Ple of p_exp


and p_exp = (var, p_base) v_exp

(* {3 Free variables} *)

let rec fv_p_base pb =
  match pb with
    | Pint e -> EcTerm.fv_exp e
    | Ppred(_b, e) -> EcTerm.fv_exp e
    | Prandom(y,r,p) ->
      Vset.union (Vset.remove y (EcTerm.fv_exp (Ernd r))) (fv_p_exp p)
    | Ple p -> fv_p_exp p

and fv_p_exp p =
  EcTerm.fold_var_in_exp 
    Vset.remove (fun res pb -> Vset.union res (fv_p_base pb)) 
    Vset.empty p

(* let fv_sum = List.fold_left (fun res p -> Vset.union res (fv_p_exp p))  *)
(*   Vset.empty *)

(* let is_fv_p_exp x p = Vset.mem x (fv_p_exp p) *)

(* Equality *)
let rec eq_pexp p1 p2 = EcTerm.g_eq_exp EcTerm.eq_var eq_base p1 p2
and eq_base b1 b2 = 
  match b1, b2 with
  | Pint e1, Pint e2 -> EcTerm.eq_exp e1 e2
  | Ppred(b1,e1), Ppred(b2,e2) ->
      b1 = b2 && EcTerm.eq_exp e1 e2
  | Prandom(x1,r1,p1), Prandom(x2,r2,p2) ->
      EcTerm.eq_var x1 x2 && 
      EcTerm.eq_random r1 r2 &&
      eq_pexp p1 p2
  | Ple p1, Ple p2 -> eq_pexp p1 p2
  | _, _ -> false


(* Constructors on integers *)

let mk_int i = Ecnst (Eint i)

let i_0 : var_exp = mk_int 0
let i_1 : var_exp = mk_int 1
let i_2 : var_exp = mk_int 2

let mk_iadd (i1:var_exp) (i2:var_exp) : var_exp =
  if EcTerm.eq_exp i1 i_0 then i2
  else if EcTerm.eq_exp i2 i_0 then i1
  else Eapp(Global.op_int_add, [i1;i2])

let mk_isub (i1:var_exp) (i2:var_exp) : var_exp =
  if EcTerm.eq_exp i2 i_0 then i1
  else Eapp(Global.op_int_sub, [i1;i2])

let mk_ile (i1:var_exp) (i2:var_exp) : var_exp =
  (Eapp(Global.op_int_le, [i1;i2]))

let mk_imax (i1:var_exp) (i2:var_exp) : var_exp =
  Eif(mk_ile i1 i2, i2, i1)

let mk_imin (i1:var_exp) (i2:var_exp) : var_exp =
  Eif(mk_ile i1 i2, i1, i2)

let mk_size (i1:var_exp) (i2:var_exp) : var_exp =
  mk_isub (mk_iadd (mk_imax i1 i2) i_1) i1


(* Constructors on reals *)
let mk_rint i =
  Eapp(Global.op_real_of_int, [mk_int i])

let mk_pint i =
  match i with
    | Ecnst (Eint i) -> mk_int i
    | _ -> Ebase (Pint i)

let r_of_int i = Eapp(Global.op_real_of_int, [mk_pint i])

let r_0 = mk_rint 0
let r_1 = mk_rint 1
(* let r_2 = mk_rint 2 *)

    
let mk_radd p1 p2 =
  if eq_pexp p1 r_0 then p2
  else if eq_pexp p2 r_0 then p1
  else Eapp(Global.op_real_add, [p1;p2])

let mk_rsub p1 p2 =
  if p2 == r_0 then p1 else Eapp(Global.op_real_sub, [p1;p2])

let rec mk_rmul p1 p2 =
  if eq_pexp p1 r_0 || eq_pexp p2 r_0 then r_0
  else if eq_pexp p1 r_1 then p2
  else if eq_pexp p2 r_1 then p1
  else
    match p1 with
      | Eapp(op,[p11;p12]) when
          (EcTerm.is_op REAL_ADD op || EcTerm.is_op REAL_SUB op) ->
        Eapp(op, [mk_rmul p11 p2; mk_rmul p12 p2])
      | _ ->
        match p2 with
          | Eapp(op,[p21;p22]) when
              (EcTerm.is_op REAL_ADD op || EcTerm.is_op REAL_SUB op) ->
            Eapp(op, [mk_rmul p1 p21; mk_rmul p1 p22])
          | _ -> Eapp(Global.op_real_mul, [p1;p2])


let mk_rdiv p1 p2 =
  if eq_pexp p1 r_0 then r_0
  else if eq_pexp p2 r_1 then p1
  else Eapp(Global.op_real_div, [p1;p2])

let mk_rinv p =
  if eq_pexp p r_1 then r_1 else  Eapp(Global.op_real_div, [r_1;p])

(* {3 Constructors } *)
let rec mk_predb b pred =
  match pred with
    | Ecnst (Ebool b') ->
      if b then
        if b' then r_1 else r_0
      else
        if b' then r_0 else r_1
    | Eapp(op,[e1;e2]) when EcTerm.is_op AND op && b = true ->
      mk_rmul (mk_predb true e1) (mk_predb true e2)

    | _ -> Ebase(Ppred(b,pred))

let mk_pred pred = mk_predb true pred

(* {3 Building predicate} *)

let mkPle p =
  match p with
    | Ebase (Ple p) -> Ebase (Ple p)
    | _ -> Ebase (Ple p)

let mkPredLe u1 u2 =
  mk_pred (mk_ile u1 u2)

let mkPredBound u1 t u2 =
  Ebase(Ppred(true, (Eapp(Global.bool_and, [mk_ile u1 t; mk_ile t u2]))))


(* { Simplification } *)

let mk_app op args =
  match args with
    | [a1;a2] when EcTerm.is_op INT_ADD op -> mk_iadd a1 a2
    | [a1;a2] when EcTerm.is_op INT_SUB op -> mk_isub a1 a2
    | [a1;a2] when EcTerm.is_op EQ op && EcTerm.eq_exp a1 a2 ->
      Ecnst (Ebool true)
    | [a1;a2] when EcTerm.is_op INT_LE op && EcTerm.eq_exp a1 a2 ->
      Ecnst (Ebool true)

    | [a1]
        when EcTerm.is_op NOT op && EcTerm.eq_exp a1 (Ecnst (Ebool true)) ->
      (Ecnst (Ebool false))
    | [a1]
        when EcTerm.is_op NOT op && EcTerm.eq_exp a1 (Ecnst (Ebool false)) ->
      (Ecnst (Ebool true))
    | _ -> Eapp(op, args)

let rec simplify e =
  match e with
    | Ecnst _ | Ebase _ -> e
    | Ernd _ -> assert false
    | Eapp (op, args) -> mk_app op (List.map simplify args)
    | Epair l -> Epair (List.map simplify l)
    | Elet(vs,e1,e2) ->
        Elet(vs,simplify e1, simplify e2)
    | Eif(b,e1, e2) ->
      match simplify b with
        | Ecnst (Ebool b) -> if b then simplify e1 else simplify e2
        | r -> Eif(r,simplify e1, simplify e2)


let mk_rapp op args =
  match args with
    | [r1;r2] when  EcTerm.is_op REAL_ADD op -> mk_radd r1 r2
    | [r1;r2] when  EcTerm.is_op REAL_SUB op -> mk_rsub r1 r2
    | [r1;r2] when  EcTerm.is_op REAL_MUL op -> mk_rmul r1 r2
    | [r1;r2] when  EcTerm.is_op REAL_DIV op -> mk_rdiv r1 r2
    | _ -> Eapp(op, args)

let rec simplify_p p =
  match p with
    | Ecnst _ -> p
    | Ebase (Pint i) -> mk_pint (simplify i)
    | Ebase (Ppred (b, pred)) -> mk_predb b (simplify pred)
    | Ebase (Prandom _) -> p
    | Ebase (Ple p) -> mkPle (simplify_p p)
    | Eapp (op, args) -> mk_rapp op (List.map simplify_p args)
    | _ -> assert false


(* {3 Building random } *)

let is_random_eq x op e1 e2 =
  EcTerm.is_op EQ op &&
    ((EcTerm.eq_exp e1 (Ebase x) && not (Vset.mem x (EcTerm.fv_exp e2)))
     || (EcTerm.eq_exp e2 (Ebase x) && not (Vset.mem x (EcTerm.fv_exp e1))))

let is_random_le x op e1 e2 =
  EcTerm.is_op INT_LE op &&
    EcTerm.eq_exp e1 (Ebase x) &&
    not (Vset.mem x (EcTerm.fv_exp e2))

let is_random_ge x op e1 e2 =
  EcTerm.is_op INT_LE op &&
    EcTerm.eq_exp e2 (Ebase x) &&
    not (Vset.mem x (EcTerm.fv_exp e1))

let is_random_bound x op e1 e2 =
  EcTerm.is_op AND op &&
    begin match e1 with
      | Eapp(op,[e11;e12]) -> is_random_ge x op e11 e12
      | _ -> false
    end &&
    begin match e2 with
      | Eapp(op,[e21;e22]) -> is_random_le x op e21 e22
      | _ -> false
    end

let get_bound _x _op e1 e2 =
  match e1, e2 with
    | Eapp(_,[e11;_]), Eapp(_,[_;e22]) -> (e11,e22)
    | _ -> raise Not_found


let is_random_in x op e1 e2 =
  EcTerm.is_op IN_LIST op &&
    EcTerm.eq_exp e1 (Ebase x) &&
    not (Vset.mem x (EcTerm.fv_exp e2))

let cardinal (r: (oper,var_exp) Ast.g_random) =
  match r with
    | Rinter(e1, e2) -> mk_size e1 e2
    | Rbool -> i_2
    | Rbitstr e -> Eapp(Global.op_int_pow, [i_2; e])
    | Rexcepted(_r, _e) -> not_implemented "EcProba.cardinal: Rexcepted"
    | Rapp(_r, _e) -> not_implemented "EcProba.cardinal: Rapp"

let proba_pred x r b e =
  match e with
    | Eapp(op,[e1;e2]) when is_random_eq x op e1 e2 ->
      let pr =
        match r with
          | Rinter (u1,u2) ->
            let t = if EcTerm.eq_exp e1 (Ebase x) then e2 else e1 in
            let bound = mkPredBound u1 t u2 in
            let card = mk_size u1 u2 in
            mk_rmul (mk_rinv (r_of_int card)) bound
          | _ -> mk_rinv (r_of_int (cardinal r)) in
      if b then pr else mk_rsub r_1 pr
    | Eapp(op,[e1;e2]) when is_random_bound x op e1 e2 ->
      let pr =
        match r with
          | Rinter (u1, u2) ->
            let t1, t2 = get_bound x op e1 e2 in
            let size = mk_isub (mk_iadd (mk_imin t2 u2) i_1) (mk_imax t1 u1) in
            let card = mk_size u1 u2 in
            mk_rmul
              (mk_rdiv (r_of_int size) (r_of_int card))
              (mkPredLe t1 t2)
          | _ -> assert false in
      if b then pr else mk_rsub r_1 pr
    | Eapp(op,[e1;e2]) when is_random_in x op e1 e2 ->
      let pr =
        let length = r_of_int (Eapp(Global.op_length_list x.Ast.v_type,[e2])) in
        mkPle (mk_rdiv length (r_of_int (cardinal r))) in
      if b then pr else mk_rsub r_1 pr 
    | _ -> Ebase (Prandom(x, r, Ebase(Ppred(b, e))))



let rec split_prod x p =
  match p with
    | Eapp(op, [p1;p2]) when EcTerm.is_op REAL_MUL op ->
      let p11,p12 = split_prod x p1 in
      let p21,p22 = split_prod x p2 in
      mk_rmul p11 p21, mk_rmul p12 p22
    | _ ->
      if Vset.mem x (fv_p_exp p) then r_1, p
      else p, r_1

let is_mul p = 
  match p with
  | Eapp(op, _) -> EcTerm.is_op REAL_MUL op
  | _ -> false

let rec pp_p_base fmt pb =
  match pb with
    | Pint e -> PpAst.pp_exp fmt e
    | Ppred(b,e) ->
      Format.fprintf fmt "1[%s%a]" (if b then "" else "!") PpAst.pp_exp e
    | Prandom(x,r,p) ->
      Format.fprintf fmt "Pr[%a=%a : %a]" PpAst.pp_var x
        PpAst.pp_random r pp_p_exp p
    | Ple p -> Format.fprintf fmt "Ple(%a)" pp_p_exp p

and pp_p_exp fmt p =
  PpAst.g_pp_exp PpAst.pp_var pp_p_base 0 fmt p

let rec push_proba x r p =
  let res = if Vset.mem x (fv_p_exp p) then
    match p with
      | Ebase pb ->
        begin match pb with
          | Pint _ -> p
          | Ppred (b,e) -> proba_pred x r b e
          | Ple p -> mkPle (push_proba x r p)
          | _ -> Ebase (Prandom(x, r, p))
        end
      | Eapp(op, _args) when EcTerm.is_op REAL_MUL op ->
        let p1, p2 = split_prod x p in
        let p2 = 
          if is_mul p2 then Ebase (Prandom(x, r, p2))
          else push_proba x r p2 in
        mk_rmul p1 p2
      | Eapp(op, args)
          when EcTerm.is_op REAL_ADD op || EcTerm.is_op REAL_SUB op ->
        Eapp(op, List.map (push_proba x r) args)
      | _ -> 
          Ebase (Prandom(x, r, p))
  else p in
  res


(* {3 Conditionnal} *)
let mk_cond e p1 p2 =
  let pb = mk_predb true e in
  let pnb = mk_predb false e in
  mk_radd (mk_rmul pb p1) (mk_rmul pnb p2)

(* {3 Substitution } *)

let rec subst_p_base s p =
  match p with
    | Pint e -> mk_pint (EcTerm.subst_exp s e)
    | Ppred(b,e) -> Ebase(Ppred(b,EcTerm.subst_exp s e))
    | Prandom(y,r,p) ->
      begin match EcTerm.subst_exp s (Ernd r) with
        | Ernd r' -> push_proba y r' (subst_p_exp s p)
        | _ -> assert false
      end
    | Ple p -> Ebase (Ple (subst_p_exp s p))

and subst_p_exp s p = EcTerm.map_var_in_exp (fun v -> v) (subst_p_base s) p


let sem_proba_assign l e p =
  assert (EcTerm.is_var_exp e);
  match l with
    | Ltuple vars ->
      begin match vars with
        | [v] ->
          subst_p_exp [v,e] p

        | [v1;v2] ->
          let ty = Ttuple[v1.v_type; v2.v_type] in
          let e1 = Eapp(Global.op_fst ty, [e]) in
          let e2 = Eapp(Global.op_snd ty, [e]) in
          subst_p_exp [v1,e1;v2,e2] p

        | [v1;v2;v3] ->
          let ty = Ttuple[v1.v_type; v2.v_type] in
          let ty' = Ttuple[ty; v3.v_type] in
          let e1 = Eapp(Global.op_fst ty, [Eapp(Global.op_fst ty', [e])]) in
          let e2 = Eapp(Global.op_snd ty, [Eapp(Global.op_fst ty', [e])]) in
          let e3 = Eapp(Global.op_snd ty, [e]) in
          subst_p_exp [v1,e1;v2,e2;v3,e3] p

        | _ ->
          not_implemented "sem_proba_assign to %d variables" (List.length vars)
      end
    | Lupd(v, e') ->
      subst_p_exp [v,Eapp(Global.op_upd_map v.v_type, [Ebase v; e'; e])] p


let rec sem_proba_random rs p =
  match rs with
    | Sasgn(Ltuple[x],Ernd r) :: rs ->
      push_proba x r (sem_proba_random rs p)
    | [] -> p
    | _ -> assert false

(* exception PRANDOM *)

let exp_of_p_exp venv p =
  let le_list = ref [] in
  let venv = ref venv in
  let rec exp_of_p_base pb =
    match pb with
      | Pint e -> e
      | Ppred (b,e) ->
        let re = Eapp(Global.op_real_of_bool, [e]) in
        if b then re else mk_rsub r_1 re
      | Prandom _ ->
         user_error "Encounter randomized expression: %a" pp_p_exp p
      | Ple p ->
        let rp = exp_of_p_exp p in
        let venv', v = Global.fresh_var !venv "var____le" Ast.Treal in
        venv := venv';
        le_list := (Ebase v,rp) :: !le_list;
        Ebase v
  and exp_of_p_exp p = 
    EcTerm.map_var_in_exp (fun _ -> assert false) exp_of_p_base p in
  let res = exp_of_p_exp p in
  !le_list, res

let p_exp_of_rbase (_,_) =
  user_error "p_exp_of_rbase the expression contain G.f[e]"

let p_exp_of_real_exp = EcTerm.map_var_in_exp (fun v -> v) p_exp_of_rbase

let rec sem_proba_stmt venv c sum le bound =
  match c with
    | [] -> sum
    | i::c ->
      let sum' = sem_proba_stmt venv c sum le bound in
      sem_proba venv i sum' le bound

and sem_proba venv i p le bound =
  let fv = fv_p_exp p in
  let modi = EcTerm.modified_stmt [i] in
  if Vset.disjoint fv modi then p
  else
    match i with
      | Sasgn(l,r) -> 
        let _venv, rs,e = EcDerandom.derandomize_exp venv (Some l) r in 
        let sem =  (sem_proba_assign l e p) in
        let res = sem_proba_random rs sem in
        res
      | Scall (_,f,_) ->
        let ep = exp_of_p_exp venv (simplify_p p) in
        if WhyCmds.check_computed_pr "sem_proba" !pr_list ep le bound then
          p_exp_of_real_exp bound
        else begin
       
          List.iter (fun ep -> Format.eprintf "%a <= %a -> " PpAst.pp_exp 
            (fst ep) PpAst.pp_exp (snd ep)) (fst ep);
          Format.eprintf "%a" PpAst.pp_exp (snd ep);
          EcUtil.not_implemented "sem_proba:call %a = %a@."
            PpAst.pp_fct_full_name f pp_p_exp p
        end
      | Sif(b,c1,c2) ->
        let venv, rb, b = EcDerandom.derandomize_exp venv None b in
        let p1 = sem_proba_stmt venv c1 p le bound in
        let p2 = sem_proba_stmt venv c2 p le bound in
        sem_proba_random rb (mk_cond b p1 p2)
      | Swhile _ -> not_implemented "EcProba.sem_proba:while"
      | Sassert _ -> not_implemented "EcProba.sem_proba:assert"

let check_bad (* name rcmp *) find_equiv f1 f2 e1 e2 bad bad1 bad2 s =
  assert (EcTerm.eq_exp bad2 bad || EcTerm.eq_exp bad1 bad);
  let (f1', f2', pre, post,_) = find_equiv s in
  (* TODO: check what to do when finding an app equiv *)
  if not (EcTerm.eq_fct f1 f1' && EcTerm.eq_fct f2 f2') then
    user_error "The equivalence relation %s does not refers to %a and %a"
      s PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2;
  if not (WhyCmds.check_implies Fol.Ptrue pre) then
    user_error "The precondition should be a tautology";
  let bad1 = Fol.pred_of_exp Fol.FVleft bad1 in
  let bad2 = Fol.pred_of_exp Fol.FVright bad2 in
  if not (WhyCmds.check_implies post (Fol.piff bad1 bad2)) then
    user_error "The postcondition should be implied by equivalence on bad";
  let eq = Fol.peq (Fol.term_of_exp Fol.FVleft e1)
    (Fol.term_of_exp Fol.FVright e2) in
  let concl = (Fol.pimplies (Fol.pnot bad2) eq) in
  if not (WhyCmds.check_implies post concl) then
    user_error "Cannot prove that postcondition %a@ implies %a"
      Fol.pp_pred post Fol.pp_pred concl


(***********************)
(* Failure event Lemma *)
(***********************)


  
  
let check_computed_pr_bad venv pr_list bad pre p u = 
  let mk_not b = Eapp(Global.bool_not,[b]) in
  let rec find_pred p = 
    match p with
    | Eapp(_, l) -> 
        let rec aux l =
          match l with
          | [] -> raise Not_found
          | p::l -> try find_pred p with _ -> aux l in
        aux l
    | Ebase(Ppred(_, e)) -> e
    | _ -> raise Not_found in
  let rec subst_pred p b v =
    match p with
    | Eapp(op,[p1;p2]) when (EcTerm.is_op REAL_ADD op) ->
        mk_radd (subst_pred p1 b v) (subst_pred p2 b v)
    | Eapp(op,[p1;p2]) when (EcTerm.is_op REAL_SUB op) ->
        mk_rsub (subst_pred p1 b v) (subst_pred p2 b v)
    | Eapp(op,[p1;p2]) when (EcTerm.is_op REAL_MUL op) ->
        mk_rmul (subst_pred p1 b v) (subst_pred p2 b v)
    | Eapp(op,[p1;p2]) when (EcTerm.is_op REAL_DIV op) ->
        mk_rdiv (subst_pred p1 b v) (subst_pred p2 b v)
    | Eapp(op,l) -> Eapp(op, List.map (fun p -> subst_pred p b v) l)
    | Ebase(Ppred(s,e)) when EcTerm.eq_exp b e ->
        mk_predb s (Ecnst (Ebool v))
    | _ -> p in
  let rec split cond p =
    try 
      let b = find_pred p in
      let pt = subst_pred p b true in
      let pf = subst_pred p b false in
      split (b::cond) pt &&
      split (mk_not b :: cond) pf
    with Not_found ->
        let ep = exp_of_p_exp venv p in
        WhyCmds.check_computed_pr_cond "pr_bad" pr_list cond ep true u 
  in
   split [mk_not bad; pre] p

let clk =   
  let name = "  lk  " in
  let _, wt = EcTerm.add_why3_type [] Tint in
  let ls = 
    Why3.Term.create_lsymbol (Why3.Ident.id_fresh name) 
      [] (Some wt) in
  let cb = { c_name = "  lk ";
             c_poly = [];
             c_type = Tint;
             c_pos = dummy_pos;
             c_def = None;
             c_why3 = ls,None ;
             c_native_why = false } in
  Global.add_cnst cb;
  (Ecst(cb,[]))

let check_inv_bad c bad count lcount u =
  let checked = ref [] in
  let tbad = Fol.term_of_exp Fol.FVleft bad in
  let tcount = Fol.term_of_exp Fol.FVleft count in
  let fv = Vset.union (EcTerm.fv_exp bad) (EcTerm.fv_exp count) in
  if not (Vset.for_all (fun x -> x.v_glob) fv) then
    user_error "all variables in bad and count must be global";
  let check_lasgn l =
    match l with
      | Ltuple l -> not (List.exists (fun x -> Vset.mem x fv) l)
      | Lupd(x,_) -> not (Vset.mem x fv) in
  let rec check_i i =
    match i with
      | Sasgn (l,_e) -> check_lasgn l
      | Scall (l,f,_args) ->
        check_lasgn l && check_fun f
      | Sif (_e,c1,c2) -> check_s c1 && check_s c2
      | Swhile (_e,c) -> check_s c
      | Sassert _ -> true
  and check_s c = 
    List.for_all check_i c
  and check_fun f =
    if List.exists (EcTerm.eq_fct f) !checked then true
    else
      let res = check_fun_body f in
      if res then  checked := f :: !checked;
      res
  and check_fun_body f =
    let fmod = List.fold_right Vset.add f.f_modify Vset.empty in
    (* First we try a simple test *)
    Vset.equal (Vset.inter fmod fv) Vset.empty ||
    (* Second we inspect the body *)
      match f.f_body with
        | FctAdv (_, os) -> List.for_all check_fun os
        | FctDef fdef ->
        (* Try to use check_s *)
          let c = fdef.f_def in
          check_s c ||
        (* Else use the logical condition *)
          begin
            (* First prove that count does not decrease and
               increases by the corresponding lcount if bad is set *)
            let tone = Ecnst(Eint 1) in
            let elcount = 
              try snd(List.find (fun (f',_) -> EcTerm.eq_fct f f') lcount) 
              with _ -> tone in
            let lcount = Fol.term_of_exp Fol.FVleft elcount in
            let k = Ebase (Fol.logic_lvar "k" Tint) in
            let lk1 = Fol.term_of_exp Fol.FVleft (Ecnst clk) in
            
            let pbad = Fol.pred_of_term tbad in
            let notbad = Fol.pnot pbad in
            let countk = Fol.peq tcount k in
            let lcountk = Fol.peq lcount lk1 in
            let le = Global.op_int_le in
            let pre = Fol.pand notbad (Fol.pand countk lcountk) in
            let mk_le a b = Fol.pred_of_term (Eapp(le,[a;b])) in
            let mk_add e1 e2 = Eapp(Global.op_int_add,[e1;e2]) in
            let post =
              Fol.pand (Fol.pimplies pbad 
                          (Fol.pand (mk_le tone lk1) 
                                    (mk_le (mk_add k lk1) tcount)))
                (Fol.pimplies notbad (mk_le k tcount)) in
            let wp =
              fst (EcDeriv.gen_wp_hl (fun _ -> assert false)  
                     (fun _ -> assert false) (List.rev c) post) in
            if not (WhyCmds.check_implies pre wp) then
              user_error "failure event: cannot prove condition for oracle.";
            (* Second we bound the probability of bad *)
            let venv = Global.fun_local_venv f in
            let p = mk_pred bad in
            let p =
              match (EcTerm.fct_def f).f_return with
              | Some e -> sem_proba_assign (Ltuple [f.f_res]) e p
              | None -> p in
            let pre, u = 
              if lcount = tone then Ecnst (Ebool true), u else 
              let eq = fst (Global.find_op dummy_pos (get_tk_name TK_EQ)
                              [Tint;Tint]) in
              let pre = Eapp(eq,[elcount; Ecnst clk]) in 
              let u = 
                 Eapp(Global.op_real_mul,
                      [Eapp(Global.op_real_of_int,[Ecnst clk]);u]) in
              pre,u in
            let p = simplify_p (sem_proba_stmt venv c p true u) in
            if not (check_computed_pr_bad venv !pr_list bad pre p u) then
              user_error
                "failure event: Computed probability = %a, can not be proved"
                pp_p_exp p;
            true 
          end in
  check_s c

let check_post p1 p2 =
 if not(WhyCmds.check_implies p1 p2)
  then 
   user_error "Cannot prove that postcondition@.  %a@. implies@. %a"
     Fol.pp_pred p1 Fol.pp_pred p2

let failure_event f e n count lcount bad max u =
  (* We want to prove Pr[f : e] <= max * u *)
  (*assert (EcTerm.is_defined_fct f &&
    as_type e bool &&
    is_cnst_exp max && as_type max int
    is_cnst_exp u && as_type u real
    is_var_exp count && as_type count int
    is_var_exp bad && as_type bad bool
    ); *)
  (* Step 1: we check that 
        e => bad && count <= max *)
  let fe = Fol.pred_of_exp Fol.FVleft e in
  let fbad = Fol.pred_of_exp Fol.FVleft bad in
  let fbound= Fol.pred_of_exp Fol.FVleft (Eapp(Global.op_int_le,[count;max])) in
  check_post fe (Fol.pand fbad fbound);
  (* Step 2: we check that f = c1;c2 where length c1 = n *)
  let s = (EcTerm.fct_def f).f_def in
  let c1, c2 = list_shop n s in
  (* Step 3: we check that {true} c1 {!bad && count = 0} *)
  let tzero = Fol.term_of_exp Fol.FVleft (Ecnst (Eint 0)) in
  let tcount = Fol.term_of_exp Fol.FVleft count in
  let fcount0 = Fol.peq tcount tzero in
  let post = Fol.pand (Fol.pnot fbad) fcount0 in
  let wp = fst (EcDeriv.gen_wp_hl (fun _ -> assert false) 
                  (fun _ -> assert false) (List.rev c1) post) in
  if not (WhyCmds.check_implies Fol.Ptrue wp) then
    user_error "failure event: cannot prove the initialization goal";
  (* Step 4: we check that "inv_bad bad_K c2" *)
  if not (check_inv_bad c2 bad count lcount u) then
    user_error "failure event: cannot prove the invariant"

let get_max_u r =
  match r with
    | Eapp(mop,[Eapp(rop,[max]); u]) when EcTerm.is_op REAL_MUL mop
        && EcTerm.is_op REAL_OF_INT rop ->
     (* TODO: Change this *)
      begin match max with
        | Ecnst c -> Ecnst c, u
        | _ -> assert false
      end
    | _ -> user_error "failure_event: the LHS must be of the form max * u"


(* Try to merge probabilities *)

let check_computed_pr venv cond p =
  let mk_not b = Eapp(Global.bool_not,[b]) in
  let rec find_pred p = 
    match p with
    | Eapp(_, l) -> 
        let rec aux l =
          match l with
          | [] -> raise Not_found
          | p::l -> try find_pred p with _ -> aux l in
        aux l
    | Ebase(Ppred(_, e)) -> e
    | _ -> raise Not_found in
  let rec subst_pred p b v =
    match p with
    | Eapp(op,[p1;p2]) when (EcTerm.is_op REAL_ADD op) ->
        mk_radd (subst_pred p1 b v) (subst_pred p2 b v)
    | Eapp(op,[p1;p2]) when (EcTerm.is_op REAL_SUB op) ->
        mk_rsub (subst_pred p1 b v) (subst_pred p2 b v)
    | Eapp(op,[p1;p2]) when (EcTerm.is_op REAL_MUL op) ->
        mk_rmul (subst_pred p1 b v) (subst_pred p2 b v)
    | Eapp(op,[p1;p2]) when (EcTerm.is_op REAL_DIV op) ->
        mk_rdiv (subst_pred p1 b v) (subst_pred p2 b v)
    | Eapp(op,l) -> Eapp(op, List.map (fun p -> subst_pred p b v) l)
    | Ebase(Ppred(s,e)) when EcTerm.eq_exp b e ->
        mk_predb s (Ecnst (Ebool v))
    | _ -> p in
  let rec split cond p =
    try 
      let b = find_pred p in
      let pt = subst_pred p b true in
      let pf = subst_pred p b false in
      split (b::cond) pt &&
      split (mk_not b :: cond) pf
    with Not_found ->
      let bound,concl = exp_of_p_exp venv p in
      WhyCmds.my_check_computed_pr_cond "pr" cond bound concl
  in split cond p

let find_function = 
  let fb _ a = a in
  let fv fopt (f,_) =
    match fopt with
    | Some f' -> 
        if EcTerm.eq_fct f f' then fopt 
        else user_error 
  "compute can be use for expression containing the\
   probabilities of only one function, here the expression contains %a and %a"
      PpAst.pp_fct_name f' PpAst.pp_fct_name f
     | None -> Some f in
  EcTerm.fold_var_in_exp fb fv
 
let rec mk_cnst r =
  match r with
  | Ecnst c -> Ecnst c
  | Ebase _ | Ernd _ -> assert false
  | Epair l -> Epair (List.map mk_cnst l)
  | Eapp(op,args) -> Eapp(op, List.map mk_cnst args)
  | Eif(b,r1,r2) -> Eif(mk_cnst b, mk_cnst r1, mk_cnst r2)
  | Elet(x,r1,r2) -> Elet(x, mk_cnst r1, mk_cnst r2)

let error () =
    user_error "Do not know how to check the probability" 

let merge_proba venv f le r =
  let loosless = EcTerm.is_lossless_fun f in
  let mk_caract e =
    let p = mk_pred e in
    match (EcTerm.fct_def f).f_return with
    | Some e -> sem_proba_assign (Ltuple [f.f_res]) e p
    | None -> p in
  let constant e =
     if le || loosless then e 
     else
       user_error "Can not prove that the function %a is lossless" 
         PpAst.pp_fct_name f in
  let test_le f1 f2 = 
    check_computed_pr venv [] (Eapp(Global.op_real_le, [f1;f2])) in
  let check_le f1 f2 = 
    if not (test_le f1 f2) then error () in
  let check_plus f1 f2 = test_le f1 (mk_rsub r_1 f2) in
  let check_not0 k = 
    let concl = Eapp(Global.bool_not, [Eapp(Global.op_real_eq, [r_0;k])]) in
    if not (check_computed_pr venv [] concl) then error () in
  let rec aux r =
    match r with
    | Ecnst c -> constant (Ecnst c)
    | Ebase(f', e) ->
        assert (EcTerm.eq_fct f f');
        mk_caract e
    | Ernd _ | Epair _ -> assert false
    | Eapp _ when EcTerm.is_cnst_exp r -> constant (mk_cnst r)
    | Eapp(op,[r1;r2]) when EcTerm.is_op REAL_MUL op ->
        if not (EcTerm.is_cnst_exp r1 || EcTerm.is_cnst_exp r2) then error ();
        mk_rmul (aux r1) (aux r2)
    | Eapp(op,[r1;r2]) when EcTerm.is_op REAL_ADD op ->
        let r1,r2 = aux r1, aux r2 in
        if le || check_plus r1 r2 then mk_radd r1 r2
        else error ()
    | Eapp(op,[r1;r2]) when EcTerm.is_op REAL_SUB op ->
        let r1,r2 = aux r1, aux r2 in
        check_le r2 r1;
        mk_rsub r1 r2
    | Eapp(op,[r1;r2]) when EcTerm.is_op REAL_DIV op ->
        if EcTerm.is_cnst_exp r2 then
          let k = mk_cnst r2 in
          let r1 = aux r1 in
          check_not0 k;
          if not le then check_le r1 k;
          mk_rdiv r1 k
        else error ()
    | Eapp _ | Elet _ | Eif _ -> not_implemented "merge_proba: app, let, or if" in
  aux r

type merge_res =
  | Merge_ok
  | Continue of p_exp * p_exp

let check_bound venv f1 le f2 =
  let op = if le then Global.op_real_le else Global.op_real_eq in
  check_computed_pr venv [] (Eapp(op,[f1;f2]))

let rec check_merge venv c f1 le f2 =
  match c with
  | [] -> Continue (f1, f2)
  | i::c ->
      match check_merge venv c f1 le f2 with
      | Merge_ok -> Merge_ok
      | Continue (f1, f2) -> check_merge_instr venv i f1 le f2 

and check_merge_instr venv i f1 le f2 =
(*  verbose "check_merge_instr %a : %a %s %a" 
  PpAst.pp_instr i pp_p_exp f1 (if le then "<=" else "=") pp_p_exp f2; *)
  let fv1, fv2 = fv_p_exp f1, fv_p_exp f2 in
  let modi = EcTerm.modified_stmt [i] in
  let dsj1, dsj2 = Vset.disjoint fv1 modi, Vset.disjoint fv2 modi in
  if dsj1 && dsj2 then Continue(f1,f2)
  else
    match i with
    | Sasgn(l,r) -> 
        let _venv, rs,e = EcDerandom.derandomize_exp venv (Some l) r in
        let f1 = 
          if dsj1 then f1 
          else sem_proba_random rs (sem_proba_assign l e f1) in
        let f2 = 
          if dsj2 then f2
          else sem_proba_random rs (sem_proba_assign l e f2) in
        Continue(f1,f2)
    | Scall (_,_,_) ->
        if check_bound venv f1 le f2 then Merge_ok
        else error ()
    | Sif(b,c1,c2) ->
        let venv, rb, b = EcDerandom.derandomize_exp venv None b in
        let res1 = check_merge venv c1 f1 le f2 in
        let res2 = check_merge venv c2 f1 le f2 in
        begin match res1, res2 with
        | Merge_ok, Merge_ok -> Merge_ok
        | Merge_ok, Continue(f21,f22) ->
            let f1 = sem_proba_random rb (mk_rmul (mk_predb false b) f21) in 
            let f2 = sem_proba_random rb (mk_rmul (mk_predb false b) f22) in 
            Continue(f1,f2)
        | Continue(f11,f12), Merge_ok ->
            let f1 = sem_proba_random rb (mk_rmul (mk_predb false b) f11) in 
            let f2 = sem_proba_random rb (mk_rmul (mk_predb false b) f12) in 
            Continue(f1,f2)
        | Continue(f11,f12), Continue(f21,f22) ->
            let f1 = sem_proba_random rb (mk_cond b f11 f21) in
            let f2 = sem_proba_random rb (mk_cond b f12 f22) in
            Continue(f1,f2)
        end
    | Swhile _ ->
        if check_bound venv f1 le f2 then Merge_ok
        else error ()
    | Sassert _ -> not_implemented "EcProba.sem_proba:assert"

let check_compute name (rcmp:real_exp) = 
  let r1, le, r2 =
    match rcmp with
    | Eapp(op,[r1;r2]) when (EcTerm.is_op EQ op || EcTerm.is_op REAL_LE op) ->
        r1, EcTerm.is_op REAL_LE op, r2
    | _ -> user_error "Do not know how to check the probability"
  in
  match find_function (find_function None r1) r2 with
  | None -> 
      if not (WhyCmds.check_pr name !pr_list rcmp) then
        user_error "Can not prove %s" name
  | Some f -> 
      if not (EcTerm.is_defined_fct f) then
        user_error "The function %a should not be abstract" 
          PpAst.pp_fct_name f;
      let venv = Global.fun_local_venv f in
      let r1 = merge_proba venv f false r1 in
      let r2 = merge_proba venv f le r2 in 
      match check_merge venv (EcTerm.fct_def f).f_def r1 le r2 with
      | Merge_ok -> ()
      | Continue(f1,f2) ->
          if not (check_bound venv f1 le f2) then begin
            verbose "check compute fail try another strategy";            
            if check_bound venv r1 le r2 then ()
            else error ()
          end


(***********************)
(* The main checker    *)
(***********************)
(* TODO: check what to do when finding an app equiv *)

let check_pr find_equiv name (rcmp:real_exp) hint =
  match rcmp, hint with
  | _, AstLogic.Pr_compute -> check_compute name rcmp
  | Eapp(op,[Ebase(f1,e1);r]), AstLogic.Pr_failure(n,bad,count,lcount) when
      EcTerm.is_defined_fct f1 && EcTerm.is_op REAL_LE op ->
        let max, u = get_max_u r in
        failure_event f1 e1 n count lcount bad max u
  | _, AstLogic.Pr_admit -> ()
  | _, AstLogic.Pr_none ->
      if not (WhyCmds.check_pr name !pr_list rcmp) then
        user_error "can not prove %s" name
  | Eapp(op,[Ebase(f1, e1);Ebase(f2, e2)]), AstLogic.Pr_equiv s ->
      let (f1', f2', pre, post,approx) = find_equiv s in
      let nsym = 
        if EcTerm.eq_fct f1 f1' && EcTerm.eq_fct f2 f2' then true
        else if EcTerm.eq_fct f1 f2' && EcTerm.eq_fct f2 f1' then false
        else user_error "The equivalence relation %s does not refer to %a and %a"
            s PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2 in
      begin match approx with
      | None -> ()
      | Some(_alpha, _delta) ->
          (* TODO : change the error message *)
          (* TODO : can we check that alpha = 1 and delta = 0,
             and does it work if op = "=" or just for "<=" *)
          user_error "can not used approximate equiv here ..."
      end;
      let eqg = EcTyping.mkeq_globals f1 f2 in
      if not (WhyCmds.check_implies eqg pre) then
        user_error "The precondition should be implies by %a"
          Fol.pp_pred eqg;
      let fe1 = 
        if nsym then Fol.term_of_exp Fol.FVleft e1 
        else Fol.term_of_exp Fol.FVright e1 in
      let fe2 = 
        if nsym then Fol.term_of_exp Fol.FVright e2 
        else Fol.term_of_exp Fol.FVleft e2 in
      let p =
        if EcTerm.is_op EQ op then Fol.peq fe1 fe2
        else
          if EcTerm.is_op REAL_LE op then
            Fol.pimplies(Fol.pred_of_term fe1) (Fol.pred_of_term fe2)
          else user_error "The comparison should be == or <="
      in
(*      Format.printf "Check %a implies %a"
        Fol.pp_pred post Fol.pp_pred p; *)
      check_post post p
  | Eapp(op,[Ebase(f1, e1);
             Eapp(add,[Eapp(mul,[alpha; Ebase(f2, e2)]);
                       delta])]), AstLogic.Pr_equiv s when 
       EcTerm.is_op REAL_LE op &&
       EcTerm.is_op REAL_ADD add &&                          
       EcTerm.is_op REAL_MUL mul ->
      let (f1', f2', pre, post,approx) = find_equiv s in
      let alpha', delta' = 
        match approx with
        | None -> 
            (* TODO : alpha' = 1 and delta' = 0 *)
            user_error "an approximate equiv expected here"
        | Some(alpha, delta) -> alpha, delta in
      if not (EcTerm.eq_fct f1 f1' && EcTerm.eq_fct f2 f2') then
        user_error "The equivalence relation %s does not refer to %a and %a"
          s PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2;
      let eqg = EcTyping.mkeq_globals f1 f2 in
      if not (WhyCmds.check_implies eqg pre) then
        user_error "The precondition should be implies by %a"
          Fol.pp_pred eqg;
      (* We check that alpha' <= alpha & delta' <= delta *)
      let falpha = Fol.term_of_exp Fol.FVleft (mk_cnst alpha) in
      let fdelta = Fol.term_of_exp Fol.FVleft (mk_cnst delta) in
      let cond = 
        Fol.pand (Fol.ple_real alpha' falpha) 
          (Fol.ple_real delta' fdelta) in
      if not (WhyCmds.check_implies Fol.Ptrue cond) then
        user_error "the bounds are too big ...";
      (* We check the post *)
      let fe1 = Fol.term_of_exp Fol.FVleft e1 in
      let fe2 = Fol.term_of_exp Fol.FVright e2 in
      let p = Fol.pimplies(Fol.pred_of_term fe1) (Fol.pred_of_term fe2) in
      check_post post p

  | Eapp(le,[ Eapp(abs,[Eapp(minus,[Ebase(f1,e1);Ebase(f2,e2)])]);
              Ebase(f3,bad) ]), AstLogic.Pr_bad(bad1,bad2,s) when
                (EcTerm.eq_fct f2 f3 || EcTerm.eq_fct f1 f3) &&
                EcTerm.is_op REAL_LE le &&
                EcTerm.is_op REAL_ABS abs &&
                EcTerm.is_op REAL_SUB minus ->
      check_bad (* name rcmp *) find_equiv f1 f2 e1 e2 bad bad1 bad2 s
  | Eapp(le,[Ebase(f1,e1);
               Eapp(add,[Ebase(f2,e2);Ebase(f3,bad)])]),
            AstLogic.Pr_bad(bad1,bad2,s) when
                (EcTerm.eq_fct f2 f3 || EcTerm.eq_fct f1 f3) &&
                  EcTerm.is_op REAL_LE le &&
                  EcTerm.is_op REAL_ADD add ->
      check_bad (* name rcmp *) find_equiv f1 f2 e1 e2 bad bad1 bad2 s
  | Eapp(eq,[Ebase(f1,e1);
               Eapp(add,[Ebase(f2,Eapp(and1,[e2;a1]));
                         Ebase(f3,Eapp(and2,[e3;Eapp(no,[a2])]))])]),
                    AstLogic.Pr_split when EcTerm.is_op EQ eq ->
      let test =
          EcTerm.is_op AND and1 &&
          EcTerm.is_op AND and2 &&
          EcTerm.is_op REAL_ADD add &&
          EcTerm.is_op NOT no &&
          EcTerm.eq_fct f1 f2 && EcTerm.eq_fct f1 f3 &&
          EcTerm.eq_exp e1 e2 && EcTerm.eq_exp e1 e3 &&
          EcTerm.eq_exp a1 a2 in
      if not test then
        user_error
          "The conclusion should have the form G.f[e] = G.f[e&&a] + G.f[e&&!a]"
  | Eapp(le, [Ebase(f1,e1);
               Eapp(add,[Ebase(f2,e2);
                         Ebase(f3,e3)])]),
                    AstLogic.Pr_split when EcTerm.is_op REAL_LE le && 
                                           EcTerm.is_op REAL_ADD add ->
       if EcTerm.eq_fct f1 f2 && EcTerm.eq_fct f2 f3 then
         begin
           let fe1 = Fol.pred_of_exp Fol.FVleft e1 in
           let fe2 = Fol.pred_of_exp Fol.FVleft e2 in
           let fe3 = Fol.pred_of_exp Fol.FVleft e3 in
           let p = Fol.pimplies fe1 (Fol.por fe2 fe3) in
           if not (WhyCmds.check_implies Fol.Ptrue p) then
             user_error "Can not prove %a" Fol.pp_pred p
         end
       else user_error 
           "The conclusion should have the form G.f[e1] <= G.f[e2] + G.f[e3]"
  | _, AstLogic.Pr_split ->
        user_error "The conclusion should have the form G.f[e1] <= G.f[e2] + G.f[e3] or G.f[e] = G.f[e&&a] + G.f[e&&!a]"

  | Eapp(cmp,[Ebase(f1,e1);Ebase(f2,e2)]), AstLogic.Pr_same ->
      let test =
        EcTerm.eq_fct f1 f2 &&
          (EcTerm.is_op EQ cmp || EcTerm.is_op REAL_LE cmp )
      in
      if test then
        begin
          let fe1 = Fol.term_of_exp Fol.FVleft e1 in
          let fe2 = Fol.term_of_exp Fol.FVleft e2 in
          let p =
            if EcTerm.is_op EQ cmp then Fol.peq fe1 fe2
            else Fol.pimplies(Fol.pred_of_term fe1) (Fol.pred_of_term fe2) in
          if not (WhyCmds.check_implies Fol.Ptrue p) then
            user_error "Can not prove %a" Fol.pp_pred p
        end
      else user_error
        "The conclusion should have the form G.f[e1] cmp G.f[e2] with cmp is = or <="
  | _, _ -> user_error "Do not know how to check the claim"



let check_and_add check find_equiv name rcmp hint =
  if check then check_pr find_equiv name rcmp hint;
  add_Pr name rcmp hint

