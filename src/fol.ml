(** First Order Logic representation. *)
(* ------------------------------------------------------------------------ *)

open EcUtil

(* ------------------------------------------------------------------------ *)
(** {2 FOL types} *)

(** {3 Variables} *)

type lv_side = FVleft | FVright

type lv_base =
  | FVpgVar of Ast.var * lv_side
  | FVlogic of string * Ast.type_exp

type lvar = { lv_base: lv_base; lv_id: UID.lvar }

let pp_lv_side fmt side = match side with
  | FVleft -> Format.fprintf fmt "{1}"
  | FVright -> Format.fprintf fmt "{2}"


let name_tbl = 
  Hashtbl.create 1997
let var_tbl =
  Hashtbl.create 1997

let base_name lv =
  assert (lv.lv_id <> UID.empty_lvar);
  match lv.lv_base with
  | FVpgVar (v,side) -> 
      v.Ast.v_name ^ (if side = FVleft then "_L" else "_R")
  | FVlogic (name,_) -> name

let add_var lv =
  let s = base_name lv in
  let s = 
    if Hashtbl.mem name_tbl s then 
      let s = s ^ "_" in
      let rec loop i =
        let s = s ^ (string_of_int i) in
        if Hashtbl.mem name_tbl s then loop (i+1) 
        else s in
      loop 0 
    else s in
  Hashtbl.add name_tbl s ();
  Hashtbl.add var_tbl lv s;
  s

let get_name lv =
  try Hashtbl.find var_tbl lv 
  with _ -> add_var lv

let reset_names () =
  Hashtbl.clear name_tbl;
  Hashtbl.clear var_tbl

let lv_name lv = match lv.lv_base with
  | FVpgVar (v,_) -> v.Ast.v_name
  | FVlogic (s, _) -> s

let lv_type lv = match lv.lv_base with
  | FVpgVar (v,_side) -> v.Ast.v_type
  | FVlogic (_, ty) -> ty

let debug_type = ref false

let pp_lvar fmt lv = 
  match lv.lv_base with
  | FVpgVar (v,side) when lv.lv_id = UID.empty_lvar -> 
      Format.fprintf fmt "%a%a" PpAst.pp_var v pp_lv_side side
  | _ -> Format.fprintf fmt "%s" (get_name lv)



let pp_lvar fmt lv =
  let pp_type fmt lv = if !debug_type then
    Format.fprintf fmt "(* %a *)" PpAst.pp_type_exp_d (lv_type lv) in
  Format.fprintf fmt "%a%a" pp_lvar lv pp_type lv


let pp_lvar_why fmt lv = match lv.lv_base with
  | FVpgVar (v,_side) ->
    Format.fprintf fmt "%a_%a" PpAst.pp_uid_var v  UID.pp_lvar lv.lv_id
  | FVlogic (name, _ty) ->
    Format.fprintf fmt "%s_%a" name UID.pp_lvar lv.lv_id



let pg_var_of_lvar lv = match lv.lv_base with
  | FVpgVar (v,_side) -> Some (v)
  | _ -> None

let var_of_lvar lv = match lv.lv_base with
  | FVpgVar (v,side) -> Some (v, side)
  | _ -> None

let eq_lvar v1 v2 =
  let eqv = match var_of_lvar v1, var_of_lvar v2 with
    | Some (v1, side1), Some (v2, side2) ->
      EcTerm.eq_var v1 v2 && side1 = side2
    | None, None -> true
    | _, _ -> false in
  (v1.lv_id = v2.lv_id) && eqv 

let lv_compare lv1 lv2 =
  let cmp = match var_of_lvar lv1, var_of_lvar lv2 with
    | Some (v1, side1), Some (v2, side2) ->
      let cmp = EcTerm.var_compare v1 v2 in
      if cmp = 0 then compare side1 side2 else cmp
    | None, Some _ -> -1
    | Some _, None -> 1
    | None, None -> 0
  in if cmp = 0 then compare lv1.lv_id lv2.lv_id else cmp

let fresh_lvar_id v =
  let vid = match v with
    | None -> None
    | Some v -> Some v.Ast.v_id
  in UID.fresh_lvar vid

let fresh_lvar lv =
  { lv with lv_id = fresh_lvar_id (pg_var_of_lvar lv) }

let lvar_of_var v side =
  { lv_base = FVpgVar (v, side); lv_id = UID.empty_lvar }

let logic_lvar name ty =
  { lv_base = FVlogic (name, ty); lv_id = fresh_lvar_id None }

module FVarCompare =
struct
  type t = lvar
  let compare x y = lv_compare x y
end

module FVset = Set.Make(FVarCompare)

(** {3 Terms} *)

type term = (lvar,lvar) Ast.v_exp

let pp_term pri fmt t = PpAst.g_pp_exp pp_lvar pp_lvar pri fmt t

let term_of_exp side (e:Ast.var_exp) : term =
  assert_bug (EcTerm.is_var_exp e) "[term_of_exp] only work on var_exp";
  let do_var (v:Ast.var) : term = Ast.Ebase (lvar_of_var v side) in
  let t = EcTerm.map_var_in_exp (fun v -> lvar_of_var v side) do_var e in
  t


(** {3 Predicates} *)

type why3_pred = 
  | WP_native of Why3.Term.lsymbol
  | WP_locale of Why3.Decl.logic_decl

type predicate = {
    p_name : string;
    p_type : Ast.type_exp list;
    p_def : (lvar list * pred) option;
    p_why3 : why3_pred;
    (* TODO : remove this side effect *)
    mutable p_opaque : bool
  }

and trigger =
  | Tterm of term
  | Tpred of pred

and triggers = trigger list list

and pred =
  | Ptrue
  | Pfalse
  | Pnot of pred
  | Pand of pred * pred
  | Por of pred * pred
  | Pimplies of pred * pred
  | Piff of pred * pred
  | Pif of bool * term * pred * pred
  (* the [bool] is a split information (see. [WhyCmds.check_split_opt]) *)
  | Pforall of lvar * triggers * pred
  | Pexists of lvar * triggers * pred
  | Plet of lvar list * term * pred
  | Papp of predicate * term list
  | Pterm of term

let is_eq_pred p = p.p_name = "="
let is_neq_pred p = p.p_name = "<>"
let is_le_pred p = p.p_name = "<="
let is_lt_pred p = p.p_name = "<"

let lsymbol p = 
  match p.p_why3 with
  | WP_native ls -> ls
  | WP_locale (ls,_) -> ls


let rec get_same_type v lv =
  match lv with 
  | [] -> [], []
  | v' :: lv2 ->
      if EcTerm.seq_type (lv_type v) (lv_type v') then
        let lv1,lv3 = get_same_type v lv2 in
        v'::lv1, lv3
      else [], lv

let rec split_decls lv =
  match lv with
  | [] -> []
  | v :: lv -> 
      let lv1, lv = get_same_type v lv in
      (v::lv1) :: split_decls lv

let pp_lvar_decls fmt lv = 
  let p_decl fmt lv =
    match lv with
    | [] -> assert false
    | v::_ -> 
        Format.fprintf fmt "%a : %a" (pp_list ~sep:", " pp_lvar) lv 
          PpAst.pp_type_exp (lv_type v) in
  let lv = split_decls lv in
  Format.fprintf fmt "%a" (pp_list ~sep:", " p_decl) lv

let rec decompose_forall p =
  match p with
  | Pforall(v, [], p) -> 
      let lv, t, p = decompose_forall p in
      v::lv, t, p
  | Pforall(v, t, p) -> [v],t,p
  | _ -> [], [], p

let rec decompose_exists p =
  match p with
  | Pexists(v, [], p) -> 
      let lv, t, p = decompose_exists p in
      v::lv, t, p
  | Pexists(v, t, p) -> [v],t,p
  | _ -> [], [], p

let rec get_eq_pred p =
  match p with 
  | Papp (p,[Ast.Ebase {lv_base = FVpgVar(v1,FVleft); lv_id = id1};
             Ast.Ebase {lv_base = FVpgVar(v2,FVright); lv_id = id2 }]) when 
               id1 = UID.empty_lvar && id2 = UID.empty_lvar  &&
               is_eq_pred p && v1.Ast.v_name = v2.Ast.v_name ->
    [v1.Ast.v_name], None
  | Pand(Papp(p,[Ast.Ebase {lv_base = FVpgVar(v1,FVleft); lv_id = id1};
                 Ast.Ebase {lv_base = FVpgVar(v2,FVright); lv_id = id2}]), p') when 
               id1 = UID.empty_lvar && id2 = UID.empty_lvar  &&
               is_eq_pred p && v1.Ast.v_name = v2.Ast.v_name ->
    let s,p = get_eq_pred p' in
    v1.Ast.v_name::s, p
  | _ -> [], Some p

let protect = PpAst.protect_on

let rec pp_pred pri fmt p =
  match p with
    | Ptrue -> Format.fprintf fmt "true"
    | Pfalse -> Format.fprintf fmt "false"
    | Papp (p, [])-> Format.fprintf fmt "%s" p.p_name
    | Papp (p, [t1; t2]) when is_eq_pred p ->
        begin match t1, t2 with
        | Ast.Ebase {lv_base = FVpgVar(v1,FVleft); lv_id = id1}, 
          Ast.Ebase {lv_base = FVpgVar(v2,FVright); lv_id = id2} when 
            id1 = UID.empty_lvar && id2 = UID.empty_lvar &&
            v1.Ast.v_name = v2.Ast.v_name ->
            Format.fprintf fmt "={%s}" v1.Ast.v_name
        | _, _ ->
            Format.fprintf fmt (protect (pri > 4) "@[%a =@, %a@]")
              (pp_term 5) t1 (pp_term 6) t2
        end
    | Papp (p, [t1; t2]) when is_neq_pred p ->
      Format.fprintf fmt (protect (pri > 4) "@[%a <>@, %a@]")
          (pp_term 5) t1 (pp_term 6) t2
    | Papp (p, [t1;t2]) when is_le_pred p ->
      Format.fprintf fmt (protect (pri > 4) "@[%a <=@, %a@]")
          (pp_term 5) t1 (pp_term 6) t2
    | Papp (p, [t1;t2]) when is_lt_pred p ->
      Format.fprintf fmt (protect (pri > 4) "@[%a <@, %a@]")
          (pp_term 5) t1 (pp_term 6) t2
    | Papp (p, l) ->
      Format.fprintf fmt "@[%s(%a)@]" p.p_name 
          (pp_list ~sep:",@," (pp_term 0)) l
    | Pimplies (a, b) ->
      Format.fprintf fmt (protect (pri > 1) "%a =>@, %a")
          (pp_pred 2) a (pp_pred 1) b
    | Piff (a, b) ->
      Format.fprintf fmt (protect (pri > 1) "@[%a <=>@, %a@]")
          (pp_pred 2) a (pp_pred 1) b
    | Pand (a, b) ->
        let ls, p = get_eq_pred p in
        begin match ls, p with
        | _, None -> 
            Format.fprintf fmt "={%a}" 
              (pp_list ~sep:"," (fun fmt -> Format.fprintf fmt "%s")) ls
        | [], Some _ ->
            Format.fprintf fmt (protect (pri > 3) "@[%a &&@, %a@]")
              (pp_pred 4) a (pp_pred 3) b
        | _, Some p ->
            Format.fprintf fmt (protect (pri > 3) "@[={%a} && %a@]")
              (pp_list ~sep:"," (fun fmt -> Format.fprintf fmt "%s")) ls
              (pp_pred 3) p
        end
    | Por (a, b) ->
      Format.fprintf fmt (protect (pri > 2) "@[%a ||@, %a@]")
          (pp_pred 3) a (pp_pred 2) b
    | Pnot(Papp(p,[e1;e2])) when is_eq_pred p -> 
        Format.fprintf fmt (protect (pri > 4) "%a <>@, %a")
          (pp_term 5) e1 (pp_term 6) e2
    | Pnot a -> 
        Format.fprintf fmt (protect (pri > 4) "!%a") (pp_pred 4) a
    | Pif (_, a, b, c) ->
      Format.fprintf fmt 
          (protect (pri > 0) 
             "if %a then@ @[<hov 2> %a@ @]@ else@ @[<hov 2>%a@ @]")
        (pp_term 0) a (pp_pred 0) b (pp_pred 0) c
    | Pforall _ ->
        let lv, _, p = decompose_forall p in
        Format.fprintf fmt (protect (pri > 1) 
                              "@[<hov 2>forall (%a),@,@[<hov 2>%a@]@]")

          pp_lvar_decls lv (pp_pred 0) p 
    | Pexists _ ->
        let lv, _, p = decompose_exists p in
        Format.fprintf fmt (protect (pri > 1) 
                              "@[<hov 2>exists (%a),@,@[<hov 2>%a@]@]")
          pp_lvar_decls lv (pp_pred 0) p 
    | Plet ([x],v,p) ->
        Format.fprintf fmt "@[<hov 2>(let %a =@[<hov 2>@ %a@ in@]@ %a)@]"
          pp_lvar x (pp_term 4) v (pp_pred 0) p
    | Plet (xs,v,p) ->
        Format.fprintf fmt (protect (pri > 0) 
                              "@[<hov 2>let %a =@[<hov 2>@ %a@ in@]@ %a@]")
          (EcUtil.pp_list ~sep:"," pp_lvar) xs 
          (pp_term 4) v (pp_pred 0) p
    | Pterm t -> (pp_term 4) fmt t

let pp_pred fmt p = 
  pp_pred 0 fmt p;
  reset_names ()

(* ------------------------------------------------------------------------ *)
(** {2 Visit/fold} *)

let rec fold_exp_in_pred do_var_qq do_exp acc p =
  let fold = fold_exp_in_pred do_var_qq do_exp in
  match p with
    | Ptrue | Pfalse  -> acc
    | Pif (_,t,p1,p2) ->
      let acc = do_exp acc t in
      let acc = fold acc p1 in
      let acc = fold acc p2 in
      acc
    | Pnot p -> fold acc p
    | Pforall (v,_,p') | Pexists (v,_,p') -> do_var_qq v (fold acc p')
    | Plet (x,e,p) -> 
        List.fold_right do_var_qq x (fold (do_exp acc e) p)
    | Pimplies (p1,p2) | Pand (p1,p2) | Por (p1,p2) | Piff (p1,p2) ->
      fold (fold acc p1) p2
    | Papp (_n,t) -> List.fold_left do_exp acc t
    | Pterm t -> do_exp acc t

let rec fold_var_in_var_exp do_var_qq do_var acc exp =
  let frec = fold_var_in_var_exp do_var_qq do_var in
  match exp with
    | Ast.Ecnst _ -> acc
    | Ast.Ebase v -> do_var acc v
    | Ast.Ernd _ -> assert false
    | Ast.Eapp (_n,tl) ->  List.fold_left frec acc tl
    | Ast.Eif (t1,t2,t3) -> frec (frec (frec acc t1) t2) t3
    | Ast.Epair l ->  List.fold_left frec acc l
    | Ast.Elet(xs,t1,t2) -> 
        List.fold_right do_var_qq xs (frec (frec acc t1) t2)

let nb_var_in_pred v p =
  let nb_occ = ref 0 in
  let do_var () var = if eq_lvar v var then nb_occ := !nb_occ + 1 in
  let do_var_qq _ acc = acc in
  let rec do_exp () e = fold_var_in_var_exp do_var_qq do_var () e in
  let _ = fold_exp_in_pred do_var_qq do_exp () p in
  !nb_occ

let eq_term t1 t2 =
  EcTerm.g_eq_exp eq_lvar eq_lvar t1 t2

let rec eq_pred p1 p2 =
  p1 == p2 || 
  match p1, p2 with
    | Ptrue, Ptrue -> true
    | Pfalse, Pfalse -> false
    | Pnot p1, Pnot p2 -> eq_pred p1 p2
    | Pand(p11,p12), Pand(p21,p22)
    | Por(p11,p12),Por(p21,p22)
    | Pimplies (p11,p12),Pimplies(p21,p22)
    | Piff(p11,p12),Piff(p21,p22) ->
      eq_pred p11 p21 && eq_pred p12 p22
    | Pif(_,e1,p11,p12), Pif(_,e2,p21,p22) ->
      eq_term e1 e2 && eq_pred p11 p21 && eq_pred p12 p22
    | Pforall(v1, _, p1), Pforall(v2,_,p2)
    | Pexists (v1, _, p1), Pexists(v2,_,p2) ->
      eq_lvar v1 v2 && eq_pred p1 p2
    | Plet(x1,e1,p1), Plet(x2,e2,p2) ->
        List.length x1 = List.length x2 &&
        List.for_all2 eq_lvar x1 x2 && eq_term e1 e2 && eq_pred p1 p2
    | Papp(pr1,args1), Papp(pr2,args2) ->
        Why3.Term.ls_equal (lsymbol pr1) (lsymbol pr2) &&
        List.length args1 = List.length args2 &&
        List.for_all2 eq_term args1 args2
    | Pterm t1, Pterm t2 -> eq_term t1 t2
    | _, _ -> false


(* ------------------------------------------------------------------------ *)
(** {2 Smart Constructors} *)

let pand p1 p2 =
  match p1, p2 with
    | Pfalse, _ | _, Pfalse -> Pfalse
    | Ptrue, p2 -> p2
    | p1, Ptrue -> p1
    | p1, p2 -> Pand (p1, p2)

let pands l = List.fold_right pand l Ptrue

let rec pimplies p1 p2 = match p1, p2 with
  | Ptrue, p2 -> p2
  | Pfalse, _ -> Ptrue
  | _, Ptrue -> Ptrue
  | p1, p2 when eq_pred p1 p2 -> Ptrue
  | Pand (p1, p2), p -> pimplies p1 (pimplies p2 p)
  | _, _ -> Pimplies (p1, p2)

let pnot = function
  | Ptrue -> Pfalse
  | Pfalse -> Ptrue
  | Pnot p -> p
  | p -> Pnot p

let por p1 p2 = match p1, p2 with
  | Ptrue, _ | _,Ptrue -> Ptrue
  | Pfalse,p |p,Pfalse -> p
  | p,p' -> Por (p,p')

let pxor p1 p2 = match p1, p2 with
  | Ptrue, Ptrue -> Pfalse
  | Ptrue,_ | _,Ptrue -> Ptrue
  | Pfalse, p | p, Pfalse -> p
  | p,p' -> Pnot(Piff(p,p'))

let pors l p = List.fold_right por l p

let piff p p' = Piff (p,p')

let pforallt x t p =
  match p with
    | Ptrue | Pfalse -> p
    | _ ->
      assert_bug (x.lv_id <> UID.empty_lvar)
        "Shouldn't quantify over program variable %a" pp_lvar x;
      Pforall(x,t, p)

let pforall x p = pforallt x [] p

let pexistst x t p =
  match p with
    | Ptrue | Pfalse -> p
    | _ -> Pexists(x, t, p)

let pexists x p = pexistst x [] p


(* TODO move this in ecUtil duplication with global *)
let builtins_pos n = ("<builtins>", (0, n, 0), (0, n, 0))

let pred_eq =
  let ta = Ast.Tvar (EcTerm.mk_tvar "'a" (builtins_pos 20)) in 
  { p_name = "=";
    p_type = [ta;ta];
    p_def = None;
    p_why3 = WP_native Why3.Term.ps_equ;
    p_opaque = true
  }

let pred_le_int =
  { p_name = "<=";
    p_type = [Ast.Tint;Ast.Tint];
    p_def = None;
    p_why3 = WP_native EcWhy3.ps_le_int;
    p_opaque = true;
  }

let pred_lt_int =
  { p_name = "<";
    p_type = [Ast.Tint;Ast.Tint];
    p_def = None;
    p_why3 = WP_native EcWhy3.ps_lt_int;
    p_opaque = true;
  }

let pred_le_real =
  { p_name = "<=";
    p_type = [Ast.Treal;Ast.Treal];
    p_def = None;
    p_why3 = WP_native EcWhy3.ps_le_real;
    p_opaque = true;
  }
 
let pred_lt_real =
  { p_name = "<";
    p_type = [Ast.Treal;Ast.Treal];
    p_def = None;
    p_why3 = WP_native EcWhy3.ps_lt_real;
    p_opaque = true;
  }
      
let ple_int t1 t2 = Papp(pred_le_int,[t1;t2])

let plt_int t1 t2 = Papp(pred_lt_int,[t1;t2])

let ple_real t1 t2 = Papp(pred_le_real,[t1;t2])

let plt_real t1 t2 = Papp(pred_lt_real,[t1;t2])

let check_bool t e =
  Format.fprintf Format.str_formatter "expression %a cannot be translated into a predicate" (pp_term 0) e;
  let msg = Format.flush_str_formatter () in
  Unification.raise_unify_type t Ast.Tbool dummy_pos msg

let rec pred_of_term e =
   let p = match e with
    | Ast.Ecnst (Ast.Ebool true) -> Ptrue
    | Ast.Ecnst (Ast.Ebool false) -> Pfalse
    | Ast.Ecnst (Ast.Ecst (c,_)) -> check_bool c.Ast.c_type e; Pterm e
    | Ast.Ecnst (Ast.Eint _) -> assert false
    | Ast.Ebase v -> check_bool (lv_type v) e; Pterm e
    | Ast.Ernd _ -> bug "Fol.pred_of_term: random expression"
    | Ast.Epair _ -> assert false
    | Ast.Eapp (op,args) ->
      let pred_of_args = List.map pred_of_term in
      let pred_of_args1 args =
        let args = pred_of_args args in
        List.nth args 0 in
      let pred_of_args2 args =
        let args = pred_of_args args in
        List.nth args 0, List.nth args 1 in
      begin match EcTerm.op_native op with
        | Some Ast.AND -> let p1,p2 = pred_of_args2 args in pand p1 p2
        | Some Ast.OR ->  let p1,p2 = pred_of_args2 args in por p1 p2
        | Some Ast.IMPL -> let p1,p2 = pred_of_args2 args in pimplies p1 p2
        | Some Ast.XOR -> let p1,p2 = pred_of_args2 args in pxor p1 p2
        | Some Ast.NOT -> pnot (pred_of_args1 args)
        | Some Ast.EQ ->
            let t1 = (List.nth args 0) in
            let t2 = (List.nth args 1) in
            peq t1 t2
        | Some Ast.INT_LE ->
          let t1 = (List.nth args 0) in
          let t2 = (List.nth args 1) in
          ple_int t1 t2
        | Some Ast.INT_LT ->
          let t1 = (List.nth args 0) in
          let t2 = (List.nth args 1) in
          plt_int t1 t2
        | Some Ast.REAL_LE ->
          let t1 = (List.nth args 0) in
          let t2 = (List.nth args 1) in
          ple_real t1 t2
        | Some Ast.REAL_LT ->
          let t1 = (List.nth args 0) in
          let t2 = (List.nth args 1) in
          plt_real t1 t2
        | _ ->
          let _, op_body, _ = op in
          let _,(_,t_res_op) = EcTerm.instanciate_op op_body EcUtil.dummy_pos in
          check_bool t_res_op e;
          Pterm e
      end
    | Ast.Elet(xs,e1,e2) -> Plet(xs,e1,pred_of_term e2)
    | Ast.Eif(b,e1,e2) ->
      pif ~split_info:false b (pred_of_term e1) (pred_of_term e2)
  in p

and peq t1 t2 =
  if eq_term t1 t2 then Ptrue else 
  match t1, t2 with
  | _, Ast.Ecnst (Ast.Ebool b) -> 
      if b then pred_of_term t1 
      else pnot (pred_of_term t1)
  | Ast.Ecnst (Ast.Ebool b), _ ->
      if b then pred_of_term t2 
      else pnot (pred_of_term t2)
  | _, _ -> Papp(pred_eq,[t1;t2])


and pif ?(split_info=false) e p1 p2 = match p1, p2 with
  | Ptrue, p2 ->
    let nep = pnot (pred_of_term e) in
    pimplies nep p2
  | p1, Ptrue ->
    let ep = pred_of_term e in
    pimplies ep p1
  | p1, p2 ->
    if eq_pred p1 p2 then p1
    else Pif (split_info,e,p1,p2)



let pred_of_exp side e = pred_of_term (term_of_exp side e)
let peq_exp e1 e2 = peq (term_of_exp FVleft e1) (term_of_exp FVright e2)
let peq_vars v1 v2 = peq_exp (Ast.Ebase v1) (Ast.Ebase v2)
let peq_lvars lv1 lv2 = pands (List.map2 peq_vars lv1 lv2)

let papp (p, args) = 
  if is_eq_pred p then
    match args with
    | [t1;t2] -> peq t1 t2
    | _ -> assert false
  else Papp (p,args)

(* ------------------------------------------------------------------------ *)
(** {2 Substitution} *)

(** apply [do_exp] on each sub expression of the predicate.
    * [quantif_do_exp] is called to change [do_exp] if needed
    * when we go under a quantification.
    * TODOopt: avoid building new terms when nothing changed.
    * *)
let rec change_exp_in_pred (do_exp : term -> term)
    (quantif_do_exp: (term -> term) -> lvar -> (term -> term))
    (p: pred) : pred =
  let subst_pred = change_exp_in_pred do_exp quantif_do_exp in
  match p with
    | Ptrue -> Ptrue
    | Pfalse -> Pfalse
    | Pnot p -> pnot (subst_pred p)
    | Pand (p1,p2) -> pand (subst_pred p1) (subst_pred p2)
    | Por (p1,p2) -> por (subst_pred p1) (subst_pred p2)
    | Pimplies (p1,p2) -> pimplies (subst_pred p1) (subst_pred p2)
    | Piff (p1,p2) -> piff (subst_pred p1) (subst_pred p2)
    | Pif (split_info,t,p1,p2) ->
      pif ~split_info (do_exp t) (subst_pred p1) (subst_pred p2)
    | Papp (n,t) -> papp (n,List.map do_exp t)
    | Pforall (v,l,p') ->
      let f = quantif_do_exp do_exp v in
      Pforall (v,change_exp_in_triggers f quantif_do_exp l, 
               change_exp_in_pred f quantif_do_exp p')
    | Pexists (v, l, p') ->
      let f = quantif_do_exp do_exp v in
      Pexists (v,change_exp_in_triggers f quantif_do_exp l, 
               change_exp_in_pred f quantif_do_exp p')
    | Plet (x,v,p) ->
      let f = List.fold_right (fun x do_e -> quantif_do_exp do_e x) x do_exp  in
      Plet (x, do_exp v,change_exp_in_pred f quantif_do_exp p)
    | Pterm t -> pred_of_term (do_exp t)
and change_exp_in_triggers do_exp quantif_do_exp l =
  let change_exp = function
    | Tterm t -> Tterm (do_exp t)
    | Tpred p -> Tpred (change_exp_in_pred do_exp quantif_do_exp p) in
  List.map (fun l -> List.map change_exp l) l
    

let rec change_in_var_exp do_var exp =
  let frec = change_in_var_exp do_var in
  match exp with
    | Ast.Ecnst _ -> exp
    | Ast.Ebase v -> (match do_var v with Some e -> e | None -> exp)
    | Ast.Ernd _ -> raise (EcError "Computing change_in_var_exp over a random expression.\n Using a probabilistic operator?")
    (* assert false *)
    | Ast.Eapp (n,tl) -> Ast.Eapp(n, List.map frec tl)
    | Ast.Eif (t1,t2,t3) -> Ast.Eif(frec t1, frec t2, frec t3)
    | Ast.Epair l -> Ast.Epair (List.map frec l)
    | Ast.Elet(xs,e1,e2) ->
        Ast.Elet(xs,frec e1, frec e2)

let no_quantif_do_exp do_exp qqvar =
  let var_term = Ast.Ebase qqvar in
  match do_exp var_term with
    | Ast.Ebase v when eq_lvar qqvar v -> do_exp
    | _ -> assert false

(** Use previous functions to process all the variables [Tvar v] in [exp]. *)
let change_vars_in_var_exp var_subst exp =
  change_in_var_exp var_subst exp

let subst_var_in_term x exp t =
  let var_subst v = if eq_lvar v x then Some exp else None in
  change_vars_in_var_exp var_subst t

(* let subst_vars_in_exp *)

(** Similar to [change_vars_in_exp] but on predicates.
    * Notice that we assume (and check) that [var_subst] only works on free
    * variables (and that they are different from bounded ones).
*)
let subst_vars_in_pred var_subst p =
  let do_exp = change_vars_in_var_exp var_subst in
  change_exp_in_pred do_exp no_quantif_do_exp p

let subst_vars_in_triggers var_subst p =
  let do_exp = change_vars_in_var_exp var_subst in
  change_exp_in_triggers do_exp no_quantif_do_exp p


(** Specialized version of [subst_vars_in_pred] to substitute one variable [v]
    * by and expression [exp] in a predicate [p]. *)
let subst_in_pred x exp p =
  let var_subst v = if eq_lvar v x then Some exp else None in
  subst_vars_in_pred var_subst p

let set_left p =
  let var_subst v =
    match var_of_lvar v with
      | None -> None
      | Some(v,side) ->
        if side = FVleft then assert false;
        Some (Ast.Ebase (lvar_of_var v FVleft)) in
  subst_vars_in_pred var_subst p

(** Build a predicate equivalent to [let v = e in p] but may use the
    * substitution in some simple cases (like substitute a variable by another
    * variable for instance).
    * [fresh] is only meaningfull when the [let] is actually built: it tells if we
    * have to build a new variable for [v].
*)

let rec let_pred ?(fresh=true) v e p =
  if p = Ptrue || p = Pfalse then p
  else match e with
    | Ast.Ecnst _ | Ast.Ebase _ when List.length v = 1 -> 
        subst_in_pred (List.nth v 0) e p
    | Ast.Epair (es:term list) when List.length es = List.length v ->
      List.fold_left (fun p (v,e) -> let_pred ~fresh [v] e p) p (List.combine v es)
    | _ ->
        if List.length v = 1 && nb_var_in_pred (List.nth v 0) p <= 1 then
          subst_in_pred (List.nth v 0) e p
        else
          let v, p =
            if fresh then
              let v' = List.map fresh_lvar v in
              let assoc = List.map2 (fun x x' -> x, Ast.Ebase x') v v' in
              let vsubst x = 
                try Some (snd (List.find (fun (y,_) -> eq_lvar x y) assoc))
                with Not_found -> None in
              let p = subst_vars_in_pred vsubst p in
              (v', p)
            else (v, p) in
          Plet (v, e, p)

let let_pred_opt ?(fresh=true) lv e p =
  match e with
    | Some e -> let_pred ~fresh [lv] e p
    | None ->
      let nb_occ = nb_var_in_pred lv p in
      if nb_occ = 0 then p
      else bug "try to substitute varaible %a by None !" pp_lvar lv

(* ------------------------------------------------------------------------ *)
(** {2 Quantification} *)

let fresh_var_in_pred v p =
  let v' = fresh_lvar v in
  let p = subst_in_pred v (Ast.Ebase v') p in
  v', p

let forall_pred_with_var ?(fresh=true) v (p: pred) : (lvar * pred) =
  (* if nb_var_in_pred v p > 0 then *)
  (* TODOopt : do only one visit *)
  let v, p = if fresh then fresh_var_in_pred v p else v, p in
  v, pforall v p
(* else p *)

let forall_pred ?(fresh=true) v (p: pred) : pred =
  snd (forall_pred_with_var ~fresh v p)

let forall_trigger lv t p =
  let trigger (e,t) =
    if EcTerm.is_type_bool t then Tpred (pred_of_term e)
    else Tterm e in

  let t = List.map (fun l -> List.map trigger l) t in
  match List.rev lv with
  | [] -> assert false
  | v::rv ->
      let p = pforallt v t p in
      List.fold_left (fun p v -> pforall v p) p rv

let exists_trigger lv t p =
  let trigger (e,t) =
    if EcTerm.is_type_bool t then Tterm e
    else Tpred (pred_of_term e) in
  let t = List.map (fun l -> List.map trigger l) t in
  match List.rev lv with
  | [] -> assert false
  | v::rv ->
      let p = pexistst v t p in
      List.fold_left (fun p v -> pexists v p) p rv

let exists_pred ?(fresh=true) v (p: pred) : pred =
  (* if nb_var_in_pred v p > 0 then *)
    (* TODOopt : do only one visit *)
    let v, p = if fresh then fresh_var_in_pred v p else v, p in
    pexists v p
  (* else p *)

let free_pred_vars p =
  let do_var_qq v acc = FVset.remove v acc in
  let do_exp acc e = fold_var_in_var_exp do_var_qq 
    (fun acc v -> FVset.add v acc) acc e in
  fold_exp_in_pred do_var_qq do_exp FVset.empty p

let free_term_vars t = 
  let do_var_qq v acc = FVset.remove v acc in
  fold_var_in_var_exp do_var_qq 
    (fun acc v -> FVset.add v acc) FVset.empty t

let pclos p =
  FVset.fold (forall_pred ~fresh:true) (free_pred_vars p) p

let fv_pred p =
  let add x (fv1, fv2 as fv) =
    match x.lv_base with
      | FVpgVar (x,side) ->
        if side = FVleft then
          EcTerm.Vset.add x fv1, fv2
        else fv1,EcTerm.Vset.add x fv2
      | _ -> fv in
  FVset.fold add (free_pred_vars p) (EcTerm.Vset.empty, EcTerm.Vset.empty)

let depend s1 s2 p =
  let s1', s2' = fv_pred p in
  not (EcTerm.Vset.is_empty (EcTerm.Vset.inter s1 s1')) ||
    not (EcTerm.Vset.is_empty (EcTerm.Vset.inter s2 s2'))

(* ------------------------------------------------------------------------ *)
(** {2 Destructors } *)

(* let rec remove_if p = *)
(*   match p with *)
(*     | Ptrue | Pfalse | Por _  | Papp _ -> p *)
(*     | Pnot p -> pnot (remove_if p) *)
(*     | Pand(p1,p2) -> pand (remove_if p1) (remove_if p2) *)
(*     | Pimplies(p1,p2) -> *)
(*       pimplies (remove_if p1) ( remove_if p2) *)
(*     | Piff(p1,p2) -> piff (remove_if p1) ( remove_if p2) *)
(*     | Pif(_,e,p1,p2) -> *)
(*       let ep = pred_of_term e in *)
(*       pand (pimplies(ep) (remove_if p1)) (pimplies (pnot ep) ( remove_if p2)) *)
(*     | Pforall(x, t, p) -> pforallt x t (remove_if p) *)
(*     | Pexists(x,t,p) -> pexistst x t (remove_if p) *)
(*     | Plet(x,t,p) -> let_pred ~fresh:false x t (remove_if p) *)
(*     | Pterm t -> Pterm t *)

let rec split_pred p =
  match p with
    | Ptrue | Pfalse | Por _ | Pexists _ | Papp _ | Pnot _ | Pterm _ -> [p]
    | Pand(p1,p2) -> split_pred p1 @ split_pred p2
    | Pimplies(p1,p2) -> List.map (fun p2 -> pimplies(p1) (p2)) (split_pred p2)
    | Piff(p1,p2) -> split_pred (pand (pimplies(p1) ( p2)) (pimplies(p2) ( p1)))
    | Pif(_,e,p1,p2) ->
      let ep = pred_of_term e in
      split_pred (pand (pimplies(ep) (p1)) (pimplies (pnot ep) ( p2)))
    | Pforall(x,t,p) -> List.map (pforallt x t) (split_pred p)
    | Plet(x,t,p) -> List.map (let_pred ~fresh:false x t) (split_pred p)

let rec remove_dep s1 s2 p =
  if EcTerm.Vset.is_empty s1 && EcTerm.Vset.is_empty s2 then p
  else
    let rec aux p =
      match p with
        | Ptrue | Pfalse -> p
        | Pand(p1,p2) -> pand (aux p1) (aux p2)
        | Pimplies(p1,p2) ->
          if depend s1 s2 p1 then Ptrue
          else pimplies p1 (aux p2)
        | Pforall(x,t,p) -> pforallt x t (aux p)
        | Pif(b,t,p1,p2) ->
          pif ~split_info:b t (aux p1) (aux p2)
        | _ -> if depend s1 s2 p then Ptrue else p in
    aux p

(* let split_pred p = split_pred (remove_if p) *)
(* ------------------------------------------------------------------------ *)

let mkeq_params f1 f2 =
  try
    List.iter2 (fun v1 v2 -> Unification.unify_type v1.Ast.v_type v2.Ast.v_type)
      f1.Ast.f_param f2.Ast.f_param;
    peq_lvars f1.Ast.f_param f2.Ast.f_param
  with _ -> user_error "The two functions %a %a should have the same type parameters" PpAst.pp_fct_name f1 PpAst.pp_fct_name f2

let mkeq_result f1 f2 =
  try
    let v1, v2 = f1.Ast.f_res, f2.Ast.f_res in
    Unification.unify_type v1.Ast.v_type v2.Ast.v_type;
    if EcTerm.is_defined_fct f1 && EcTerm.is_defined_fct f2 &&
      (EcTerm.fct_def f1).Ast.f_return = None then Ptrue
    else peq_vars v1 v2
  with _ -> user_error "The two functions should have the same result type"


(* ------------------------------------------------------------------------ *)



let string_of_side = function
  | FVleft -> "_left"
  | FVright -> "_right"

let string_of_lv = function
  | FVpgVar(v,side) -> v.Ast.v_name ^ (string_of_side side)
  | FVlogic(s,_) -> s

let preid_of_lv lv = Why3.Ident.id_fresh (string_of_lv lv)
   
let init_why3_lvar tva va lv =
  let tva, t = EcTerm.add_why3_type tva (lv_type lv) in
  let v = Why3.Term.create_vsymbol (preid_of_lv lv.lv_base) t in
  tva, (lv, Why3.Term.t_var v)::va, v

let init_why3_lvars tva va lvs =
  List.fold_right (fun lv (tva,va,wls) ->
    let (tva,va,v) = init_why3_lvar tva va lv in
    (tva,va,v::wls)) lvs (tva,va,[])

let term_of_lvar env v =
  try 
    snd (List.find (fun (v',_) -> eq_lvar v v') env)
  with Not_found -> bug "Fol.term_of_lvar"

let term_of_term, form_of_term =
  EcTerm.g_term_of_exp (pp_term 0) init_why3_lvar term_of_lvar 

let rec form_of_fol tva va p =
    match p with
    | Ptrue -> Why3.Term.t_true
    | Pfalse -> Why3.Term.t_false
    | Pnot p -> Why3.Term.t_not (form_of_fol tva va p)
    | Pand(p1,p2) -> 
        Why3.Term.t_and (form_of_fol tva va p1) (form_of_fol tva va p2) 
    | Por(p1,p2) -> 
        Why3.Term.t_or (form_of_fol tva va p1) (form_of_fol tva va p2) 
    | Pimplies(p1,p2) -> 
        Why3.Term.t_implies (form_of_fol tva va p1) (form_of_fol tva va p2) 
    | Piff(p1,p2) ->
        Why3.Term.t_iff (form_of_fol tva va p1) (form_of_fol tva va p2) 
    | Pif(_,t,p1,p2) ->
        Why3.Term.t_if (form_of_term tva va t)
          (form_of_fol tva va p1) (form_of_fol tva va p2) 
    | Pforall _ ->
        let lvs, t, p = decompose_forall p in
        let tva, va, v = init_why3_lvars tva va lvs in
        let t = triggers tva va t in
        let p = form_of_fol tva va p in
        Why3.Term.t_forall_close v t p
    | Pexists _ ->
        let lvs, t, p = decompose_exists p in
        let tva, va, v = init_why3_lvars tva va lvs in
        Why3.Term.t_exists_close v (triggers tva va t) (form_of_fol tva va p)
    | Plet(lvs,t,p) ->
        begin match lvs with
        | [] -> form_of_fol tva va p
        | [lv] ->
            let wt = term_of_term tva va t in
            let tva, va, v = init_why3_lvar tva va lv in
            Why3.Term.t_let_close v wt (form_of_fol tva va p)
        | _ ->
            let wt = term_of_term tva va t in
            let tva, va, wl = init_why3_lvars tva va lvs in
            let pattern = 
              Why3.Term.pat_app 
                (Why3.Term.fs_tuple (List.length lvs))
                (List.map Why3.Term.pat_var wl)
                (EcWhy3.ty_tuple (List.map (fun v -> v.Why3.Term.vs_ty) wl)) 
            in
            let br = Why3.Term.t_close_branch pattern (form_of_fol tva va p) in
            Why3.Term.t_case wt [br]
        end
    | Papp(pr,args) -> 
        let of_term = term_of_term tva va in
        (try 
          Why3.Term.ps_app (lsymbol pr) (List.map of_term args)
        with Why3.Ty.TypeMismatch(t1,t2) ->
          bug "form_of_pred : TypeMismatch %a and %a in %a"
            Why3.Pretty.print_ty t1 Why3.Pretty.print_ty t2 pp_pred p)
    | Pterm t -> form_of_term tva va t
and triggers tva va t =
  let trigger = function
    | Tterm t -> term_of_term tva va t
    | Tpred p -> form_of_fol tva va p in
  List.map (fun l -> List.map trigger l) t
  
let mk_why3_pred name params body =
  let tva, va, wl = init_why3_lvars [] [] params in
  let body = form_of_fol tva va body in
  let tparams = List.map (fun v -> v.Why3.Term.vs_ty) wl in
  let preid = Why3.Ident.id_fresh name in
  let ls = Why3.Term.create_psymbol preid tparams in
  Why3.Decl.make_ls_defn ls wl body

let mk_why3_apred name dom =
  let _tva, wtys =
    List.fold_right
      (fun ty (tva, wtys) ->
         let (tva, wty) = EcTerm.add_why3_type tva ty in
           (tva, wty :: wtys))
      dom ([], []) in
  let predid = Why3.Ident.id_fresh name in
    (Why3.Term.create_psymbol predid wtys, None)

let mk_predicate name (params, body) =
  { p_name = name;
    p_type = List.map lv_type params;
    p_def = Some (params,body);
    p_why3 = WP_locale (mk_why3_pred name params body);
    p_opaque = false }

let mk_apredicate name dom =
  { p_name   = name;
    p_type   = dom;
    p_def    = None;
    p_why3   = WP_locale (mk_why3_apred name dom);
    p_opaque = true }

let predicate_name pr = pr.p_name

let predicate_type pr =
  let fv = EcTerm.fv_types pr.p_type in
  let subst = 
    List.map (fun tv -> tv, 
      Ast.Tvar(EcTerm.mk_tvar tv.Ast.tv_name tv.Ast.tv_pos)) fv in
  List.map (EcTerm.subst_tvar subst) pr.p_type

let set_opacity b pr = pr.p_opaque <- b
let opacity pr = pr.p_opaque

let logic_decl pr = 
  match pr.p_why3 with
  | WP_native _ -> bug "Fol.logic_decl"
  | WP_locale ld -> if pr.p_opaque then fst ld, None else ld

let unfold_predicate on_pred =
  let rec aux p = 
    match p with 
    | Ptrue | Pfalse | Pterm _ -> p
    | Pnot p -> Pnot (aux p)
    | Pand (p1, p2) -> Pand (aux p1, aux p2)
    | Por (p1, p2) -> Por (aux p1, aux p2)
    | Pimplies (p1, p2) -> Pimplies (aux p1, aux p2)
    | Piff (p1,p2) -> Piff(aux p1, aux p2)
    | Pif(b,t,p1,p2) -> Pif(b,t,aux p1, aux p2)
    | Pforall(x,t,p) -> Pforall(x,t,aux p)
    | Pexists(x,t,p) -> Pexists(x,t,aux p)
    | Plet(x,t,p) -> Plet(x,t,aux p)
    | Papp(pr,args) ->
        if on_pred pr then 
          match pr.p_def with
          | Some (decls,def) ->
              let assoc = List.combine decls args in
              let var_subst v =
                try Some (snd (List.find (fun p -> eq_lvar (fst p) v) assoc))
                with _ -> None in
              subst_vars_in_pred var_subst def
          | None -> user_error "the predicate %s is axiomatic" pr.p_name 
        else p in
  aux

let unfold_pred l =
  let on_pred = 
    if l = [] then fun pr -> pr.p_def <> None
    else fun pr -> List.mem pr.p_name l in
  unfold_predicate on_pred

let pp_predicate fmt pr = 
  match pr.p_def with
  | Some (params, p) when not pr.p_opaque ->
      Format.fprintf fmt "@[<hov 2>%s (%a)@ =@ @[<hov 2>%a@]@].@." pr.p_name
        pp_lvar_decls params pp_pred p
  | _ -> 
      Format.fprintf fmt "%s : %a" pr.p_name 
        (pp_list ~sep:"," PpAst.pp_type_exp) pr.p_type 


(** Building axiom *)

type why3_axiom = Why3.Decl.prsymbol * Why3.Term.term

let mk_axiom name p =
  let preid = Why3.Ident.id_fresh name in 
  let pr = Why3.Decl.create_prsymbol preid in
  pr, form_of_fol [] [] p

(* ------------------------------------------------------------------------ *)



type pop_spec = 
    (lvar list * Ast.var list) *
      (lvar * Ast.exp * Ast.exp option) *
      (lvar * Ast.exp * Ast.exp option) *
      (pred * pred * (term * term) option)

type pop_aspec =
    (lvar list * Ast.type_exp list) *
      (lvar * Ast.oper * lvar list) *
      (pred * pred)







(** Simplification of fol *)

let rec remove_let s p = 
  match p with
  | Ptrue | Pfalse -> p
  | Pnot p -> pnot (remove_let s p)
  | Pand(p1,p2) -> pand (remove_let s p1) (remove_let s p2)
  | Por(p1,p2) -> por (remove_let s p1) (remove_let s p2)
  | Pimplies(p1,p2) -> pimplies (remove_let s p1) (remove_let s p2)
  | Piff(p1,p2) -> piff (remove_let s p1) (remove_let s p2)
  | Pif(b,t,p1,p2) -> 
      pif ~split_info:b (change_vars_in_var_exp s t) (remove_let s p1) (remove_let s p2)
  | Pforall(l,t,p) -> pforallt l (subst_vars_in_triggers s t) (remove_let s p)
  | Pexists(l,t,p) -> pexistst l (subst_vars_in_triggers s t) (remove_let s p)
  | Papp(p,args) -> papp (p, List.map (change_vars_in_var_exp s) args)
  | Pterm t -> pred_of_term (change_vars_in_var_exp s t)
  | Plet(ls,t,p) ->
      let t = change_vars_in_var_exp s t in
      match ls, t with
      | [x], _ -> remove_let (fun y -> if eq_lvar x y then Some t else s y) p
      | _, Ast.Epair lt ->
          let s = 
            let ass = List.combine ls lt in
            fun y -> try Some (snd (List.find (fun (x,_) -> eq_lvar x y) ass)) with _ -> s y in
          remove_let s p
      | _, _ -> let_pred ~fresh:false ls t (remove_let s p)

let remove_let = remove_let (fun _ -> None)

let find_same p = 
  let is_pg_var lv = 
    match lv.lv_base with
    | FVpgVar _ -> lv.lv_id = UID.empty_lvar 
    | _ -> false in
  let side v = 
    match v.lv_base with
    | FVpgVar (_,side) -> side
    | _ -> assert false in
  let var v = 
    match v.lv_base with
    | FVpgVar (v,_) -> v
    | _ -> assert false in
  let add acc v1 v2 = 
    let in_a = ref false in
    let check (v1', v2') = 
      if EcTerm.eq_var v1 v1' then
        if EcTerm.eq_var v2 v2' then in_a := true
        else (
          (*verbose "find_same: conflict %a %a %a" PpAst.pp_var v1
            PpAst.pp_var v2 PpAst.pp_var v2'; *)
          raise Not_found) in
    List.iter check acc;
    if !in_a then acc else (v1,v2)::acc in
  let rec aux1 acc a1 a2 = 
    match a1, a2 with
    | Ast.Ebase v1, Ast.Ebase v2 when is_pg_var v1 && is_pg_var v2 ->
        begin match side v1, side v2 with
        | FVleft, FVright -> add acc (var v1) (var v2) 
        | FVright, FVleft -> add acc (var v2) (var v1) 
        | _, _ -> acc
        end
    | Ast.Eapp(op1,args1), Ast.Eapp(op2,args2) when EcTerm.eq_op op1 op2 ->
        List.fold_left2 aux1 acc args1 args2
    | Ast.Elet(_,a11,a12), Ast.Elet(_,a21,a22) -> 
        aux1 (aux1 acc a11 a21) a12 a22
    | Ast.Epair(args1), Ast.Epair(args2) when List.length args1 = List.length args2 ->
        List.fold_left2 aux1 acc args1 args2
    | _ -> acc in
  let rec aux acc p =
    match p with
    | Papp(p, [a1;a2]) when is_eq_pred p -> 
(*        Format.printf "start aux1 with %a and %a\n" (pp_term 0) a1 (pp_term 0) a2; *) 
        aux1 acc a1 a2
(*    | Pterm(Ast.Eapp(op, [a1;a2])) when EcTerm.is_op Ast.EQ op ->
        aux1 acc a1 a2 *)
    | Ptrue | Pfalse | Piff _ | Papp _ | Pterm _ -> acc
    | Pnot p -> aux acc p
    | Pand(p1,p2) | Por(p1,p2) | Pif(_,_,p1,p2) -> aux (aux acc p1) p2
    | Pimplies(_,p) | Pforall(_,_,p) | Pexists(_,_,p) | Plet (_,_,p)-> aux acc p
  in aux [] p



let dest_forall p = 
  let rec aux lx p = 
    match p with
    | Pforall (x,[], p) -> aux (x::lx) p
    | _ -> List.rev lx, p in
  aux [] p

let is_simpl_eq l p = 
  let test v t = 
    if List.exists (eq_lvar v) l &&
      not (FVset.mem v (free_term_vars t)) then (v,t)
    else raise Not_found in
  match p with
  | Papp(p,[t1;t2]) when is_eq_pred p ->
      (match t1, t2 with
      | Ast.Ebase v1, _ -> test v1 t2
      | _, Ast.Ebase v2 ->test v2 t1
      | _, _ -> raise Not_found)
  | _ -> raise Not_found
  
let get_simpl_eq l p =
  let rec aux acc p = 
    match p with
    | Pimplies(p1,p2) ->
        (try 
          let vt = is_simpl_eq l p1 in
          vt,
          List.fold_left (fun p2 p1 -> pimplies p1 p2) p2 acc
        with _ -> aux (p1::acc) p2)
    | _ -> raise Not_found in
  aux [] p

let rec remove_v v l =
  match l with
  | [] -> assert false
  | v' :: l ->
      if eq_lvar v v' then l
      else v' :: remove_v v l

let rec remove_simpl_eq l p =
  let get =
    try Some (get_simpl_eq l p) with _ -> None in
  match get with
  | Some ((v,t), p) -> 
      remove_simpl_eq (remove_v v l) (subst_in_pred v t p)
  | None -> l, p

let simplify_equality p =
(*  verbose "simplify_equality %a" pp_pred p; *)
  let l, p = dest_forall p in
  let l, p = remove_simpl_eq l p in
  let p = List.fold_right pforall l p in
(*  verbose "simplify_equality ret %a" pp_pred p; *)
  p
  
  

