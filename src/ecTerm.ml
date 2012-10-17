(** Function on ast terms *)

open EcUtil
open Ast

let cmp_name_id (name1, id1) (name2, id2) =
  let cmp = String.compare name1 name2 in
  if cmp = 0 then compare id1 id2 else cmp

(** {2 Functions over type} *)

let eq_tdef_name td1 td2 = 
  td1.t_name = td2.t_name



let mk_tvar ?(tvar_def=Open) name pos = {
  tv_name = name;
  tv_id = UID.fresh_tvar name;
  tv_pos = pos;
  tv_def = tvar_def
}

let name_id_tvar tv = tv.tv_name, tv.tv_id

let eq_tvar tv1 tv2 = tv1.tv_name = tv2.tv_name && tv1.tv_id = tv2.tv_id

let tvar_compare tv1 tv2 = cmp_name_id (name_id_tvar tv1) (name_id_tvar tv2)

let rec is_type_bool t = 
  match t with
  | Tbool -> true
  | Tnamed {t_def = Some t } -> is_type_bool t
  | Tvar   {tv_def = Defined t} -> is_type_bool t
  | _ -> false

let rec get_tuple t = 
  match t with
  | Ttuple l -> l
  | Tnamed {t_def = Some t } -> get_tuple t
  | Tvar   {tv_def = Defined t} -> get_tuple t
  | _ -> raise Not_found

let rec get_named_type name t =
  match t with
  | Tnamed t when t.t_name = name -> t.t_poly
  | Tnamed {t_def = Some t } -> get_named_type name t
  | Tvar   {tv_def = Defined t} -> get_named_type name t
  | _ -> raise Not_found


let rec type_of_random = function
  | Rinter _ -> Tint
  | Rbool -> Tbool
  | Rbitstr c -> Tbitstring c
  | Rexcepted(r, _) -> type_of_random r
  | Rapp(op,_) -> 
    let (_,op,_) = op in snd (op.op_type)



module OrderedTvar =
struct
  type t = tvar
  let compare = tvar_compare
end

module TdefSet = Set.Make (OrderedTvar)


let rec fv_type_aux fv t =
  match t with
    | Tunit | Tbool | Tint | Treal | Tbitstring _ -> fv
    | Tvar v ->
        begin match v.tv_def with
        | Open | Closed -> TdefSet.add v fv
        | Defined def -> fv_type_aux fv def
        end
    | Ttuple l -> List.fold_left fv_type_aux fv l
    | Tnamed tdef -> 
        let fv = 
          match tdef.t_def with
          | None -> fv
          | Some d -> fv_type_aux fv d in
        List.fold_left fv_type_aux fv tdef.t_poly

let fv_types lt =
  let fv = List.fold_left fv_type_aux TdefSet.empty lt in
  TdefSet.elements fv

let fv_type t = fv_types [t]

let fv_g_fct_sig (dom,codom) = fv_types (codom :: dom)

let rec subst_tvar subst t =
  match t with
    | Tunit | Tbool | Tint | Treal | Tbitstring _ -> t
    | Ttuple l -> Ttuple (List.map (subst_tvar subst) l)
    | Tvar tv ->
      begin match tv.tv_def with
      | Open | Closed -> (try (List.assoc tv subst) with Not_found -> t)
      | Defined t -> subst_tvar subst t
      end
    | Tnamed tdef -> 
        Tnamed { tdef with
          t_poly = List.map (subst_tvar subst) tdef.t_poly;
          t_def = match tdef.t_def with 
          | None -> None
          | Some t -> Some (subst_tvar subst t) }

let subst_fct_sig subst (dom,codom) =
  let subst = List.map (fun (v1,v2) -> v1, Tvar v2) subst in
  List.map (subst_tvar subst) dom, subst_tvar subst codom

let init_why3_tv tv = 
  assert (tv.tv_def = Closed || tv.tv_def = Open);
  let preid = Why3.Ident.id_fresh tv.tv_name in
  let wtv = Why3.Ty.create_tvsymbol preid in
  (tv, wtv)

let find_why3_tvar tenv tv =
  snd (List.find (fun (tv',_) -> eq_tvar tv tv') tenv)

let eq_var v1 v2 = v1.v_name = v2.v_name && v1.v_id = v2.v_id

let op_body ((_,op,_):oper) = op

let op_name op = (op_body op).op_name

let op_native op = (op_body op).op_native

let op_why op = fst ((op_body op).op_why)

let op_ac op = snd ((op_body op).op_why)

let op_id op = (op_body op).op_id

let op_prec op = (op_body op).op_prec

let is_infix op = (op_body op).op_infix

let is_op o op = op_native op = Some o

let eq_op op1 op2 = op_name op1 = op_name op2 && op_id op1 = op_id op2

let eq_const c1 c2 = c1.c_name = c2.c_name

let rec eq_exp e1 e2 =
  match e1, e2 with
    | Ebase v1, Ebase v2 -> eq_var v1 v2
    | Ecnst c1, Ecnst c2 -> eq_cnst c1 c2
    (* C'est correct seulement si c1 c2 sont vraiment
     * des expressions constantes *)
    | Ernd r1, Ernd r2 -> eq_random r1 r2
    | Epair l1, Epair l2 ->
        (try List.for_all2 eq_exp l1 l2 with _ -> false)
    | Eif(b1,e11,e12),Eif(b2,e21,e22) ->
      eq_exp b1 b2 && eq_exp e11 e21 && eq_exp e12 e22
    | Eapp(op1,args1), Eapp(op2,args2) ->
      let eq_args args1 args2 =
        try List.for_all2 eq_exp args1 args2
        with _ -> false in
      eq_op op1 op2 && eq_args args1 args2
    | Elet(xs1,e11,e12), Elet(xs2,e21,e22) ->
        (try 
          eq_exp e11 e21 && eq_exp e12 e22 &&
          List.for_all2 eq_var xs1 xs2 
        with _ -> false)
    | _, _ -> false
and eq_cnst c1 c2 =
  match c1, c2 with
    | Ebool b1, Ebool b2 -> b1 = b2
    | Eint n1, Eint n2 -> n1 = n2
    | Ecst (c1,_), Ecst (c2,_) when eq_const c1 c2 -> true
    | Ecst ({c_def = Some e1},_), _ -> eq_exp e1 (Ecnst c2)
    | _, Ecst ({c_def = Some e2},_) -> eq_exp (Ecnst c1) e2
    | _, _ -> false
and eq_random r1 r2 =
  match r1, r2 with
    | Rinter(e11,e12), Rinter(e21,e22) -> eq_exp e11 e21 && eq_exp e12 e22
    | Rbool, Rbool -> true
    | Rbitstr e1, Rbitstr e2 -> eq_exp e1 e2
    | Rexcepted(r1',e1), Rexcepted(r2',e2) -> eq_random r1' r2' && eq_exp e1 e2
    | Rapp (op1,args1), Rapp (op2,args2) when eq_op op1 op2 ->
      List.for_all2 eq_exp args1 args2
    | _, _ -> false

(* TODO Deal with undo ??? *)

let bitstring_size = ref [] 

let find_bitstring c =
  snd (List.find (fun (c', _) -> eq_exp c c') !bitstring_size)

let decl_bitstring task = 
  List.fold_left (fun task (_,(ts,_)) ->
    Why3.Task.add_ty_decl task [(ts,Why3.Decl.Tabstract)]) task !bitstring_size

let rec mk_bs_name c =
  match c with
  | Ecnst (Eint i) -> string_of_int i 
  | Ecnst (Ecst (c,_)) -> c.c_name
  | Eapp (op,[c1;c2]) when is_op INT_ADD op ->
      mk_bs_name c1 ^"_p_"^mk_bs_name c2
  | _ -> raise Not_found

let add_bitstring c =
   try ignore (find_bitstring c); assert false
   with Not_found ->
     let bs = 
       try mk_bs_name c 
       with _ -> "nth_"^ string_of_int (List.length !bitstring_size) 
     in
     let id = Why3.Ident.id_fresh ("bitstring_"^ bs) in
     let ts = Why3.Ty.create_tysymbol id [] None in
     let ty = Why3.Ty.ty_app ts [] in
     bitstring_size := (c,(ts,ty)) :: !bitstring_size;
     bs

let rec mk_why3_type tenv t =
  match t with
    | Tunit -> EcWhy3.ty_tuple []
    | Tbool -> EcWhy3.ty_bool
    | Tint -> Why3.Ty.ty_int
    | Treal -> Why3.Ty.ty_real
    | Tbitstring c -> 
      (try snd (find_bitstring c) with _ -> assert false)
    | Ttuple l ->
      EcWhy3.ty_tuple (List.map (mk_why3_type tenv) l)
    | Tnamed tdef ->
      Why3.Ty.ty_app tdef.t_wsymbol (List.map (mk_why3_type tenv) tdef.t_poly)
    | Tvar tv ->
      match tv.tv_def with
        | Defined t -> mk_why3_type tenv t
        | _ -> 
          try Why3.Ty.ty_var (find_why3_tvar tenv tv)
          with Not_found -> assert false 

let add_why3_type tenv t =
  let fv = fv_type t in
  let tenv = 
    List.fold_left (fun tenv tv ->
      try ignore(find_why3_tvar tenv tv); tenv
      with Not_found -> init_why3_tv tv :: tenv) tenv fv in
  tenv, mk_why3_type tenv t

let mk_fsymbol why_name (tparams,tres) =
  let fv = fv_types (tres::tparams) in
  let tenv = List.map init_why3_tv fv in
  let preid = Why3.Ident.id_fresh why_name in
  let tparams = List.map (mk_why3_type tenv) tparams in
  if is_type_bool tres then
    Why3.Term.create_psymbol preid tparams
  else
    Why3.Term.create_fsymbol preid tparams (mk_why3_type tenv tres) 

let mk_tdef name pos poly def = 
  let mk_poly t = 
    match t with
    | Tvar ({ tv_def = (Closed | Open) } as tv) -> 
        init_why3_tv tv
    | _ -> assert false in
  let tenv = List.map mk_poly poly in
  let mk_def def = 
    match def with
    | None -> None 
    | Some t -> Some (mk_why3_type tenv t) in
  let twhy3 =
    Why3.Ty.create_tysymbol
      (Why3.Ident.id_fresh name) 
      (List.map snd tenv)
      (mk_def def) in
  {
   t_name = name;
   t_wsymbol = twhy3;
   t_native_why = false;
   t_pos = pos;
   t_poly = poly;
   t_def = def
 }

(** Functions over variables *)



let name_id_var v = v.v_name, v.v_id

let var_compare v1 v2 = cmp_name_id (name_id_var v1) (name_id_var v2)

let mk_var glob name t pos = {
  v_name = name;
  v_id   = UID.fresh_var name;
  v_glob = glob;
  v_type = t;
  v_pos  = pos
}


let mk_local = mk_var false
let mk_global = mk_var true


let fresh_var v =
  mk_var v.v_glob v.v_name v.v_type dummy_pos

module VarCompare =
struct
  type t = var
  let compare = var_compare
end

module Vset = struct
  include Set.Make(VarCompare)

  let pp fmt vs =
    let pp_var fmt v =
      Format.fprintf fmt "%s_%a" v.v_name UID.pp_var v.v_id
    in EcUtil.pp_list ~sep:" " pp_var fmt (elements vs)

  let disjoint vs1 vs2 = is_empty (inter vs1 vs2)
end

module VarCompare2 =
struct
  type t = Ast.var * Ast.var 
        
  let compare (u1,u2) (v1,v2) =
    let c = var_compare u1 v1 in
    if c = 0 then var_compare u2 v2 else c
  
end

module Vset2 = Set.Make(VarCompare2)

(** Building why3 term and formula *)

let get_cnst_type = function 
  | Ebool _ -> Tbool
  | Eint _ -> Tint
  | Ecst (c,poly) ->
      let subst = List.map2 (fun v v' -> v,Tvar v') c.c_poly poly in
      subst_tvar subst c.c_type

let form_of_cnst c =
  match c with
  | Ebool b -> if b then Why3.Term.t_true else Why3.Term.t_false
  | Ecst (c,_) ->
      EcWhy3.mk_prop (Why3.Term.fs_app (fst c.c_why3) [] EcWhy3.ty_bool)
  | _ -> assert false

let term_of_cnst tenv c = 
  match c with 
  | Ebool b -> if b then EcWhy3.bool_true else EcWhy3.bool_false 
  | Eint i -> Why3.Term.t_int_const (string_of_int i)
  | Ecst (body,_) -> 
      let t = get_cnst_type c in
      let _, wt = add_why3_type tenv t in
      try 
        Why3.Term.fs_app (fst body.c_why3) [] wt
      with Why3.Ty.TypeMismatch(t1, t2) ->
        bug "term_of_cnst : Why.Ty.TypeMismatch %a and %a"
          Why3.Pretty.print_ty t1 Why3.Pretty.print_ty t2
        

let tres_op (_, op, poly) =
  let (_, tres) = op.op_type in
  let subst = List.map2 (fun tv tv' -> (tv,Tvar tv')) op.op_poly poly in
  subst_tvar subst tres 

let g_term_of_exp pp_exp add_v on_b =
  let add_vs tenv env lvs =
    List.fold_right (fun lv (tva,va,wls) ->
      let (tva,va,v) = add_v tva va lv in
      (tva,va,v::wls)) lvs (tenv,env,[]) in
  let rec term_of_exp tenv env t =
    match t with
    | Ecnst c -> term_of_cnst tenv c
    | Ebase v -> on_b env v
    | Ernd _ -> assert false 
    | Eapp(op,args) ->
        let tres = tres_op op in 
        let args = List.map (term_of_exp tenv env) args in
        let (_,op,_) = op in
        let ls = fst op.op_why3 in
        (try
          if EcWhy3.is_psymbol ls then
            EcWhy3.mk_bool (Why3.Term.ps_app ls args)
          else
            Why3.Term.fs_app (fst op.op_why3) args 
              (mk_why3_type tenv tres) 
        with Why3.Ty.TypeMismatch(t1, t2) ->
          bug "term_of_exp %s : %a: %a(%a) : Why.Ty.TypeMismatch %a and %a"
            (if EcWhy3.is_psymbol ls then "psymbol" else "lsymbol")
            pp_exp t
            Why3.Pretty.print_ls ls
            (pp_list ~sep:", " Why3.Pretty.print_term) args
            Why3.Pretty.print_ty t1 Why3.Pretty.print_ty t2 )

    | Elet(xs,t1,t2) ->
        begin match xs with
        | [] -> term_of_exp tenv env t2
        | [lv] ->
            let wt = term_of_exp tenv env t1 in
            let tenv, env, v = add_v tenv env lv in
            Why3.Term.t_let_close v wt (term_of_exp tenv env t2)
        | _ ->
            let wt = term_of_exp tenv env t1 in
            let tenv, env, wl = add_vs tenv env xs in
            let pattern = 
              Why3.Term.pat_app 
                (Why3.Term.fs_tuple (List.length xs))
                (List.map Why3.Term.pat_var wl)
                (EcWhy3.ty_tuple (List.map (fun v -> v.Why3.Term.vs_ty) wl))
            in
            let br = 
              Why3.Term.t_close_branch pattern (term_of_exp tenv env t2) in
            Why3.Term.t_case wt [br]
        end
    | Epair args -> 
        Why3.Term.t_tuple (List.map (term_of_exp tenv env) args)
    | Eif(e1,e2,e3) ->
        Why3.Term.t_if (form_of_exp tenv env e1)
          (term_of_exp tenv env e2)
          (term_of_exp tenv env e3)
  and form_of_exp tenv env t =
    match t with
    | Ecnst c -> form_of_cnst c
    | Ebase v -> EcWhy3.mk_prop (on_b env v)
    | Ernd _ -> assert false 
    | Eapp((_,op,_),args) -> 
        begin match op.op_native, args with
        | Some AND, [e1;e2] ->
            Why3.Term.t_and_simp (form_of_exp tenv env e1) 
              (form_of_exp tenv env e2) 
        | Some OR, [e1;e2] -> 
            Why3.Term.t_or_simp (form_of_exp tenv env e1) 
              (form_of_exp tenv env e2) 
        | Some IMPL, [e1;e2] -> 
            Why3.Term.t_implies_simp (form_of_exp tenv env e1) 
              (form_of_exp tenv env e2) 
        | Some NOT, [e1]-> 
            Why3.Term.t_not_simp (form_of_exp tenv env e1) 
        | Some (AND | OR | IMPL | NOT), _ -> assert false
        | _, _ -> 
            let args = List.map (term_of_exp tenv env) args in
            let ls = fst op.op_why3 in
            try 
              if EcWhy3.is_psymbol ls then
                Why3.Term.ps_app ls args 
              else
                EcWhy3.mk_prop (Why3.Term.fs_app ls args EcWhy3.ty_bool)
            with Why3.Ty.TypeMismatch(t1, t2) ->
              bug "form_of_exp : Why.Ty.TypeMismatch %a and %a"
                Why3.Pretty.print_ty t1 Why3.Pretty.print_ty t2
            
        end
    | Elet(xs,t1,t2) ->
        begin match xs with
        | [] -> form_of_exp tenv env t2
        | [lv] ->
            let wt = term_of_exp tenv env t1 in
            let tenv, env, v = add_v tenv env lv in
            Why3.Term.t_let_close v wt (form_of_exp tenv env t2)
        | _ ->
            let wt = term_of_exp tenv env t1 in
            let tenv, env, wl = add_vs tenv env xs in
            let pattern = 
              Why3.Term.pat_app 
                (Why3.Term.fs_tuple (List.length xs))
                (List.map Why3.Term.pat_var wl)
                (EcWhy3.ty_tuple (List.map (fun v -> v.Why3.Term.vs_ty) wl))
            in
            let br = 
              Why3.Term.t_close_branch pattern (form_of_exp tenv env t2) in
            Why3.Term.t_case wt [br]
        end    
    | Epair _ -> assert false
    | Eif(e1,e2,e3) ->
        Why3.Term.t_if (form_of_exp tenv env e1)
          (form_of_exp tenv env e2)
          (form_of_exp tenv env e3) in
  term_of_exp, form_of_exp

let term_of_var env v =
  try snd (List.find (fun(v',_) -> eq_var v v') env)
  with Not_found -> bug "EcTerm.term_of_var"

let add_why3_var tenv env lv =
  let tenv, t = add_why3_type tenv lv.v_type in
  let v = Why3.Term.create_vsymbol (Why3.Ident.id_fresh lv.v_name) t in
  tenv, (lv, Why3.Term.t_var v)::env, v

let add_why3_vars tenv env lvs =
    List.fold_right (fun lv (tva,va,wls) ->
      let (tva,va,v) = add_why3_var tva va lv in
      (tva,va,v::wls)) lvs (tenv,env,[]) 

let term_of_exp, form_of_exp = 
  g_term_of_exp (fun _ _ -> ()) add_why3_var term_of_var

let mk_op_why3 why_name t body =
  match body with
  | None ->
      let ls = mk_fsymbol why_name t in
      ls, None
  | Some (params, body) ->
      let tenv, env, params = add_why3_vars [] [] params in
      let tenv, tres = add_why3_type tenv (snd t) in
      let preid = Why3.Ident.id_fresh why_name in
      let tparams = List.map (fun v -> v.Why3.Term.vs_ty) params in
      let ls, te = 
        if is_type_bool (snd t) then 
          Why3.Term.create_psymbol preid tparams, 
          form_of_exp tenv env body
        else 
          Why3.Term.create_fsymbol preid tparams tres, 
          term_of_exp tenv env body in
      Why3.Decl.make_ls_defn ls params te
      

(** {Functions on operators} *)


let mk_op_body name native why t body infix pos assoc prec =
  (* TODO why = why_name, ac. If ac check that t is the expected type i.e
     a,a -> a *)
  let fv = fv_g_fct_sig t in
  let ld = mk_op_why3 (fst why) t body in
  { op_name = name;
    op_native = native;
    op_why = why;
    op_why3 = ld;
    op_type = t;
    op_body = body;
    op_pos = pos;
    op_id = UID.fresh_op name;
    op_infix = infix;
    op_poly = fv;
    op_native_why = false;
    op_assoc = assoc;
    op_prec = prec;
  }

let instanciate_op op pos =
  if op.op_poly = [] then [],op.op_type
  else
    let poly = List.map (fun tv -> mk_tvar tv.tv_name pos) op.op_poly in
    let subst = List.combine op.op_poly poly in
    poly, subst_fct_sig subst op.op_type

let reset_poly =
  let reset tv = 
    match tv.tv_def with
    | Defined _ -> tv.tv_def <- Open
    | _ -> () in
  List.iter reset




(** Functions on expressions :
    * We normally should have defined the generic version first and then
    * instantiate it with var/eq_var, but for some mysterious reason,
    * ocaml doesn't want to accept that !
    * *)


let g_eq_exp eq_v eq_b =
  let rec eq_exp e1 e2 =
    match e1, e2 with
    | Ebase v1, Ebase v2 -> eq_b v1 v2
    | Ecnst c1, Ecnst c2 -> eq_cnst c1 c2
    | Ernd r1, Ernd r2 -> eq_random r1 r2
    | Epair l1, Epair l2 ->
      (try List.for_all2 eq_exp l1 l2 with Invalid_argument _ -> false)
    | Eif(b1,e11,e12),Eif(b2,e21,e22) ->
      eq_exp b1 b2 && eq_exp e11 e21 && eq_exp e12 e22
    | Eapp(op1,args1), Eapp(op2,args2) ->
      let eq_args args1 args2 =
        try List.for_all2 eq_exp args1 args2
        with _ -> false 
      in
      eq_args args1 args2 && eq_op op1 op2 
    | Elet(xs1,e11,e12), Elet(xs2,e21,e22) ->
        (try 
          eq_exp e11 e21 && eq_exp e12 e22 &&
          List.for_all2 eq_v xs1 xs2 
        with _ -> false)
    | _, _ -> false

  and eq_random r1 r2 =
    match r1, r2 with
    | Rinter(e11,e12), Rinter(e21,e22) -> eq_exp e11 e21 && eq_exp e12 e22
    | Rbool, Rbool -> true
    | Rbitstr e1, Rbitstr e2 -> eq_exp e1 e2
    | Rexcepted(r1',e1), Rexcepted(r2',e2) ->
        eq_random r1' r2' && eq_exp e1 e2
    | Rapp (op1,args1), Rapp (op2,args2) when eq_op op1 op2 ->
      List.for_all2 eq_exp args1 args2
    | _, _ -> false in
  eq_exp

let rec is_cnst_exp = function
  | Ecnst _ -> true
  | Ebase _| Ernd _ -> false
  | Epair l -> List.for_all is_cnst_exp l 
  | Eapp(_,args) -> List.for_all is_cnst_exp args
  | Eif(b,e1,e2) -> is_cnst_exp b && is_cnst_exp e1 && is_cnst_exp e2
  | Elet(_,e1,e2) -> is_cnst_exp e1 && is_cnst_exp e2


let rec is_cnst_rnd = function
  | Rinter(e1,e2) -> is_cnst_exp e1 && is_cnst_exp e2
  | Rbool -> true
  | Rbitstr e -> is_cnst_exp e
  | Rexcepted(r,e) -> is_cnst_rnd r && is_cnst_exp e
  | Rapp(_,args) -> List.for_all is_cnst_exp args

let rec is_var_exp = function
  | Ecnst _ | Ebase _ -> true
  | Ernd _ -> false
  | Epair l -> List.for_all is_var_exp l
  (* CESAR: What's append if the operator is a pop ?*)
  | Eapp(_,args) -> List.for_all is_var_exp args
  | Eif(b,e1,e2) -> is_var_exp b && is_var_exp e1 && is_var_exp e2
  | Elet(_,e1,e2) -> is_var_exp e1 && is_var_exp e2

let rec is_uniform = function
  | Rinter _ | Rbool | Rbitstr _ -> true
  | Rapp _ -> (* CESAR CAN WE KNOW IF THE OP IS UNIFORM *) false
  | Rexcepted(r, _) -> is_uniform r

(* substitution *)

type 'v renaming = ('v * 'v) list

(** [mk_renaming vd] return (vd',r) where r is a renaming allowing
    to replace variable in vd by the fresh variables in vd' *)
let g_mk_renaming fresh_var d1 =
  let fresh_decl = List.map fresh_var in
  let d2 = fresh_decl d1 in
  d2, List.combine d1 d2

let mk_renaming d1 = g_mk_renaming fresh_var d1

let map_var_in_exp do_v do_b exp =
  let rec frec exp =
    match exp with
      | Ecnst c -> Ecnst c
      | Ebase v -> do_b v
      | Ernd r -> Ernd (frec_rnd r)
      | Eapp (op,tl) -> Eapp(op, List.map frec tl)
      | Eif (t1,t2,t3) -> Eif(frec t1, frec t2, frec t3)
      | Epair l -> Epair (List.map frec l)
      | Elet(xs,e1,e2) -> Elet(List.map do_v xs,frec e1, frec e2)
  and frec_rnd r =
    match r with
      | Rinter(e1,e2) -> Rinter(frec e1, frec e2)
      | Rbool -> Rbool
      | Rbitstr e -> Rbitstr (frec e)
      | Rexcepted(r,e) -> Rexcepted(frec_rnd r, frec e)
      | Rapp (op,tl) -> Rapp(op, List.map frec tl)
  in frec exp

let subst_var s x =
  try (List.assoc x s) with Not_found -> Ebase x

let subst_exp s = map_var_in_exp (fun x -> x) (subst_var s)

let rename_var s x =
  try (List.assoc x s) with Not_found -> x

let rename_exp s = map_var_in_exp (fun x -> x) (fun x -> Ebase (rename_var s x))

(* Function over instructions *)

let rename_lasgn s = function
  | Ltuple l -> Ltuple (List.map (rename_var s) l)
  | Lupd(v,e) -> Lupd (rename_var s v, rename_exp s e)

let rec rename_instr s i =
  match i with
    | Sasgn(v,e) -> Sasgn(rename_lasgn s v, rename_exp s e)
    | Scall(v,f,args) ->
      Scall(rename_lasgn s v,f,List.map (rename_exp s) args)
    | Sif(b,s1,s2) ->
      Sif(rename_exp s b, rename_stmt s s1, rename_stmt s s2)
    | Swhile (b,body) ->
      Swhile (rename_exp s b, rename_stmt s body)
    | Sassert b -> 
      Sassert (rename_exp s b)
and rename_stmt s l = List.map (rename_instr s) l

(* Functions over functions *)

exception UndefinedFct of fct
exception DefinedFct of fct


let eq_fct f1 f2 = f1.f_name = f2.f_name && f1.f_game.g_name = f2.f_game.g_name

let is_defined_fct f =
  match f.f_body with
    | FctDef _ -> true
    | _ -> false

let check_defined_fct f =
  if not (is_defined_fct f) then raise (UndefinedFct f)

let fct_def f =
  match f.f_body with
    | FctDef d -> d
    | _ -> raise (UndefinedFct f)

let fct_adv f =
  match f.f_body with
    | FctAdv(a,fcts) -> (a,fcts)
    | _  -> raise (DefinedFct f)

let fct_global_vars f = List.map snd f.f_game.g_vars

(* Modified global variables *)

let modified_lasgn = function
  | Ltuple l -> List.fold_right Vset.add l Vset.empty
  | Lupd(v,_) -> Vset.singleton v

let rec modified_instr = function
  | Sasgn(l,_) -> modified_lasgn l
  | Scall(l,f,_) ->
    List.fold_right Vset.add f.f_modify (modified_lasgn l)
  | Sif(_,s1,s2) -> Vset.union (modified_stmt s1) (modified_stmt s2)
  | Swhile (_,body) -> modified_stmt body
  | Sassert _ -> Vset.empty
and modified_stmt s =
  List.fold_left (fun acc i -> Vset.union acc (modified_instr i)) Vset.empty s

let global_modified = function
  | FctDef fd ->
    Vset.filter (fun v -> v.v_glob) (modified_stmt fd.f_def)
  | FctAdv(_,o) ->
    List.fold_right (fun f -> List.fold_right Vset.add f.f_modify)
      o Vset.empty

(* Read variables *)
let fold_var_in_exp do_var_qq do_var acc exp =
  let rec frec acc exp =
    match exp with
      | Ecnst _ -> acc
      | Ebase v -> do_var acc v
      | Ernd r -> frec_rnd acc r
      | Eapp (_,tl) ->  List.fold_left frec acc tl
      | Eif (t1,t2,t3) -> frec (frec (frec acc t1) t2) t3
      | Epair l  -> List.fold_left frec acc l
      | Elet(xs,t1,t2) -> 
          List.fold_right do_var_qq xs (frec (frec acc t1) t2)
  and frec_rnd acc r =
    match r with
      | Rinter(e1,e2) -> frec (frec acc e1) e2
      | Rbool -> acc
      | Rbitstr e -> frec acc e
      | Rexcepted(r,e) -> frec (frec_rnd acc r) e
      | Rapp (_,tl) ->  List.fold_left frec acc tl
  in frec acc exp

let fv_exp_acc = fold_var_in_exp Vset.remove (fun fv x -> Vset.add x fv)

let fv_exp = fv_exp_acc Vset.empty

let fv_args = List.fold_left fv_exp_acc Vset.empty

let global_read_fct f =
  List.fold_right Vset.add f.f_read Vset.empty

let read_lasgn = function
  | Ltuple _ -> Vset.empty
  | Lupd(v,e1) -> Vset.add v (fv_exp e1)

let rec read_instr i =
  match i with
    | Sasgn(l,e) ->
      Vset.union (read_lasgn l) (fv_exp e)
    | Scall(l,f,args) ->
      Vset.union (read_lasgn l)
        (Vset.union (global_read_fct f) (fv_args args))
    | Sif(e,s1,s2) ->
      Vset.union (fv_exp e) (Vset.union (read_stmt s1) (read_stmt s2))
    | Swhile(e,body) ->
      Vset.union (fv_exp e) (read_stmt body)
    | Sassert e -> 
      fv_exp e

and read_stmt s =
  List.fold_left (fun acc i -> Vset.union acc (read_instr i)) Vset.empty s

let global_read = function
  | FctDef fd -> 
    let fv_ret = match fd.f_return with None -> Vset.empty | Some e -> fv_exp e in
    Vset.filter (fun v -> v.v_glob) 
    (Vset.union (read_stmt fd.f_def) fv_ret )
  | FctAdv(_,o) ->
    List.fold_right (fun f -> List.fold_right Vset.add f.f_read)
      o Vset.empty


(** Equality of stmt *)

let eq_lasgn l1 l2 =
  match l1, l2 with
    | Ltuple l1, Ltuple l2 -> eq_list eq_var l1 l2
    | Lupd (x1, e1), Lupd (x2, e2) -> eq_var x1 x2 && eq_exp e1 e2
    | _, _ -> false

let rec eq_instr i1 i2 =
  match i1, i2 with
    | Sasgn(l1,e1), Sasgn(l2,e2) ->
      eq_lasgn l1 l2 && eq_exp e1 e2
    | Scall(l1,f1,args1), Scall(l2,f2,args2) ->
      eq_lasgn l1 l2 && eq_fct f1 f2 && eq_list eq_exp args1 args2
    | Sif(e1,s1,s1'), Sif(e2,s2,s2') ->
      eq_exp e1 e2 && eq_stmt s1 s2 && eq_stmt s1' s2'
    | Swhile(e1,s1), Swhile(e2,s2) ->
      eq_exp e1 e2 && eq_stmt s1 s2
    | Sassert(e1), Sassert(e2) -> eq_exp e1 e2
    | _, _ -> false

and eq_stmt s1 s2 = eq_list eq_instr s1 s2


(** Retyping *)




let rec seq_type t1 t2 =
  match t1, t2 with
      | Tunit, Tunit | Tint, Tint | Tbool, Tbool | Treal, Treal -> true
    | Tbitstring k1, Tbitstring k2 ->
        eq_exp k1 k2 
    | Ttuple l1, Ttuple l2 ->
        if List.length l1 = List.length l2 then List.for_all2 seq_type l1 l2
        else false 
    | Tnamed { t_def = Some t }, _ -> seq_type t t2
    | _, Tnamed { t_def = Some t } -> seq_type t1 t
    | Tnamed tn1, Tnamed tn2 ->
        tn1.t_name = tn2.t_name && 
        List.length tn1.t_poly = List.length tn2.t_poly &&
        List.for_all2 seq_type tn1.t_poly tn2.t_poly
  (* Types variables *)
    | Tvar v1, Tvar v2 when eq_tvar v1 v2 -> true
    | Tvar {tv_def = Defined t'} , t -> seq_type t' t
    | t, Tvar {tv_def = Defined t'}  -> seq_type t t'
    | _, _ -> false


(** Lossless *)
let rec is_lossless_expr e =
  match e with
  | Ecnst _ | Ebase _ -> true
  | Eapp(_, args) | Epair args -> List.for_all is_lossless_expr args
  | Elet(_,e1,e2) -> is_lossless_expr e1 && is_lossless_expr e2
  | Eif(e1,e2,e3) -> 
      is_lossless_expr e1 && is_lossless_expr e2 && is_lossless_expr e3
  | Ernd r -> is_lossless_rnd r
and is_lossless_rnd r =
  match r with
  | Rinter (e1, e2) -> 
      (* TODO: this is true only if e1 <= e2 ... *)
      is_lossless_expr e1 && is_lossless_expr e2
  | Rbool | Rbitstr _ -> true
  | Rexcepted(r,l) -> 
      (* TODO: this is true only if l is not the domain of r ... *)
      is_lossless_rnd r && is_lossless_expr l
  (* TODO: all probabilistic operators are lossless ? *)
  | Ast.Rapp (_,args) ->  List.for_all is_lossless_expr args

let rec is_lossless_stmt s =
  List.for_all is_lossless_instr s
and is_lossless_instr i =
  match i with
  | Sasgn (_, e) -> is_lossless_expr e
  | Scall(_,f,_) -> is_lossless_fun f
  | Sif(_,s1,s2) -> is_lossless_stmt s1 && is_lossless_stmt s2
  | Swhile _ -> false
  | Sassert _ -> false 
and is_lossless_fun f = 
  match f.f_body with
  | FctAdv (_, o) -> List.for_all is_lossless_fun o
  | FctDef fdef ->
      is_lossless_stmt fdef.f_def &&
      match fdef.f_return with
      | None -> true
      | Some e -> is_lossless_expr e


