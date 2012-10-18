(** Printing function for {!Ast} objects. *)

open EcUtil
open Ast

let pp_const fmt v = Format.fprintf fmt "%s" v.c_name

let pp_uid_var fmt v = Format.fprintf fmt "%s_%a" v.v_name UID.pp_var v.v_id

let pp_var fmt v = Format.fprintf fmt "%s" v.v_name

let pp_vset fmt s =
  Format.fprintf fmt "@[{%a}@]"
    (EcUtil.pp_list ~sep:", " pp_var) (EcTerm.Vset.elements s)

let pp_op fmt (op:oper) =
  let op_b = EcTerm.op_body op in
  Format.fprintf fmt "%s" op_b.op_name

let pp_cnst fmt (c:const cnst) =
  match c with
    | Ebool b ->  Format.fprintf fmt "%s" (if b then "true" else "false")
    | Eint n -> Format.fprintf fmt "%d" n
    | Ecst (c,_) -> pp_const fmt c

let rec is_closed_list e =
  match e with
  | Eapp(f,[_;e2]) when EcTerm.is_op CONS_LIST f ->
      is_closed_list e2
  | Ecnst(Ecst(c,_)) -> c.c_name = "[]" 
  | _ -> false

let rec get_closed_list e = 
  match e with
  | Eapp(f,[e1;e2]) when EcTerm.is_op CONS_LIST f ->
      e1::get_closed_list e2 
  | Ecnst(Ecst(c,_)) when (c.c_name = "[]") -> []
  | _ -> raise Not_found

      
let protect_on x s = if x then "(" ^^ s ^^ ")" else s

(*
   IMPL IFF -> 1
   OR -> 2
   AND -> 3
   NOT 4 ->
   OP1 -> 5
   OP2 -> 6
   OP3 -> 7
   OP4 -> 8
   max -> 9 *)

let op_char1 = ['=';'<';'>';'~']
let op_char2 = ['+';'-']
let op_char3 = ['*';'/';'%']

let string_contains chars s = 
  List.exists (String.contains s) chars
  
let priority op = 
  let name = EcTerm.op_name op in
  match name with
  | "=>" | "<=>" -> 1, 2, 1
  | "||" -> 2, 3, 2
  | "&&" -> 2, 4, 3
(*  | "!" -> 4 *)
  | _ ->
      if string_contains op_char1 name then 5,5,6
      else if string_contains op_char2 name then 6,6,7
      else if string_contains op_char3 name then 7,7,8
      else 8,8,9

let rec g_pp_exp pp_v pp_base pri fmt e =
  let pp_exp = g_pp_exp pp_v pp_base in
  match e with
    | Ecnst c -> pp_cnst fmt c
    | Ebase v -> pp_base fmt v
    | Ernd r -> g_pp_random pp_exp fmt r
    | Epair l -> 
        Format.fprintf fmt "@[(%a)@]" (pp_list ~sep:",@," (pp_exp 0)) l
    | Eapp (_,[_;_]) when is_closed_list e ->        
        let l = get_closed_list e in
        Format.fprintf fmt "@[[%a]@]"
          (pp_list ~sep:";@," (pp_exp 0)) l
    | Eapp(f1,[Eapp(f2,[e1;e2])]) when 
        EcTerm.is_op NOT f1 && EcTerm.is_op EQ f2 ->
          Format.fprintf fmt (protect_on (pri > 4) "@[%a <> %a@]")
          (pp_exp 5) e1 (pp_exp 5) e2
    | Eapp(f1,[e1]) when EcTerm.is_op NOT f1 ->
        Format.fprintf fmt (protect_on (pri > 4) "!%a")
          (pp_exp 4) e1
    | Eapp (f, [e1; e2]) when EcTerm.is_infix f ->
        let p,p1,p2 = priority f in
        Format.fprintf fmt (protect_on (pri > p) "@[%a %a %a@]")
          (pp_exp p1) e1 pp_op f (pp_exp p2) e2
    | Eapp (f, args) when EcTerm.is_op PGET_MAP f ->
      Format.fprintf fmt (protect_on (pri > 9) "@[%a[%a]@]")
        (pp_exp 9) (List.nth args 0) (pp_exp 0) (List.nth args 1)
    | Eapp (f, args) when EcTerm.is_op PUPD_MAP f ->
      Format.fprintf fmt (protect_on (pri > 9) "@[%a[%a <- %a]@]")
        (pp_exp 9) (List.nth args 0) (pp_exp 0) (List.nth args 1)
          (pp_exp 0) (List.nth args 2)
    | Eapp (f,args) when EcTerm.is_op REAL_ABS f ->
      Format.fprintf fmt "@[|%a|@]" (pp_exp 0) (List.nth args 0)
    | Eapp (f,args) when EcTerm.is_op REAL_EXP f ->
      Format.fprintf fmt "@[exp(%a)@]" (pp_exp 0) (List.nth args 0)
    | Eapp (f,args) when (EcTerm.is_op REAL_OPP f || EcTerm.is_op INT_OPP f) ->
      Format.fprintf fmt "@[-%a@]" (pp_exp 9) (List.nth args 0)
    | Eapp(f,args) when EcTerm.is_op REAL_OF_INT f ->
      Format.fprintf fmt "@[%a%%r@]" (pp_exp 9) (List.nth args 0)
    | Eapp (f, args) ->
      Format.fprintf fmt "@[%a (%a)@]" pp_op f (pp_list ~sep:",@," (pp_exp 0)) 
          args
    | Eif (c, e1, e2) ->
      Format.fprintf fmt (protect_on (pri > 0) "@[if %a then %a else %a@]")
          (pp_exp 0) c (pp_exp 0) e1 (pp_exp 0) e2
    | Elet (xs, e1, e2) ->
      Format.fprintf fmt (protect_on (pri > 0) "(let %a = %a in %a)")
          (pp_list ~sep:"," pp_v) xs (pp_exp 4) e1 (pp_exp 0) e2

and g_pp_random pp_exp fmt r =
  match r with
    | Rinter(e1,e2) ->
      Format.fprintf fmt "[%a..%a]" (pp_exp 0) e1 (pp_exp 0) e2
    | Rbool -> Format.fprintf fmt "{0,1}"
    | Rbitstr e -> Format.fprintf fmt "{0,1}^%a" (pp_exp 9) e
    | Rexcepted(r,e) -> Format.fprintf fmt "%a \\ %a" 
          (g_pp_random pp_exp) r (pp_exp 9) e
    | Rapp (f, args) ->
      Format.fprintf fmt "@[%a (%a)@]" pp_op f
          (pp_list ~sep:",@," (pp_exp 0)) args

let pp_exp = g_pp_exp pp_var pp_var

let pp_random fmt r = g_pp_random pp_exp fmt r

let pp_exp = pp_exp 0

let pp_tvar fmt tv =
  Format.fprintf fmt "%s%a" tv.tv_name UID.pp_tvar tv.tv_id

let rec pp_type_exp b debug fmt = function
  | Tunit -> Format.fprintf fmt "unit"
  | Tbool -> Format.fprintf fmt "bool"
  | Tint ->  Format.fprintf fmt  "int"
  | Treal -> Format.fprintf fmt "real"
  | Tbitstring e -> Format.fprintf fmt "bitstring{%a}" pp_exp e
  (* | Ttuple [] -> Format.fprintf fmt "unit" *)
  | Ttuple l ->
      let lparen, rparen = if b || debug then "(",")" else "","" in
      Format.fprintf fmt "@[%s%a%s@]"
        lparen 
        (pp_list ~sep:(format_of_string " * ") (pp_type_exp true debug)) l 
        rparen
  | Tnamed tdef ->
      Format.fprintf fmt "@[%a%s%a@]"
        (pp_type_args debug) tdef.t_poly 
        tdef.t_name
        (pp_type_exp_def debug) tdef.t_def
  | Tvar tdef ->
      let pp_v fmt v = 
        if debug then pp_tvar fmt v else Format.fprintf fmt "%s" v.tv_name in
      Format.fprintf fmt "@[%a%a@]"
        pp_v tdef
        (pp_type_exp_var_def debug) 
        tdef.tv_def

and pp_type_args debug fmt args =
  match args with
  | [] -> ()
  | [a] -> Format.fprintf fmt "%a " (pp_type_exp true debug) a
  | _ -> Format.fprintf fmt "(%a)" 
        (pp_list ~sep:(format_of_string ",") (pp_type_exp false debug)) args
and pp_type_exp_def debug fmt t =
  match t with
  | None -> ()
  | Some t ->
      if debug then 
        Format.fprintf fmt "@[[%a]@]" (pp_type_exp false debug) t
and pp_type_exp_var_def debug fmt t =
  if debug then
    match t with
    | Open -> Format.fprintf fmt "/*open*/"
    | Closed -> Format.fprintf fmt "/*closed*/"
    | Defined t ->
        Format.fprintf fmt "@[[%a]]" (pp_type_exp false debug) t



let pp_type_exp_d = pp_type_exp false true

let pp_type_exp = pp_type_exp false false 

let pp_type_def fmt t = 
  let pp_def fmt t =
    match t with
    | None -> ()
    | Some t -> Format.fprintf fmt " = %a" pp_type_exp t in
  Format.fprintf fmt "type %a%s%a.@." 
    (pp_type_args false) t.t_poly
    t.t_name 
    pp_def t.t_def

let pp_typed_var fmt v = Format.fprintf fmt "%s:%a"
  v.v_name pp_type_exp_d v.v_type

let pp_cnst_def fmt c = match c.c_def with
  | None ->
    Format.fprintf fmt "cnst %a : %a@." pp_const c pp_type_exp c.c_type
  | Some def ->
    Format.fprintf fmt "cnst %a : %a = %a@."
      pp_const c pp_type_exp c.c_type pp_exp def

let pp_var_decl fmt v =
   Format.fprintf fmt "var %a : %a;@\n" pp_var v pp_type_exp v.v_type

let pp_gvar_decl fmt v =
   Format.fprintf fmt "var %a : %a@\n" pp_var v pp_type_exp v.v_type

let pp_var_decl_d fmt v =
  Format.fprintf fmt "var %a : %a;;@\n" pp_var v pp_type_exp_d v.v_type


let pp_fct_sig fmt (lt, t_res) =
  let pp_tparams fmt lt = 
    if List.length lt = 1 then
      pp_type_exp fmt (List.hd lt)
    else 
      Format.fprintf fmt "(%a)" (pp_list ~sep:", " pp_type_exp) lt in
  Format.fprintf fmt "%a -> %a" pp_tparams lt pp_type_exp t_res

let rec get_same_type v lv =
  match lv with 
  | [] -> [], []
  | v' :: lv2 ->
      if EcTerm.seq_type v.v_type v'.v_type then
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
        Format.fprintf fmt "%a : %a" (pp_list ~sep:", " pp_var) lv 
          pp_type_exp v.v_type in
  let lv = split_decls lv in
  Format.fprintf fmt "%a" (pp_list ~sep:", " p_decl) lv

let pp_tvar_list = pp_lvar_decls 

let pp_op_decl fmt op =
  let name = if op.op_infix then ("["^op.op_name^"]") else op.op_name in
  match op.op_body with
  | None ->
      Format.fprintf fmt "op %s : %a.@\n" name pp_fct_sig op.op_type
  | Some (params,body) ->
      Format.fprintf fmt "op %s (%a) = %a.@\n" 
        name 
        pp_tvar_list params
        pp_exp body

let pp_pop_decl fmt op =
  let name = op.op_name in
  match op.op_body with
    | None ->
      Format.fprintf fmt "pop %s : %a.@\n" name pp_fct_sig (List.tl (fst op.op_type), List.hd (fst op.op_type)) 
    | Some (params,body) ->
      Format.fprintf fmt "pop %s (%a) = (%a) -> %a.@\n" 
        name 
        pp_tvar_list (List.tl params) pp_lvar_decls [List.hd params]
        pp_exp body

let pp_var_list fmt l = (pp_list ~sep:(format_of_string", ") pp_var) fmt l

let pp_adv_decl fmt adv =
  Format.fprintf fmt "adversary %s(%a) : %a {%a};;@\n"
    adv.adv_name  pp_tvar_list adv.adv_param pp_type_exp
    adv.adv_res
    (pp_list ~sep:(format_of_string", ") pp_fct_sig) adv.adv_odecl

let pp_lval fmt lv = match lv with
  | [v] -> Format.fprintf fmt "%a" pp_var v
  | _ -> Format.fprintf fmt "(%a)" pp_var_list lv

let pp_lasgn fmt = function
  | Ltuple [] -> ()
  | Ltuple lv -> Format.fprintf fmt "%a = " pp_lval lv
  | Lupd(v,e) -> Format.fprintf fmt "%a[%a] = " pp_var v pp_exp e

let pp_call fmt (f, args) =
  Format.fprintf fmt "@[%s (%a)@]" f.f_name (pp_list ~sep:",@ " pp_exp) args

let is_single_stmt s = 
  match s with
  | [Sasgn _] | [Scall _] | [Sassert _] -> true
  | _ -> false

let rec pp_instr fmt instr = match instr with
  | Sasgn (l, e) -> Format.fprintf fmt "@[%a%a;@]" pp_lasgn l pp_exp e
  | Scall (l, f, args) ->
    Format.fprintf fmt "@[%a%a;@]" pp_lasgn l pp_call (f, args)
  
  | Sif (c, bt, []) ->
    Format.fprintf fmt "@[if (%a) %a@]"
      pp_exp c pp_block bt
  | Sif (c, bt, bf) ->
      let pp_space fmt bt = 
        if is_single_stmt bt then Format.fprintf fmt "@\n" else 
        Format.fprintf fmt " " in
    Format.fprintf fmt "@[if (%a) %a%aelse %a@]"
      pp_exp c pp_block bt pp_space bt pp_block bf
  | Swhile (cond, body) ->
    Format.fprintf fmt "@[while (%a) %a@]"
      pp_exp cond pp_block body
  | Sassert cond ->
    Format.fprintf fmt "@[assert (%a);@]" pp_exp cond
and pp_block fmt stmt =
  if is_single_stmt stmt then
    Format.fprintf fmt "@[%a@]" (pp_stmt ~num:false) stmt
  else
    Format.fprintf fmt "{@\n  @[%a@]@\n}" (pp_stmt ~num:false) stmt

and pp_stmt ?(num=false) fmt stmt =
  let count = ref 0 in
  let pp_instr fmt i = 
    let pp_space fmt i = 
      if i < 10 then Format.fprintf fmt "  "
      else if i < 100 then Format.fprintf fmt " " in
    if num then begin 
      incr count; 
      Format.fprintf fmt "%a%i : %a" pp_space !count !count pp_instr i
    end
    else pp_instr fmt i in
  Format.fprintf fmt "@[%a@]" (pp_list ~sep:"@\n" pp_instr) stmt

let pp_return fmt exp = match exp with
  | None -> ()
  | Some e -> Format.fprintf fmt "return %a;" pp_exp e

let pp_fct_def fmt def =
  Format.fprintf fmt "%a" (pp_list ~sep:"" pp_var_decl) def.f_local;
  Format.fprintf fmt "%a@\n" (pp_stmt ~num:false) def.f_def; 
  pp_return fmt def.f_return

let pp_fct_full_name fmt fct =
  Format.fprintf fmt "%s.%s" fct.f_game.g_name fct.f_name

let pp_fct_name fmt fct = Format.fprintf fmt "%s" fct.f_name

let pp_fct fmt fct =
  match fct.f_body with
    | FctAdv (adv, l) ->
      Format.fprintf fmt "abs %a = %s{%a}@\n" pp_fct_name fct adv.adv_name
        (pp_list ~sep:"; " pp_fct_name) l
    | FctDef def ->
      Format.fprintf fmt "@[<v 2>fun %s (%a) : %a = {@\n%a@]@\n}@\n"
        fct.f_name pp_tvar_list fct.f_param pp_type_exp (fct.f_res.v_type)
      pp_fct_def def

let pp_ifct fmt ifct =
  let pp_param fmt (v, ty) =
    Format.fprintf fmt "%s : %a" v pp_type_exp ty
  in
    Format.fprintf fmt "%s(%a) : %a"
      ifct.if_name
      (pp_list ~sep:", " pp_param) ifct.if_params
      pp_type_exp ifct.if_type

let pp_igame fmt ig =
  Format.fprintf fmt "@[<v 2>game interface %s = {@\n%a\n}@\n"
    ig.gi_name
    (pp_list ~sep:"" pp_ifct) ig.gi_sig.gi_functions

let pp_game fmt g =
  Format.fprintf fmt "@[<v 2>game %s%s = {@\n%a%a@]@\n}@\n"
    g.g_name
    (match g.g_subinterface with
      | Some i -> Printf.sprintf " : %s" i
      | None   -> "")
    (pp_list ~sep:"" pp_gvar_decl) (List.map snd g.g_vars)
    (pp_list ~sep:"" pp_fct) (List.map snd g.g_functions)

(*
  let pp_equiv_kind fmt = function
  | Aequiv_spec(pre,post) ->
  Format.fprintf fmt "@[<hov 2>@ @[%a@]@ ==>@ @[%a@]@]"

  let pp_annot_body fmt a = match a with
  | Aequiv (f1, f2, pre, post) ->
  Format.fprintf fmt "%a ~ %a :@[<hov 2>@ @[%a@]@ ==>@ @[%a@]@]"
  pp_fct_full_name f1 pp_fct_full_name f2 pp_exp pre pp_exp post
  | Aproba ((f1,p1), (f2, p2)) ->
  Format.fprintf fmt "@[<hov 2>%a[@[%a@]]@ == %a[@[%a@]]@]"
  pp_fct_full_name f1 pp_exp p1 pp_fct_full_name f2 pp_exp p2
  let pp_annot fmt a =
  Format.fprintf fmt "property %s : @[<hov 2>@[%a@]@]@."
  a.a_name pp_annot_body a.a_body
*)


(** {2 Probability } *)

let pp_proba fmt (f,e) =
  Format.fprintf fmt "@[%a[%a]@]" pp_fct_full_name f pp_exp e

let pp_real_exp = g_pp_exp pp_var pp_proba 0


