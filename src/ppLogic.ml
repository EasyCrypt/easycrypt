open EcUtil

let pp_equiv fmt (f1, f2, pre, post) =
  Format.fprintf fmt "%a ~ %a@\n"
    PpAst.pp_fct_full_name f1 PpAst.pp_fct_full_name f2;
  Format.fprintf fmt "@[%a@ ==>@ %a@]@\n@." 
    Fol.pp_pred pre Fol.pp_pred post

(** {2 Why format } *)
(* TODO
 * merge with PpAst
 * Have a nice pretty printer for variables
 *)

let pp_var_why fmt v = PpAst.pp_uid_var fmt v

let pp_op_why fmt op =
  Format.fprintf fmt "%s" (EcTerm.op_why op)

let pp_const_why fmt c =
  Format.fprintf fmt "%s%s" c.Ast.c_name (if c.Ast.c_def = None then "" else "()")

let pp_cnst_why fmt = function
  | Ast.Ebool b ->  Format.fprintf fmt "%s" (if b then "True" else "False")
  | Ast.Eint n -> Format.fprintf fmt "%d" n
  | Ast.Ecst (c,_) -> pp_const_why fmt c

let rec pp_exp_why pp_base fmt e =
  let pp_exp = pp_exp_why pp_base in
  match e with
    | Ast.Ecnst c -> pp_cnst_why fmt c
    | Ast.Ebase v -> pp_base fmt v
    | Ast.Ernd _  -> bug "PpLogic.pp_exp_why : rnd expression"
    | Ast.Epair l -> Format.fprintf fmt "(%a)" (pp_list ~sep:", " pp_exp) l
    | Ast.Eapp(op,args) ->
        Format.fprintf fmt "(%a %a)" pp_op_why op
          (pp_list ~sep:" " pp_exp) args
    | Ast.Eif(c, e1, e2) ->
      Format.fprintf fmt "(@[(if %a then@ %a else@ %a)@])"
        pp_exp c pp_exp e1 pp_exp e2
    | Ast.Elet(vs, e1, e2) ->
      Format.fprintf fmt "(@[(let@ %a=%a in@ %a)@])"
        (pp_list ~sep:" " pp_base) vs 
        pp_exp e1 pp_exp e2

let pp_term_why fmt e = pp_exp_why Fol.pp_lvar_why fmt e

let rec pp_type_why fmt = function
  | Ast.Tunit -> Format.fprintf fmt "Unit.unit"
  | Ast.Tbool -> Format.fprintf fmt "Bool.bool"
  | Ast.Tint -> Format.fprintf fmt "int"
  | Ast.Treal -> Format.fprintf fmt "real"
  | Ast.Tbitstring _ -> 
      (* TODO: make different bitstring type for each size,
         or add a length predicate (I prefers this solution *)
      Format.fprintf fmt "bitstring"
  | Ast.Tnamed def -> 
      if def.Ast.t_poly = [] then
        Format.fprintf fmt "%s" def.Ast.t_name
      else 
        Format.fprintf fmt "(%s %a)" def.Ast.t_name
          (pp_list ~sep:" " pp_type_why) def.Ast.t_poly
  | Ast.Tvar {Ast.tv_def = Ast.Defined t} -> pp_type_why fmt t
  | Ast.Tvar def -> PpAst.pp_tvar fmt def
  | Ast.Ttuple l -> 
      Format.fprintf fmt "(%a)" (pp_list ~sep:"'" pp_type_why) l

let pp_type_hyp_why _fmt _v = ()
(* TODO deal correctly with bitstring *)
(*
  match v.v_type with
  | Tbitstring e -> ()
  Format.fprintf fmt "length_bitstring(%a) = %a ->@ "
  pp_var_why v
  pp_exp_why e
  | _ -> ()
*)
(*let rec pp_pred_why fmt p =
  Fol.fpp_pred
    pp_pred_why Fol.pp_lvar_why pp_term_why pp_type_why pp_type_hyp_why
    fmt p*)

let pp_type_body fmt = function
  | None -> ()
  | Some t -> Format.fprintf fmt " = %a" pp_type_why t

let pp_type_decl_why fmt tdef =  
  Format.fprintf fmt "type %s %a %a@\n" tdef.Ast.t_name
    (pp_list ~sep:" " pp_type_why) tdef.Ast.t_poly 
    pp_type_body tdef.Ast.t_def

let pp_fct_sig_why fmt (lt, t_res) =
  Format.fprintf fmt "%a : %a"
    (pp_list ~sep:" " pp_type_why) lt pp_type_why t_res 

let pp_function_params = 
  pp_list ~sep:" " (fun fmt v -> Format.fprintf fmt "( %a : %a)"
      PpAst.pp_uid_var v pp_type_why v.Ast.v_type) 

let pp_op_decl_why fmt op =
  if op.Ast.op_native = None then
    let name,_ = op.Ast.op_why in
    match op.Ast.op_body with
    | None -> 
        Format.fprintf fmt "function %s %a@\n" name pp_fct_sig_why op.Ast.op_type
    | Some (params,b) ->
        let tres = snd op.Ast.op_type in
        Format.fprintf fmt "function %s %a : %a = %a@\n"
          name pp_function_params params 
          pp_type_why tres (pp_exp_why PpAst.pp_uid_var) b

let pp_cnst_decl_why fmt c =
  match c.Ast.c_def with
    | None -> Format.fprintf fmt "logic %s : %a@\n" c.Ast.c_name pp_type_why c.Ast.c_type
    | Some e -> Format.fprintf fmt "function %s () : %a = %a@\n"
      c.Ast.c_name pp_type_why c.Ast.c_type (pp_exp_why pp_var_why) e

let pp_easycrypt_why fmt =
  let dir = Filename.dirname Sys.executable_name in
  let dir = Filename.concat dir "src" in
  let in_ch = open_in (Filename.concat dir "easycrypt.why") in
  (try while true do Format.fprintf fmt "%s@\n" (input_line in_ch) done
   with End_of_file -> ());
  close_in in_ch


let pp_axiom_why _fmt (_name, _pred) = ()
(*  Format.fprintf fmt "axiom %s :@\n  %a@\n@\n" name pp_pred_why pred *)

let pp_lvar_decl fmt v =
  Format.fprintf fmt "%a:%a" Fol.pp_lvar_why v pp_type_why (Fol.lv_type v)

let pp_predicate_params = 
  pp_list ~sep:" " (fun fmt v -> Format.fprintf fmt "( %a : %a)"
      Fol.pp_lvar_why v pp_type_why (Fol.lv_type v)) 

let pp_predicate_why _fmt _name (_decls,_def) _opaque =
  ()
(*
  if opaque then
    Format.fprintf fmt "logic %s : %a -> prop@\n@\n" name 
      (pp_list ~sep:", " (fun fmt v -> pp_type_why fmt (Fol.lv_type v))) decls
  else
    Format.fprintf fmt "predicate %s %a = %a@\n@\n" name 
      pp_predicate_params decls
      pp_pred_why def
*)

let pp_goal_why _fmt _name _pred = ()
(*  Format.fprintf fmt "goal %s :@\n  %a@\n" name pp_pred_why pred *)
