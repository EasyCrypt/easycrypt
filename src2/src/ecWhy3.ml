(** ----------------------------------------------------------------------*)
open Why3
open EcUtils
open EcIdent
open EcPath
open EcTypes
open EcDecl
open EcFol

let config : Whyconf.config = Whyconf.read_config None

let main : Whyconf.main = Whyconf.get_main config

let env : Env.env = Env.create_env (Whyconf.loadpath main)

type env = {
    logic_task : Task.task;
    env_ty : Ty.tysymbol Mp.t;
    env_op : Term.lsymbol Mp.t;
    env_ax : Decl.prsymbol Mp.t;
  }

let empty = {
  logic_task = None;
  env_ty     = Mp.empty;
  env_op     = Mp.empty;
  env_ax     = Mp.empty;
}

let preid id = 
  Ident.id_fresh (EcIdent.name id)

let create_tvsymbol id = 
  Ty.create_tvsymbol (preid id)

let trans_pty env p = 
  try Mp.find p env.env_ty 
  with _ -> assert false

let trans_tybase = function
  | Tunit      -> Ty.ty_tuple []
  | Tbool      -> Ty.ty_bool
  | Tint       -> Ty.ty_int
  | Treal      -> Ty.ty_real
  | Tbitstring -> assert false

let rec trans_ty env tvmap ty = 
  match ty with
  | Tbase _ -> assert false (* FIXME *)
  | Tunivar _ -> assert false
  | Tvar id -> 
     let tv, tvmap = Mid.get_upd create_tvsymbol id tvmap in
     Ty.ty_var tv, tvmap
  | Ttuple tys -> 
      let tys, tvmap = trans_tys env tvmap tys in
      Ty.ty_tuple tys, tvmap
  | Tconstr(p,tys) ->
      let tys, tvmap = trans_tys env tvmap tys in
      let id = trans_pty env p in
      Ty.ty_app id tys, tvmap

and trans_tys env tvmap tys =
  let tvmap = ref tvmap in
  let f ty = 
    let ty,vm = trans_ty env !tvmap ty in 
    tvmap := vm; ty in
  let tys = List.map f tys in
  tys, !tvmap

let trans_typarams tvmap tparams = 
  let tvmap = ref tvmap in
  let f id = 
    let v, vm = Mid.get_upd create_tvsymbol id !tvmap in
    tvmap := vm; v in
  let tparams = List.map f tparams in
  tparams, !tvmap 

let trans_tydecl env path td =
  let pid = preid (EcPath.basename path) in
  let tparams, tvmap = trans_typarams Mid.empty td.tyd_params in
  let body = omap td.tyd_type (fun ty -> fst(trans_ty env tvmap ty)) in
  Ty.create_tysymbol pid tparams body 

let add_ty env path td =
  assert (not (Mp.mem path env.env_ty));
  let ty = trans_tydecl env path td in
  { env with 
    env_ty = Mp.add path ty env.env_ty;
    logic_task = Task.add_ty_decl env.logic_task ty       
  }

module VM = struct
  type t = Term.vsymbol Mid.t
  let get_id id vm = 
    try Mid.find id vm with _ -> assert false
  let get_path p vm = 
    try Mid.find (EcPath.basename p) vm with _ -> assert false

  let create_vsymbol id ty = Term.create_vsymbol (preid id) ty 

  let add_id id ty vm = 
    assert (not (Mid.mem id vm));
    let wid = create_vsymbol id ty in
    wid, Mid.add id wid vm

  let add_ids ids lt vm = 
    assert (List.length lt = List.length ids);
    let r = ref vm in
    let f id t = 
      let id, vm = add_id id t !r in
      r := vm; id in
    let ids = List.map2 f ids lt in
    ids, !r
    
end 

exception RandExpr

let destr_ty_tuple t =
  match t.Ty.ty_node with
  | Ty.Tyapp (ts, lt) -> assert (Ty.is_ts_tuple ts); lt
  | _ -> assert false 

let trans_op env p = 
  try Mp.find p env.env_op with _ -> assert false

let form_of_bool e = 
  if Term.t_equal e Term.t_bool_true then Term.t_true
  else if Term.t_equal e Term.t_bool_false then Term.t_false 
  else Term.t_equ e Term.t_bool_true
  
let rec trans_expr env tvm vm e =
  match e with
  | Eunit  -> Term.t_tuple [] 
  | Ebool b -> if b then Term.t_bool_true else Term.t_bool_false 
  | Eint n -> 
      let n = Term.ConstInt(Term.IConstDecimal (string_of_int n)) in
      Term.t_const n 
  | Eflip | Einter _ | Ebitstr _ | Eexcepted _ -> raise RandExpr
  | Elocal(id,_) -> Term.t_var (VM.get_id id vm)
  | Evar(p,_) -> Term.t_var (VM.get_path p vm)
        (* FIXME should be assert false *)
  | Eapp(p,args) -> 
      let p = trans_op env p in
      let args = List.map (trans_expr env tvm vm) args in (* FIXME tvm *)
      Term.t_app_infer p args (* FIXME : use t_app *)
  | Elet(lp,e1,e2) ->
      (* FIXME type *)
      let e1 = trans_expr env tvm vm e1 in
      begin match lp with
      | LSymbol id -> 
          let id, vm = VM.add_id id (Term.t_type e1) vm in
          let e2 = trans_expr env tvm vm e2 in
          Term.t_let e1 (Term.t_close_bound id e2)
      | LTuple ids ->
          let t1 = Term.t_type e1 in
          let ids, vm = VM.add_ids ids (destr_ty_tuple t1) vm in
          let pat = 
            Term.pat_app (Term.fs_tuple (List.length ids)) 
              (List.map Term.pat_var ids) t1 in
          let e2 = trans_expr env tvm vm e2 in
          let br = Term.t_close_branch pat e2 in
          Term.t_case e1 [br] 
      end
  | Etuple args ->
    let args = List.map (trans_expr env tvm vm) args in
    Term.t_tuple args 
  | Eif(e1,e2,e3) ->
      let e1 = trans_expr env tvm vm e1 in
      let e2 = trans_expr env tvm vm e2 in
      let e3 = trans_expr env tvm vm e3 in
      Term.t_if (form_of_bool e1) e2 e3

let trans_bop op t1 t2 = (* FIXME once asym Land and Lor *)
  match op with
  | Land -> Term.t_and t1 t2
  | Lor  -> Term.t_or t1 t2 
  | Limp -> Term.t_implies t1 t2 
  | Liff -> Term.t_iff t1 t2 
  
let trans_quant = function
  | Lforall -> Term.Tforall
  | Lexists -> Term.Texists

let trans_oty env tvm oty =
  match oty with
  | None -> None, tvm 
  | Some t -> let t,tvm = trans_ty env tvm t in Some t, tvm 

let rec trans_form env tvm lm pvm f =
  match f with
  | Ftrue -> Term.t_true
  | Ffalse -> Term.t_false
  | Fnot f -> 
      Term.t_not (trans_form env tvm lm pvm f)
  | Fbinop(f1,op,f2) ->
      let f1 = trans_form env tvm lm pvm f1 in
      let f2 = trans_form env tvm lm pvm f2 in
      trans_bop op f1 f2 
  | Fquant(q,b,f) ->
      let ids, tys = List.split b in
      let tys, tvm = trans_tys env tvm tys in
      let vs, lm = VM.add_ids ids tys lm in
      let f = trans_form env tvm lm pvm f in
      Term.t_quant_close (trans_quant q) vs [] f
  | Fif(f1,f2,f3) ->
      let f1 = trans_form env tvm lm pvm f1 in
      let f2 = trans_form env tvm lm pvm f2 in
      let f3 = trans_form env tvm lm pvm f3 in
      Term.t_if f1 f2 f3
  | Flet(lp,f1,f2) ->
      let f1 = trans_form env tvm lm pvm f1 in
      begin match lp with
      | LFPSymbol(id, ty) -> 
          let id, lm = VM.add_id id (Term.t_type f1) lm in
          let f2 = trans_form env tvm lm pvm f2 in
          Term.t_let f1 (Term.t_close_bound id f2)
      | LFPTuple ids ->
          let t1 = Term.t_type f1 in
          let ids, lm = VM.add_ids (List.map fst ids) (destr_ty_tuple t1) lm in
          let pat = 
            Term.pat_app (Term.fs_tuple (List.length ids)) 
              (List.map Term.pat_var ids) t1 in
          let f2 = trans_form env tvm lm pvm f2 in
          let br = Term.t_close_branch pat f2 in
          Term.t_case f1 [br] 
      end
  | Funit -> Term.t_tuple [] 
  | Fbool b -> if b then Term.t_bool_true else Term.t_bool_false
  | Fint n ->
      let n = Term.ConstInt(Term.IConstDecimal (string_of_int n)) in
      Term.t_const n 
  | Flocal(id, _) -> Term.t_var (VM.get_id id lm)
  | Fpvar _ -> assert false (* FIXME *)
  | Fapp(p,args, oty) ->
      let oty,tvm = trans_oty env tvm oty in
      let p = trans_op env p in
      let args = List.map (trans_form env tvm lm pvm) args in (* FIXME tvm *)
      Term.t_app p args oty (* FIXME : use t_app *)
  | Ftuple args ->
      let args = List.map (trans_form env tvm lm pvm) args in (* FIXME tvm *)
      Term.t_tuple args
  | Fofbool f -> 
      let f = trans_form env tvm lm pvm f in
      form_of_bool f 

let trans_op_body env tvm ls = function
  | None -> Decl.create_param_decl ls 
  | Some (OB_op(ids,body)) ->
      let ids, lm = VM.add_ids ids ls.Term.ls_args Mid.empty in
      let e = trans_expr env tvm lm body in
      Decl.create_logic_decl [Decl.make_ls_defn ls ids e]
  | Some(OB_pr(ids,body)) ->
      let ids, lm = VM.add_ids ids ls.Term.ls_args Mid.empty in
      let e = trans_form env tvm lm () body in (* FIXME () *)
      Decl.create_logic_decl [Decl.make_ls_defn ls ids e]
  
let trans_op env path op = 
  assert (not op.op_prob);
  let _, tvm = trans_typarams Mid.empty op.op_params in
  let pid = preid (EcPath.basename path) in
  let dom, tvm = odfl ([],tvm) (omap op.op_dom (trans_tys env tvm)) in
  let codom, tvm = trans_oty env tvm op.op_codom in
  let ls = Term.create_lsymbol pid dom codom in
  ls, trans_op_body env tvm ls op.op_body 

let add_op env path op =
  if op.op_prob then env 
  else
    let ls, decl = trans_op env path op in
    { env with
      env_op = Mp.add path ls env.env_op;
      logic_task = Task.add_decl env.logic_task decl
    }

let add_ax env path ax =
  let pr = Decl.create_prsymbol (preid (EcPath.basename path)) in
  let f = trans_form env Mid.empty Mid.empty () ax.ax_spec in
  let decl = Decl.create_prop_decl Decl.Paxiom pr f in
  { env with
    env_ax = Mp.add path pr env.env_ax;
    logic_task = Task.add_decl env.logic_task decl
  }








