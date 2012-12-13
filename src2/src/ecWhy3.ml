(** ----------------------------------------------------------------------*)
open Why3
open EcUtils
open EcIdent
open EcPath
open EcTypes
open EcDecl
open EcFol
open EcTypesmod

let config : Whyconf.config = Whyconf.read_config None

let main : Whyconf.main = Whyconf.get_main config

let w3_env : Env.env = Env.create_env (Whyconf.loadpath main)
    
type env = {
    logic_task : Task.task;
    env_ty : Ty.tysymbol Mp.t;
    env_op : Term.lsymbol Mp.t;
    env_ax : Decl.prsymbol Mp.t;
    env_w3 : EcPath.path Ident.Mid.t;
  }


let empty = {
  logic_task = None;
  env_ty     = Mp.empty;
  env_op     = Mp.empty;
  env_ax     = Mp.empty;
  env_w3     = Ident.Mid.empty;
}


(*------------------------------------------------------------------*)
(** Import why3 theory                                              *)
(*------------------------------------------------------------------*)



let w3_id_string id = id.Ident.id_string

module Wtvm = 
  struct
    type t = EcIdent.t Ty.Mtv.t ref 
    let create () = ref Ty.Mtv.empty 
    let get tvm tv = 
      try Ty.Mtv.find tv !tvm 
      with _ ->
        let id = EcIdent.create (w3_id_string tv.Ty.tv_name) in
        tvm := Ty.Mtv.add tv id !tvm;
        id
  end
      
exception UnknownWhy3Ident of Ident.ident 

let path_of_id env id = 
  try Ident.Mid.find id env.env_w3 
  with _ -> raise (UnknownWhy3Ident id) 

let rec import_w3_ty env tvm ty = 
  match ty.Ty.ty_node with
  | Ty.Tyvar v -> Tvar (Wtvm.get tvm v)
  | Ty.Tyapp(t, args) ->
      let args = List.map (import_w3_ty env tvm) args in
      if Ty.is_ts_tuple t then Ttuple args
      else
        let id = t.Ty.ts_name in
        let path = path_of_id env id in
        Tconstr(path,args)
  
let exists_w3 env id = 
  Ident.Mid.mem id env.env_w3 

let add_w3_ty env p ty = 
  { env with 
    env_ty = Mp.add p ty env.env_ty;
    env_w3 = Ident.Mid.add (ty.Ty.ts_name) p env.env_w3 }

let import_w3_tydef path (env,ld) ty =
  let id = ty.Ty.ts_name in
  if exists_w3 env id then env, ld
  else 
    let tvm = Wtvm.create () in
    let params = List.map (Wtvm.get tvm) ty.Ty.ts_args in
    let def = omap ty.Ty.ts_def (import_w3_ty env tvm) in
    let eid = EcIdent.create (w3_id_string id) in
    let td = { tyd_params = params; tyd_type = def } in
    let p = EcPath.extend (Some path) eid in
    let env = add_w3_ty env p ty in
    env, Th_type (eid,td) :: ld

let force_bool env codom = 
  match codom with
  | None ->  Tconstr(path_of_id env Ty.ts_bool.Ty.ts_name, [])
  | Some t -> t 

let add_w3_ls env p ls = 
  { env with 
    env_op = Mp.add p ls env.env_op;
    env_w3 = Ident.Mid.add (ls.Term.ls_name) p env.env_w3 }

let import_w3_ls path (env,ld) ls = 
  let id = ls.Term.ls_name in
  if exists_w3 env id then env, ld 
  else
    let tvm = Wtvm.create () in
    let dom = List.map (import_w3_ty env tvm) ls.Term.ls_args in
    let codom = omap ls.Term.ls_value (import_w3_ty env tvm) in
    let params = Ty.Stv.elements (Term.ls_ty_freevars ls) in
    let params = List.map (Wtvm.get tvm) params in
    let eid = EcIdent.create (w3_id_string id) in
    let op = { op_params = params;
               op_dom = if dom = [] then None else Some dom;
               op_codom = Some (force_bool env codom);
               op_body = None;
               op_prob = false } in
    let p = EcPath.extend (Some path) eid in
    let env = add_w3_ls env p ls in
    env, Th_operator (eid,op) :: ld
    
let import_w3_constructor path envld (ls, pls) = 
  let envld = import_w3_ls path envld ls in
  List.fold_left (fun envld ols -> 
    match ols with
    | Some ls -> import_w3_ls path envld ls
    | None -> envld) envld pls
    
let import_w3_constructors path = 
  List.fold_left (import_w3_constructor path) 

let import_decl path envld d = 
  match d.Decl.d_node with
  | Decl.Dtype ty -> import_w3_tydef path envld ty 
  | Decl.Ddata ddl ->
      let lty, lc = List.split ddl in
      let envld = List.fold_left (import_w3_tydef path) envld lty in
      List.fold_left (import_w3_constructors path) envld lc 
  | Decl.Dparam ls -> import_w3_ls path envld ls
  | Decl.Dlogic lls ->
      let lls = List.map fst lls in 
      List.fold_left (import_w3_ls path) envld lls
  | Decl.Dind _  -> envld  (* FIXME *)
  | Decl.Dprop _ -> envld  (* FIXME *)

let import_w3 env path th = 
  let task = Task.use_export None th in
  let ths = Ident.Mid.remove th.Theory.th_name (Task.used_theories task) in
  let others = Task.used_symbols ths in
  let decls = Task.local_decls task others in
  let env,ld = List.fold_left (import_decl path) (env,[]) decls in
  let ld = List.rev ld in 
  let env = { env with 
              logic_task = Task.use_export env.logic_task th } in
  let pp_d d = 
    match d with
    | Th_type (id, _)     -> Format.printf "type %s@." (EcIdent.name id)
    | Th_operator (id, _) -> Format.printf "op %s@."   (EcIdent.name id)
    | _                   -> Format.printf "????@." in
  List.iter pp_d ld;
  ld, env

let import_w3_th env path dir s = 
  let th = Env.find_theory w3_env dir s in
  import_w3 env path th 

(*
let _ = 
  let path = EcPath.Pident (EcIdent.create "Top") in
  let _, env = import_w3 empty path Theory.bool_theory in
  let _, env = import_w3 env path Theory.builtin_theory in
  let _ = import_w3_th env path ["int"] "Int" in
  ()
*)

(*------------------------------------------------------------------*)
(* exporting to why3                                                *)
(*------------------------------------------------------------------*)


let add_decl_with_tuples task d =
  let ids = Ident.Mid.set_diff d.Decl.d_syms (Task.task_known task) in
  let add id s = match Ty.is_ts_tuple_id id with
    | Some n -> Stdlib.Sint.add n s
    | None -> s in
  let ixs = Ident.Sid.fold add ids Stdlib.Sint.empty in
  let add n task = Task.use_export task (Theory.tuple_theory n) in
  Task.add_decl (Stdlib.Sint.fold add ixs task) d

let preid id = 
  Ident.id_fresh (EcIdent.name id)

let str_p p = 
  let ls,s = EcPath.toqsymbol p in
  List.fold_right (fun s1 s2 -> s1 ^ "_" ^ s2) ls s
  
let preid_p p = Ident.id_fresh (str_p p)

let create_tvsymbol id = 
  Ty.create_tvsymbol (preid id)

type accum = {
    mutable tvm  : Ty.tvsymbol Mid.t;          
    mutable pvm  : Term.lsymbol Mid.t array;
  }

type vmap = {
    accu : accum;
    lvm  : Term.vsymbol Mid.t;
  }

let empty_vmap () =
  { accu = { tvm = Mid.empty; pvm = Array.make 3 Mid.empty };
    lvm  = Mid.empty } 
      
let trans_tv vm tv = 
  let accu = vm.accu in
  let tvm = accu.tvm in
  try Mid.find tv tvm 
  with _ ->
    let wtv = create_tvsymbol tv in
    let tvm = Mid.add tv wtv tvm in
    accu.tvm <- tvm;
    wtv

(* ------------------------ Types -----------------------------------------*)

let trans_tybase = function
  | Tunit      -> Ty.ty_tuple []
  | Tbool      -> Ty.ty_bool
  | Tint       -> Ty.ty_int
  | Treal      -> Ty.ty_real
  | Tbitstring -> assert false

let trans_pty env p = 
  try Mp.find p env.env_ty 
  with _ -> assert false

let rec trans_ty env vm ty = 
  match ty with
  | Tbase tb -> trans_tybase tb
  | Tunivar _ -> assert false
  | Tvar id -> Ty.ty_var (trans_tv vm id)
  | Ttuple tys -> Ty.ty_tuple (trans_tys env vm tys)
  | Tconstr(p,tys) ->
      let id = trans_pty env p in
      Ty.ty_app id (trans_tys env vm tys)

and trans_tys env vm tys = List.map (trans_ty env vm) tys

let trans_oty env vm oty =
  match oty with
  | None -> None 
  | Some t -> Some (trans_ty env vm t)

let trans_typarams vm tparams = List.map (trans_tv vm) tparams 

let trans_tydecl env path td =
  let pid = preid_p path in
  let vm = empty_vmap () in
  let tparams = trans_typarams vm td.tyd_params in
  let body = omap td.tyd_type (trans_ty env vm) in
  Ty.create_tysymbol pid tparams body 

let add_ty env path td =
  assert (not (Mp.mem path env.env_ty));
  let ty = trans_tydecl env path td in
  let decl = Decl.create_ty_decl ty in
  { env with 
    env_ty = Mp.add path ty env.env_ty;
    logic_task = add_decl_with_tuples env.logic_task decl }

(*------------------------- Expressions-------------------------------------*)

let check_side accu side = 
  if Array.length accu.pvm <= side then
    let pvm = Array.make (side + 1) Mid.empty in
    Array.iteri (fun i m -> pvm.(i) <- m) accu.pvm;
    accu.pvm <- pvm

let trans_pv env vm (p,ty) side =
  (* FIXME ensure that ty is closed *)
  let accu = vm.accu in
  check_side accu side;
  let pvm = accu.pvm.(side) in
  let id = EcPath.basename p in
  try Mid.find id pvm 
  with _ ->
    let wid = Ident.id_fresh (str_p p ^ string_of_int side) in
    let ty = trans_ty env vm ty in
    let ls = Term.create_lsymbol wid [] (Some ty) in
    accu.pvm.(side) <- Mid.add id ls pvm;
    ls

let trans_lv vm lv = 
  try Mid.find lv vm.lvm 
  with _ -> assert false

let create_vsymbol id ty = Term.create_vsymbol (preid id) ty 

let add_id vm id ty =
  assert (not (Mid.mem id vm.lvm));
  let wid = create_vsymbol id ty in
  let vm = { vm with
             lvm = Mid.add id wid vm.lvm } in
  wid, vm

let add_ids vm ids lty = 
  assert (List.length lty = List.length ids);
  let vm = ref vm in
  let wids = 
    List.map2 (fun id ty -> let wid, vm' = add_id !vm id ty in vm := vm'; wid)
      ids lty in
  wids, !vm

let t_app p args ty =
  if p.Term.ls_value = None then Term.t_app p args None
  else Term.t_app p args (Some ty)
    
let prop_of_bool t = 
  assert (Ty.oty_equal t.Term.t_ty (Some Ty.ty_bool));
  match t.Term.t_node with
  | Term.Tif(t1,t2,t3) when 
      Term.t_equal t2 Term.t_bool_true &&
      Term.t_equal t3 Term.t_bool_false -> t1
  | _ ->
      if Term.t_equal t Term.t_bool_true then Term.t_true
      else if Term.t_equal t Term.t_bool_false then Term.t_false 
      else Term.t_equ t Term.t_bool_true

let force_prop t = 
  if t.Term.t_ty = None then t
  else prop_of_bool t

let bool_of_prop t = 
  assert (t.Term.t_ty = None);
  match t.Term.t_node with
  | Term.Ttrue -> Term.t_bool_true
  | Term.Tfalse -> Term.t_bool_false
  | Term.Tapp(ls,[t;tt]) when
      Term.t_equal tt Term.t_bool_true && 
      Term.ls_equal ls Term.ps_equ -> t
  | _ -> 
      Term.t_if t Term.t_bool_true Term.t_bool_false 

let trans_op env p = 
  try Mp.find p env.env_op with _ -> assert false

exception RandExpr

let destr_ty_tuple t =
  match t.Ty.ty_node with
  | Ty.Tyapp (ts, lt) -> assert (Ty.is_ts_tuple ts); lt
  | _ -> assert false 

let rec trans_expr env vm e =
  match e with
  | Eunit  -> Term.t_tuple [] 
  | Ebool b -> if b then Term.t_true else Term.t_false 
  | Eint n -> 
      let n = Term.ConstInt(Term.IConstDecimal (string_of_int n)) in
      Term.t_const n 
  | Eflip | Einter _ | Ebitstr _ | Eexcepted _ -> raise RandExpr
  | Elocal(id,_) -> Term.t_var (trans_lv vm id) 
  | Evar(p,ty) -> 
      (* FIXME should assert false *)
      Term.t_app_infer (trans_pv env vm (p,ty) 0) [] 
  | Eapp(p,args, ty) -> 
      let p = trans_op env p in
      let ty = trans_ty env vm ty in
      let args = List.map (trans_expr_b env vm) args in 
      t_app p args ty
  | Elet(lp,e1,e2) ->
      let e1 = trans_expr_b env vm e1 in
      begin match lp with
      | LSymbol id -> 
          let id, vm = add_id vm id (Term.t_type e1) in
          let e2 = trans_expr env vm e2 in
          Term.t_let e1 (Term.t_close_bound id e2)
      | LTuple ids ->
          let t1 = Term.t_type e1 in
          let ids, vm = add_ids vm ids (destr_ty_tuple t1) in
          let pat = 
            Term.pat_app (Term.fs_tuple (List.length ids)) 
              (List.map Term.pat_var ids) t1 in
          let e2 = trans_expr env vm e2 in
          let br = Term.t_close_branch pat e2 in
          Term.t_case e1 [br] 
      end
  | Etuple args ->
    let args = List.map (trans_expr_b env vm) args in
    Term.t_tuple args 
  | Eif(e1,e2,e3) ->
      let e1 = trans_expr env vm e1 in
      let e2 = trans_expr env vm e2 in
      let e3 = trans_expr env vm e3 in
      Term.t_if (force_prop e1) e2 e3 

and trans_expr_b env vm e = 
  let t = trans_expr env vm e in
  if t.Term.t_ty = None then bool_of_prop t else t

let trans_bop op t1 t2 = (* FIXME once asym Land and Lor *)
  let t1 = force_prop t1 in
  let t2 = force_prop t2 in
  match op with
  | Land -> Term.t_and_simp t1 t2
  | Lor  -> Term.t_or_simp t1 t2 
  | Limp -> Term.t_implies_simp t1 t2 
  | Liff -> Term.t_iff_simp t1 t2 
  
let trans_quant = function
  | Lforall -> Term.Tforall
  | Lexists -> Term.Texists

let rec trans_form env vm f =
  match f.f_node with
  | Ftrue  -> Term.t_true
  | Ffalse -> Term.t_false
  | Fnot f -> Term.t_not_simp (trans_form env vm f)
  | Fbinop(f1,op,f2) ->
      let f1 = trans_form env vm f1 in
      let f2 = trans_form env vm f2 in
      trans_bop op f1 f2 
  | Fquant(q,b,f) ->
      let ids, tys = List.split b in
      let tys = trans_tys env vm tys in
      let vs, vm = add_ids vm ids tys in
      let f = trans_form env vm f in
      Term.t_quant_close (trans_quant q) vs [] f
  | Fif(f1,f2,f3) ->
      let f1 = trans_form env vm f1 in
      let f2 = trans_form env vm f2 in
      let f3 = trans_form env vm f3 in
      Term.t_if_simp (force_prop f1) f2 f3
  | Flet(lp,f1,f2) ->
      let f1 = trans_form_b env vm f1 in
      begin match lp with
      | LSymbol id -> 
          let id, vm = add_id vm id (Term.t_type f1) in
          let f2 = trans_form env vm f2 in
          Term.t_let f1 (Term.t_close_bound id f2)
      | LTuple ids ->
          let t1 = Term.t_type f1 in
          let ids, vm = add_ids vm ids (destr_ty_tuple t1) in
          let pat = 
            Term.pat_app (Term.fs_tuple (List.length ids)) 
              (List.map Term.pat_var ids) t1 in
          let f2 = trans_form env vm f2 in
          let br = Term.t_close_branch pat f2 in
          Term.t_case f1 [br] 
      end
  | Funit -> Term.t_tuple [] 
  | Fint n ->
      let n = Term.ConstInt(Term.IConstDecimal (string_of_int n)) in
      Term.t_const n 
  | Flocal id -> Term.t_var (trans_lv vm id) 
  | Fpvar(p,ty,s) ->  Term.t_app_infer (trans_pv env vm (p,ty) s) [] 
  | Fapp(p,args) ->
      let ty = trans_ty env vm f.f_ty in
      let p = trans_op env p in
      let args = List.map (trans_form_b env vm) args in 
      t_app p args ty 
  | Ftuple args ->
      let args = List.map (trans_form_b env vm) args in
      Term.t_tuple args

and trans_form_b env vm f = 
  let t = trans_form env vm f in
  if t.Term.t_ty = None then bool_of_prop t else t

let trans_op_body env vm ls = function
  | None -> Decl.create_param_decl ls 
  | Some (OB_op(ids,body)) ->
      let ids, vm = add_ids vm ids ls.Term.ls_args in
      let e = trans_expr env vm body in
      let e = 
        if ls.Term.ls_value = None then force_prop e else e in
      Decl.create_logic_decl [Decl.make_ls_defn ls ids e]
  | Some(OB_pr(ids,body)) ->
      let ids,vm = add_ids vm ids ls.Term.ls_args in
      let e = force_prop (trans_form env vm body) in 
      Decl.create_logic_decl [Decl.make_ls_defn ls ids e]

let trans_op env path op = 
  assert (not op.op_prob);
  let vm = empty_vmap () in
  let _ = trans_typarams vm op.op_params in
  let pid = preid_p path in
  let dom = odfl [] (omap op.op_dom (trans_tys env vm)) in
  let codom = trans_oty env vm op.op_codom in
  let codom = if Ty.oty_equal codom (Some Ty.ty_bool) then None else codom in
  let ls = Term.create_lsymbol pid dom codom in
  ls, trans_op_body env vm ls op.op_body 






let add_op env path op =
  if op.op_prob then env 
  else
    let ls, decl = trans_op env path op in
    { env with
      env_op = Mp.add path ls env.env_op;
      logic_task = add_decl_with_tuples env.logic_task decl
    }

let add_ax env path ax =
  let pr = Decl.create_prsymbol (preid_p path) in
  let vm = empty_vmap () in 
  let f = trans_form env vm ax.ax_spec in
  let decl = Decl.create_prop_decl Decl.Paxiom pr f in
  { env with
    env_ax = Mp.add path pr env.env_ax;
    logic_task = add_decl_with_tuples env.logic_task decl }









