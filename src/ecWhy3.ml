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

let get_w3_th = Env.find_theory w3_env
    
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

type rebinding_w3 = {
    rb_th   : Theory.theory;
    rb_ty   : Ty.tysymbol Mp.t;
    rb_op   : Term.lsymbol Mp.t;
    rb_ax   : Decl.prsymbol Mp.t;
    rb_w3   : EcPath.path Ident.Mid.t;
  }

type rebinding_item = 
  | RBuse of rebinding_w3
  | RBty  of EcPath.path * Ty.tysymbol * Decl.decl
  | RBop  of EcPath.path * Term.lsymbol * Decl.decl
  | RBax  of EcPath.path * Decl.prsymbol * Decl.decl

type rebinding = rebinding_item list

let merge check k o1 o2 = 
  match o1, o2 with
  | None, _ -> o2
  | Some _, None -> o1
  | Some e1, Some e2 -> check k e1 e2; o1

exception MergeW3Ty of EcPath.path * Ty.tysymbol * Ty.tysymbol
exception MergeW3Op of EcPath.path * Term.lsymbol * Term.lsymbol
exception MergeW3Ax of EcPath.path * Decl.prsymbol * Decl.prsymbol
exception MergeW3Id of Ident.ident * EcPath.path * EcPath.path

let merge_ty = 
  let check p t1 t2 = 
    if not (Ty.ts_equal t1 t2) then raise (MergeW3Ty(p,t1,t2)) in
  Mp.merge (merge check)

let merge_op =
  let check p t1 t2 = 
    if not (Term.ls_equal t1 t2) then raise (MergeW3Op(p,t1,t2)) in
  Mp.merge (merge check)

let merge_ax = 
  let check p t1 t2 = 
    if not (Decl.pr_equal t1 t2) then raise (MergeW3Ax(p,t1,t2)) in
  Mp.merge (merge check)

let merge_id = 
  let check p t1 t2 = 
    if not (EcPath.p_equal t1 t2) then raise (MergeW3Id(p,t1,t2)) in
  Ident.Mid.merge (merge check)

let add_decl_with_tuples task d =
  let ids = Ident.Mid.set_diff d.Decl.d_syms (Task.task_known task) in
  let add id s = match Ty.is_ts_tuple_id id with
    | Some n -> Stdlib.Sint.add n s
    | None -> s in
  let ixs = Ident.Sid.fold add ids Stdlib.Sint.empty in
  let add n task = Task.use_export task (Theory.tuple_theory n) in
  Task.add_decl (Stdlib.Sint.fold add ixs task) d

let add_ts env path ts decl =
  if Mp.mem path env.env_ty then 
    (assert (Ty.ts_equal ts (Mp.find path env.env_ty)); env)
  else 
    { env with 
      env_ty = Mp.add path ts env.env_ty;
      logic_task = add_decl_with_tuples env.logic_task decl }

let add_ls env path ls decl =
  if Mp.mem path env.env_op then 
    (assert (Term.ls_equal ls (Mp.find path env.env_op)); env)
  else 
    { env with 
      env_op = Mp.add path ls env.env_op;
      logic_task = add_decl_with_tuples env.logic_task decl }

let add_pr env path pr decl =
  if Mp.mem path env.env_ax then 
    (assert (Decl.pr_equal pr (Mp.find path env.env_ax)); env)
  else 
    { env with 
      env_ax = Mp.add path pr env.env_ax;
      logic_task = add_decl_with_tuples env.logic_task decl }

let rebind_item env = function
  | RBuse w3 ->
      { logic_task = Task.use_export env.logic_task w3.rb_th;
        env_ty = merge_ty env.env_ty w3.rb_ty;
        env_op = merge_op env.env_op w3.rb_op;
        env_ax = merge_ax env.env_ax w3.rb_ax;
        env_w3 = merge_id env.env_w3 w3.rb_w3;
      }
  | RBty(p,ts,decl) -> add_ts env p ts decl
  | RBop(p,ls,decl) -> add_ls env p ls decl
  | RBax(p,pr,decl) -> add_pr env p pr decl

let rebind = List.fold_left rebind_item

(*------------------------------------------------------------------*)
(** Import why3 theory                                              *)
(*------------------------------------------------------------------*)

type renaming_kind =
  | RDts 
  | RDls
  | RDpr

type renaming_decl = (string list * renaming_kind * EcIdent.t) list

let w3_id_string id = id.Ident.id_string

module Renaming = struct 

  type renaming = {
      r_ts : EcIdent.t Ty.Mts.t;
      r_ls : EcIdent.t Term.Mls.t;
      r_pr : EcIdent.t Decl.Mpr.t
    }

  let init rd th = 
    let ns = th.Theory.th_export in
    let rec aux ts ls pr rd = 
      match rd with
      | [] -> { r_ts = ts; r_ls = ls; r_pr = pr }
      | (p,RDts,id) :: rd ->
          let ts = Ty.Mts.add (Theory.ns_find_ts ns p) id ts in
          aux ts ls pr rd
      | (p,RDls,id) :: rd ->
          let ls = Term.Mls.add (Theory.ns_find_ls ns p) id ls in
          aux ts ls pr rd 
      | (p,RDpr,id)::rd -> 
          let pr = Decl.Mpr.add (Theory.ns_find_pr ns p) id pr in
          aux ts ls pr rd in
    aux Ty.Mts.empty Term.Mls.empty Decl.Mpr.empty rd

  let get_ts rn ts = 
    try Ty.Mts.find ts rn.r_ts 
    with _ -> 
      let id = ts.Ty.ts_name in
      EcIdent.create (w3_id_string id)

  let remove_infix s =
    let len = String.length s in
    if len < 7 then s else
    let inf = String.sub s 0 6 in
    if inf = "infix "  then String.sub s 6 (len - 6) else
    let prf = String.sub s 0 7 in
    if prf = "prefix " then String.sub s 7 (len - 7) else
    if s = "mixfix []" then EcCoreLib.s_get else
    if s = "mixfix [<-]" then EcCoreLib.s_set else 
    s
    
  let get_ls rn ls = 
    try Term.Mls.find ls rn.r_ls 
    with _ ->
      let id = ls.Term.ls_name in
      let s  = remove_infix (w3_id_string id) in
      EcIdent.create s

  let get_pr rn pr = 
    try Decl.Mpr.find pr rn.r_pr 
    with _ ->
      let id = pr.Decl.pr_name in
      EcIdent.create (w3_id_string id)
end
      
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

type zipper_elem =
  | Zenter of EcIdent.t 
  | Zdecl  of theory_item 

and zipper = zipper_elem list 

let import_w3_tydef rn path (env,rb,z) ty =
  let tvm = Wtvm.create () in
  let params = List.map (Wtvm.get tvm) ty.Ty.ts_args in
  let def = omap ty.Ty.ts_def (import_w3_ty env tvm) in
  let eid = Renaming.get_ts rn ty in
  let td = { tyd_params = params; tyd_type = def } in
  let p = EcPath.extend (Some path) eid in
  let env = add_w3_ty env p ty in
  let rb  = add_w3_ty env p ty in
  env, rb, Zdecl(Th_type (eid,td)) :: z

let force_bool env codom = 
  match codom with
  | None ->  EcTypes.tbool
  | Some t -> t 

exception CanNotTranslate
exception UnboundLS of Term.lsymbol

let import_w3_quant = function
  | Term.Tforall -> Lforall
  | Term.Texists -> Lexists

let import_w3_term env tvm =
  let memo = Ty.Hty.memo 37 (import_w3_ty env tvm) in
  let import_ty ty = 
    match ty with
    | None -> EcTypes.tbool
    | Some t -> memo t in
  let add_local v vm = 
    let id = EcIdent.create (w3_id_string v.Term.vs_name) in
    let ty = import_ty (Some v.Term.vs_ty) in
    (id,ty), Term.Mvs.add v id vm in
  let add_locals vs vm = 
    let r = ref vm in
    let its = List.map (fun v -> let (d,vm) = add_local v !r in r := vm; d) vs in
    its, !r in
(*  let tmemo = Term.Hterm.create 37 in *)
  let rec import vm t =
(*    try Term.Hterm.find tmemo t 
    with _ ->
      let f = *)
        match t.Term.t_node with
        | Term.Tvar v -> f_local (Term.Mvs.find v vm) (import_ty t.Term.t_ty)
        | Term.Tconst _ -> raise CanNotTranslate (* FIXME *)
        | Term.Tapp(f,args) ->
            let args = List.map (import vm) args in
            if Term.is_fs_tuple f then f_tuple args
            else 
              let f = 
                try Ident.Mid.find f.Term.ls_name env.env_w3 
                with _ -> raise (UnboundLS f) in
              let ty = import_ty t.Term.t_ty in
              f_app_t f args ty
        | Term.Tif(t1,t2,t3) ->
          let f1 = import vm t1 in
          let f2 = import vm t2 in
          let f3 = import vm t3 in
          f_if f1 f2 f3
        | Term.Tlet(e,tb) ->
            let f1 = import vm e in
            let v, t = Term.t_open_bound tb in
            let (id,_), vm = add_local v vm in
            let f2 = import vm t in
            f_let (LSymbol id) f1 f2
        | Term.Tcase _ -> raise CanNotTranslate (* FIXME : tuple *)
        | Term.Teps _ ->  raise CanNotTranslate 
        | Term.Tquant(q,tq) ->
            let vs,_,t = Term.t_open_quant tq in 
            let ids, vm = add_locals vs vm in
            let f = import vm t in
            f_quant (import_w3_quant q) ids f
        | Term.Tbinop(op,t1,t2) ->
            let f1 = import vm t1 in
            let f2 = import vm t2 in
            (* FIXME : and asym ... *)
            begin match op with
            | Term.Tand     -> f_and f1 f2
            | Term.Tor      -> f_or  f1 f2
            | Term.Timplies -> f_imp f1 f2
            | Term.Tiff     -> f_iff f1 f2
            end
        | Term.Tnot t -> f_not (import vm t)
        | Term.Ttrue  -> f_true
        | Term.Tfalse -> f_false

(*in
      Term.Hterm.add tmemo t f;
      f*) in
  import_ty, add_locals, import 

let add_w3_ls env p ls = 
  { env with 
    env_op = Mp.add p ls env.env_op;
    env_w3 = Ident.Mid.add (ls.Term.ls_name) p env.env_w3 }

let import_w3_ls rn path (env,rb,z) ls = 
  let tvm = Wtvm.create () in
  let dom = List.map (import_w3_ty env tvm) ls.Term.ls_args in
  let codom = omap ls.Term.ls_value (import_w3_ty env tvm) in
  let params = Ty.Stv.elements (Term.ls_ty_freevars ls) in
  let params = List.map (Wtvm.get tvm) params in
  let eid = Renaming.get_ls rn ls in
  let op = { op_params = params;
             op_dom = if dom = [] then None else Some dom;
             op_codom = Some (force_bool env codom);
             op_body = None;
             op_prob = false } in
  let p = EcPath.extend (Some path) eid in
  let env = add_w3_ls env p ls in
  let rb  = add_w3_ls env p ls in
  env, rb, Zdecl (Th_operator (eid,op)) :: z
    
let import_w3_constructor rn path envld (ls, pls) = 
  let envld = import_w3_ls rn path envld ls in
  List.fold_left (fun envld ols -> 
    match ols with
    | Some ls -> import_w3_ls rn path envld ls
    | None -> envld) envld pls
    
let import_w3_constructors rn path = 
  List.fold_left (import_w3_constructor rn path) 

let add_w3_pr env p pr = 
  { env with 
    env_ax = Mp.add p pr env.env_ax;
    env_w3 = Ident.Mid.add (pr.Decl.pr_name) p env.env_w3 }

let import_w3_pr rn path (env,rb, z as envld) k pr t =
  match k with
  | Decl.Plemma | Decl.Paxiom ->
      let eid = Renaming.get_pr rn pr in
      let _, _, import = import_w3_term env (Wtvm.create()) in
      let spec = 
        try Some (import Term.Mvs.empty t);
        with CanNotTranslate -> None in
      let ax = { ax_spec = spec;
                 ax_kind = if k = Decl.Plemma then Lemma else Axiom } in
      let p = EcPath.extend (Some path) eid in
      let env = add_w3_pr env p pr in
      let rb  = add_w3_pr env p pr in
      env, rb, Zdecl(Th_axiom (eid,ax)) :: z
  | Decl.Pgoal | Decl.Pskip -> envld


let import_decl rn path envld d = 
  match d.Decl.d_node with
  | Decl.Dtype ty -> import_w3_tydef rn path envld ty 
  | Decl.Ddata ddl ->
      let lty, lc = List.split ddl in
      let envld = List.fold_left (import_w3_tydef rn path) envld lty in
      List.fold_left (import_w3_constructors rn path) envld lc 
  | Decl.Dparam ls -> import_w3_ls rn path envld ls
  | Decl.Dlogic lls ->
      let lls = List.map fst lls in 
      List.fold_left (import_w3_ls rn path) envld lls
  | Decl.Dind _  -> envld  (* FIXME *)
  | Decl.Dprop (k,pr,t) -> import_w3_pr rn path envld k pr t 

let import_decls rn path env decls =
  let rec diff ls ls' = 
    match ls, ls' with
    | s::ls, s'::ls' when s = s' -> diff ls ls'
    | _, _ -> List.rev ls, ls' in
  let rec close accu ls path z = 
    match ls, z, path with
    | [], _, _ -> path, z 
    | s::ls, Zenter id:: z, EcPath.Pqname(p,id') ->
        assert (s=EcIdent.name id && EcIdent.id_equal id id');
        close [] ls p (Zdecl (Th_theory (id,accu)) :: z)
    | s::ls, Zenter id:: z, _ -> assert false
    | _, Zdecl d::z, _ -> close (d::accu) ls path z
    | _, [], _ -> assert false in
  let open_ ls path z = 
    List.fold_left (fun (path, z) s -> 
      let id = EcIdent.create s in
      EcPath.extend (Some path) id, Zenter id :: z) (path,z) ls in
  let close_open ls ls' path z = 
    let ls, ls' = diff ls ls' in
    let path, z = close [] ls path z in
    open_ ls' path z in 
  let rec aux ls path (env,rb,z as envld) decls = 
    match decls with
    | d::decls ->
        let ids = d.Decl.d_news in
        if Ident.Sid.is_empty ids then aux ls path envld decls
        else
          let id = Ident.Sid.choose ids in
          let (_,_,s) = Theory.restore_path id in
          let ls' = List.rev (List.tl (List.rev s)) in
          let path, z = close_open ls ls' path z in
          let envld = import_decl rn path (env,rb,z) d in
          aux ls' path envld decls 
    | [] -> 
        let final_close z = 
          List.rev_map (function Zdecl d -> d | _ -> assert false) z in
        let _, z = close [] ls path z in
        (env,rb,final_close z) in
  aux [] path (env,empty, []) decls

let import_w3 env path th rd =
  let rn = Renaming.init rd th in
  let task = Task.use_export None th in
  let ths = Ident.Mid.remove th.Theory.th_name (Task.used_theories task) in
  let others = Task.used_symbols ths in
  let decls = Task.local_decls task others in
  let env,rb, ld =  import_decls rn path env decls in
  let rb = 
    { rb_th   = th;
      rb_ty   = rb.env_ty;
      rb_op   = rb.env_op;
      rb_ax   = rb.env_ax;
      rb_w3   = rb.env_w3;
    } in
  ld, RBuse rb

(*------------------------------------------------------------------*)
(* exporting to why3                                                *)
(*------------------------------------------------------------------*)


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

let trans_pty env p = 
  try Mp.find p env.env_ty 
  with _ -> assert false

let rec trans_ty env vm ty = 
  match ty with
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

let force_bool t = 
  if t.Term.t_ty = None then bool_of_prop t
  else t

type op_kind = 
  | OK_true
  | OK_false
  | OK_not
  | OK_and
  | OK_or
  | OK_imp
  | OK_iff
  | OK_eq
  | OK_other 

let op_kind = 
  let l = [EcCoreLib.p_true, OK_true; EcCoreLib.p_false, OK_false;
           EcCoreLib.p_not, OK_not; 
           EcCoreLib.p_and, OK_and; EcCoreLib.p_or, OK_or; 
           EcCoreLib.p_imp, OK_imp; EcCoreLib.p_iff, OK_iff;
           EcCoreLib.p_eq, OK_eq] in
  let m = List.fold_left (fun m (p,k) -> Mp.add p k m) Mp.empty l in
  fun p -> try Mp.find p m with _ -> OK_other

let trans_op env p args ty = 
  match op_kind p, args with
  | OK_true , []      -> Term.t_true
  | OK_false, []      -> Term.t_false
  | OK_not  , [e]     -> Term.t_not (force_prop e)
  | OK_and  , [e1;e2] -> Term.t_and (force_prop e1) (force_prop e2)
  | OK_or   , [e1;e2] -> Term.t_or  (force_prop e1) (force_prop e2)
  | OK_imp  , [e1;e2] -> Term.t_implies (force_prop e1) (force_prop e2)
  | OK_iff  , [e1;e2] -> Term.t_iff (force_prop e1) (force_prop e2)
  | OK_eq   , [e1;e2] -> Term.t_equ (force_bool e1) (force_bool e2)
  | OK_other, _ ->
      let p = try Mp.find p env.env_op with _ -> 
        (Format.printf "can not find %s@." (EcPath.tostring p);assert false) in
      t_app p (List.map force_bool args) ty
  | _       , _ -> assert false
      



exception RandExpr

let destr_ty_tuple t =
  match t.Ty.ty_node with
  | Ty.Tyapp (ts, lt) -> assert (Ty.is_ts_tuple ts); lt
  | _ -> assert false 

let rec trans_expr env vm e =
  match e with
  | Eint n -> 
      let n = Term.ConstInt(Term.IConstDecimal (string_of_int n)) in
      Term.t_const n 
  | Eflip | Einter _ | Ebitstr _ | Eexcepted _ -> raise RandExpr
  | Elocal(id,_) -> Term.t_var (trans_lv vm id) 
  | Evar(p,ty) -> assert false 
  | Eapp(p,args,ty) ->
      let ty = trans_ty env vm ty in
      let args = List.map (trans_expr env vm) args in 
      trans_op env p args ty 
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

and trans_expr_b env vm e = force_bool (trans_expr env vm e)

let trans_quant = function
  | Lforall -> Term.Tforall
  | Lexists -> Term.Texists

let merge_branches lb = 
  if List.exists (fun b -> b.Term.t_ty = None) lb then List.map force_prop lb
  else lb

let rec trans_form env vm f =
  match f.f_node with
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
      let f2,f3 = 
        match merge_branches [f2;f3] with
        | [f2;f3] -> f2, f3
        | _ -> assert false in
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
  | Fint n ->
      let n = Term.ConstInt(Term.IConstDecimal (string_of_int n)) in
      Term.t_const n 
  | Flocal id -> Term.t_var (trans_lv vm id) 
  | Fpvar(p,ty,s) ->  Term.t_app_infer (trans_pv env vm (p,ty) s) [] 
  | Fapp(p,args) ->
      let ty = trans_ty env vm f.f_ty in
      let args = List.map (trans_form env vm) args in 
      trans_op env p args ty
  | Ftuple args ->
      let args = List.map (trans_form_b env vm) args in
      Term.t_tuple args

and trans_form_b env vm f = force_bool (trans_form env vm f)

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

let add_ty env path td =
  let ts = trans_tydecl env path td in
  let decl = Decl.create_ty_decl ts in
  add_ts env path ts decl, RBty(path,ts,decl) 

let add_op env path op =
  if op.op_prob then env, None
  else
    let ls, decl = trans_op env path op in
    add_ls env path ls decl, Some (RBop(path,ls,decl))

let check_empty vm = 
  let check_empty m = assert (Mid.is_empty m) in 
  Array.iter check_empty vm.accu.pvm

(**** Calling prover *)
let provers = Whyconf.get_provers config

let provers_list = 
  Whyconf.Mprover.fold (fun p config l ->
    (p.Whyconf.prover_name, config, Driver.load_driver w3_env config.Whyconf.driver []) :: l) provers []

let get_prover name =
  try 
    List.find (fun (s,_,_) -> s = name) provers_list 
  with _ -> assert false (* FIXME error message *)

let call_prover_task prover timelimit task =
  let (_, pr, dr)  = get_prover prover in
  let res = 
    Call_provers.wait_on_call
      (Driver.prove_task ~command:pr.Whyconf.command ~timelimit
         dr task ()) () in
(*  Format.printf "call prover res = %a@." Call_provers.print_prover_result res; *)
  res.Call_provers.pr_answer = Call_provers.Valid

let check_w3_formula task prover timelimit f = 
  let pr   = Decl.create_prsymbol (Ident.id_fresh "goal") in
  let decl = Decl.create_prop_decl Decl.Pgoal pr f in
  let task = add_decl_with_tuples task decl in
(*  Format.printf "task = %a@." Pretty.print_task task;  *)
  call_prover_task prover timelimit task
  
exception CanNotProve of axiom

let add_ax env path ax =
  let pr = Decl.create_prsymbol (preid_p path) in
  let vm = empty_vmap () in
  match ax.ax_spec with
  | None -> assert false
  | Some f ->
      let f = trans_form env vm f in
      check_empty vm;
      if ax.ax_kind = Lemma && 
        not (check_w3_formula env.logic_task "Alt-Ergo" 10 f) then
        raise (CanNotProve ax);
      let decl = Decl.create_prop_decl Decl.Paxiom pr f in
      add_pr env path pr decl, RBax(path,pr,decl)



 
  











