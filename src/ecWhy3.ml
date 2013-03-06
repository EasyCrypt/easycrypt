(* ----------------------------------------------------------------------*)
open Why3
open EcUtils
open EcIdent
open EcPath
open EcTypes
open EcDecl
open EcFol
open EcModules
open EcTheory

module Mp   = EcPath.Mp
module Msym = EcSymbols.Msym

(* ----------------------------------------------------------------------*)
module Config : sig
  type prover =
    string * Why3.Whyconf.config_prover * Why3.Driver.driver

  val load    : string option -> unit
  val config  : unit -> Whyconf.config
  val main    : unit -> Whyconf.main
  val w3_env  : unit -> Env.env
  val provers : unit -> prover list
  val known_provers : unit -> string list
end = struct
  type prover =
    string * Why3.Whyconf.config_prover * Why3.Driver.driver

  let theconfig  : (Whyconf.config option) ref = ref None
  let themain    : (Whyconf.main   option) ref = ref None
  let thew3_env  : (Env.env        option) ref = ref None
  let theprovers : (_              list  ) ref = ref []

  let load why3config =
    if !theconfig = None then begin
      let config  = Whyconf.read_config why3config in
      let main    = Whyconf.get_main config in
      Whyconf.load_plugins main;
      let w3_env  = Env.create_env (Whyconf.loadpath main) in
      let provers =
        Whyconf.Mprover.fold
          (fun p config l ->
            (p.Whyconf.prover_name, config,
             Driver.load_driver w3_env config.Whyconf.driver []) :: l)
          (Whyconf.get_provers config) []
      in
        theconfig  := Some config;
        themain    := Some main;
        thew3_env  := Some w3_env;
        theprovers := provers
    end

  let config () =
    load None; EcUtils.oget !theconfig

  let main () =
    load None; EcUtils.oget !themain

  let w3_env () =
    load None; EcUtils.oget !thew3_env

  let provers () =
    load None; !theprovers

  let known_provers () = 
    List.map (fun (p,_,_) -> p) (provers())

end

let initialize    = Config.load
let known_provers = Config.known_provers

let get_w3_th dirname name =
  Env.find_theory (Config.w3_env ()) dirname name

(* ----------------------------------------------------------------------*)

type env = {
    logic_task : Task.task;
    env_ty : Ty.tysymbol Mp.t;
    env_op : (Term.lsymbol * Term.lsymbol * Ty.tvsymbol list) Mp.t;
    env_ax : Decl.prsymbol Mp.t;
    env_pa : Term.term Mp.t;
    env_w3 : (EcPath.path * Ty.tvsymbol list) Ident.Mid.t;
  }

let w3_ls_true = Term.fs_bool_true
let w3_ls_false = Term.fs_bool_false

let w3_ls_not, decl_not, spec_not = 
  let ls = 
    Term.create_fsymbol (Ident.id_fresh "Not") [] 
      (Ty.ty_func Ty.ty_bool Ty.ty_bool) in
  let decl = Decl.create_param_decl ls in
  let preid = Ident.id_fresh "b" in
  let id = Term.create_vsymbol preid Ty.ty_bool in
  let b = Term.t_var id in
  let f_app = Term.t_func_app (Term.t_app_infer ls []) b in
  let form = 
    Term.t_forall_close [id] [] 
      (Term.t_iff (Term.t_equ f_app Term.t_bool_true) 
         (Term.t_not (Term.t_equ b Term.t_bool_true))) in
  let pr = Decl.create_prsymbol (Ident.id_fresh "Not_spec") in
  let decl_spec = Decl.create_prop_decl Decl.Paxiom pr form in
  ls, decl, decl_spec 

let mk_w3_opp2 s mk = 
  let ls = 
    Term.create_fsymbol (Ident.id_fresh s) [] 
     (Ty.ty_func Ty.ty_bool (Ty.ty_func Ty.ty_bool Ty.ty_bool)) in
  let decl = Decl.create_param_decl ls in
  let preid = Ident.id_fresh "b" in
  let id1 = Term.create_vsymbol preid Ty.ty_bool in
  let id2 = Term.create_vsymbol preid Ty.ty_bool in
  let b1 = Term.t_var id1 in
  let b2 = Term.t_var id2 in
  let f_app = 
    Term.t_func_app (Term.t_func_app (Term.t_app_infer ls []) b1) b2 in
  let form = 
    Term.t_forall_close [id1;id2] [] 
      (Term.t_iff (Term.t_equ f_app Term.t_bool_true) 
         (mk (Term.t_equ b1 Term.t_bool_true) 
            (Term.t_equ b2 Term.t_bool_true))) in
  let pr = Decl.create_prsymbol (Ident.id_fresh (s^"_spec")) in
  let decl_spec = Decl.create_prop_decl Decl.Paxiom pr form in
  ls, decl, decl_spec 

let w3_ls_and, decl_and, spec_and = mk_w3_opp2 "AND" Term.t_and
let w3_ls_anda, decl_anda, spec_anda = mk_w3_opp2 "ANDA" Term.t_and_asym  
let w3_ls_or, decl_or, spec_or = mk_w3_opp2 "OR" Term.t_or
let w3_ls_ora, decl_ora, spec_ora = mk_w3_opp2 "OR" Term.t_or_asym
let w3_ls_imp, decl_imp, spec_imp = mk_w3_opp2 "IMP" Term.t_implies
let w3_ls_iff, decl_iff, spec_iff = mk_w3_opp2 "IFF" Term.t_iff

let w3_ls_eq, decl_eq, spec_eq = 
  let a  = Ty.create_tvsymbol (Ident.id_fresh "'a") in
  let ta = Ty.ty_var a in
  let ty = (Ty.ty_func ta (Ty.ty_func ta Ty.ty_bool)) in
  let ls = Term.create_fsymbol (Ident.id_fresh "EQ") [] ty in
  let decl = Decl.create_param_decl ls in
  let preid = Ident.id_fresh "x" in
  let id1 = Term.create_vsymbol preid ta in
  let id2 = Term.create_vsymbol preid ta in
  let b1 = Term.t_var id1 in
  let b2 = Term.t_var id2 in
  let f_app = 
    Term.t_func_app (Term.t_func_app (Term.fs_app ls [] ty) b1) b2 in
  let form = 
    Term.t_forall_close [id1;id2] [] 
      (Term.t_iff (Term.t_equ f_app Term.t_bool_true) 
         (Term.t_equ b1 b2)) in
  let pr = Decl.create_prsymbol (Ident.id_fresh ("EQ_spec")) in
  let decl_spec = Decl.create_prop_decl Decl.Paxiom pr form in
  ls, decl, decl_spec 

let ts_distr, fs_mu, distr_theory = 
  let th  = Theory.create_theory (Ident.id_fresh "Distr") in
  let th  = Theory.use_export th Theory.bool_theory in
  let th  = Theory.use_export th Theory.highord_theory in
  let vta = Ty.create_tvsymbol (Ident.id_fresh "ta") in
  let ta  = Ty.ty_var vta in 
  let tdistr = Ty.create_tysymbol (Ident.id_fresh "distr") [vta] None in
  let th  = Theory.add_ty_decl th tdistr in
  let mu  = 
    Term.create_fsymbol (Ident.id_fresh "mu") 
      [Ty.ty_app tdistr [ta]; Ty.ty_func ta Ty.ty_bool] 
      Ty.ty_real in
  let th = Theory.add_param_decl th mu in
  tdistr, mu, Theory.close_theory th 
  
let ty_distr t = Ty.ty_app ts_distr [t]

(* Special type for translation of hoare, equiv and pr *)
let ts_mem = Ty.create_tysymbol (Ident.id_fresh "memory") [] None 
let ty_mem = Ty.ty_app ts_mem []

let ts_mod = Ty.create_tysymbol (Ident.id_fresh "module") [] None
let ty_mod = Ty.ty_app ts_mod [] 

let ts_mod_name = Ty.create_tysymbol (Ident.id_fresh "module_name") [] None
let ty_mod_name = Ty.ty_app ts_mod_name []

let ts_fun_name = 
  let ta = Ty.create_tvsymbol (Ident.id_fresh "ta") 
  and tr = Ty.create_tvsymbol (Ident.id_fresh "tr") in
  Ty.create_tysymbol (Ident.id_fresh "fun_name") [ta;tr] None
let ty_fun_name ta tr = Ty.ty_app ts_fun_name [Ty.ty_tuple ta; tr]

let ts_var_name = 
  let t = Ty.create_tvsymbol (Ident.id_fresh "t") in
  Ty.create_tysymbol (Ident.id_fresh "var_name") [t] None
let ty_var_name t = Ty.ty_app ts_var_name [t]

let fs_getmod = 
  Term.create_fsymbol (Ident.id_fresh "getmod") [ty_mod; ty_mod_name] ty_mod

let getmod m mn = Term.t_app_infer fs_getmod [m;mn] 

let fs_appmod = 
  Term.create_fsymbol (Ident.id_fresh "appmod") [ty_mod;ty_mod] ty_mod

let appmod f m = Term.t_app_infer fs_appmod [f;m]

let fs_getvar = 
  let t = Ty.ty_var (Ty.create_tvsymbol (Ident.id_fresh "t")) in
  let tv = ty_var_name t in
  Term.create_fsymbol (Ident.id_fresh "getvar") [tv; ty_mem] t

let getvar v mem = Term.t_app_infer fs_getvar [v; mem]

let ty_mem_t tr = Ty.ty_tuple [ty_mem; tr] 

let fs_sem = 
  let ta = Ty.ty_var (Ty.create_tvsymbol (Ident.id_fresh "ta"))
  and tr = Ty.ty_var (Ty.create_tvsymbol (Ident.id_fresh "tr")) in
  let tf = Ty.ty_app ts_fun_name [ta; tr] in
  Term.create_fsymbol (Ident.id_fresh "sem") 
      [ty_mod;tf;ty_mem;ta] (ty_distr (ty_mem_t tr))

let ty_event tr = Ty.ty_func (ty_mem_t tr) Ty.ty_bool

let getpr m fn mem args ev =
  let sem = Term.t_app_infer fs_sem [m;fn;mem;Term.t_tuple args] in
  Term.t_app_infer fs_mu [sem;ev]

let add_decl_with_tuples task d =
  let ids = Ident.Mid.set_diff d.Decl.d_syms (Task.task_known task) in
  let add id s = match Ty.is_ts_tuple_id id with
    | Some n -> Stdlib.Sint.add n s
    | None -> s in
  let ixs = Ident.Sid.fold add ids Stdlib.Sint.empty in
  let add n task = Task.use_export task (Theory.tuple_theory n) in
  Task.add_decl (Stdlib.Sint.fold add ixs task) d

let initial_task = 
  let task = 
    List.fold_left Task.use_export None 
      [Theory.builtin_theory;Theory.bool_theory;Theory.highord_theory;
       distr_theory] in
  let task = 
    List.fold_left Task.add_decl task
      [decl_not; spec_not;
       decl_and; spec_and; decl_anda; spec_anda;
       decl_or; spec_or; decl_ora; spec_ora;
       decl_imp; spec_imp; decl_iff; spec_iff;
       decl_eq; spec_eq ] in
  let ts = [ts_mem; ts_mod; ts_mod_name; ts_fun_name; ts_var_name] in
  let add_ty_decl task ts = 
    add_decl_with_tuples task (Decl.create_ty_decl ts) in
  let fs = [fs_appmod; fs_getmod; fs_getvar; fs_sem;] in
  let add_param_decl task fs =
    add_decl_with_tuples task (Decl.create_param_decl fs) in
  let task = List.fold_left add_ty_decl task ts in
  List.fold_left add_param_decl task fs
  
let empty = {
    logic_task = initial_task; 
    env_ty     = Mp.empty;
    env_op     = Mp.empty;
    env_ax     = Mp.empty;
    env_pa     = Mp.empty;
    env_w3     = Ident.Mid.empty;
  } 

(* ---------------------------------------------------------------------- *)
    
type rebinding_w3 = {
    rb_th   : Theory.theory;
    rb_decl : Decl.decl list; 
    rb_ty   : Ty.tysymbol Mp.t;
    rb_op   : (Term.lsymbol * Term.lsymbol * Ty.tvsymbol list) Mp.t;
    rb_ax   : Decl.prsymbol Mp.t;
    rb_w3   : (EcPath.path * Ty.tvsymbol list) Ident.Mid.t;
  }

let rb_empty th = {
    rb_th     = th;
    rb_decl   = [];
    rb_ty     = Mp.empty;
    rb_op     = Mp.empty;
    rb_ax     = Mp.empty;
    rb_w3     = Ident.Mid.empty;
  } 

type highorder_decl = (Term.lsymbol * Decl.decl * Decl.decl) option

type rebinding_item = 
  | RBuse of rebinding_w3 
  | RBty  of EcPath.path * Ty.tysymbol * Decl.decl
  | RBop  of EcPath.path * (Term.lsymbol * Ty.tvsymbol list) * Decl.decl *
                highorder_decl 
  | RBax  of EcPath.path * Decl.prsymbol * Decl.decl
  | RBpa  of EcPath.path * Term.lsymbol

type rebinding = rebinding_item list

let merge check k o1 o2 = 
  match o1, o2 with
  | Some e1, Some e2 -> check k e1 e2; o1
  | _, None -> o1
  | None, _ -> o2

exception MergeW3Ty of EcPath.path * Ty.tysymbol * Ty.tysymbol
exception MergeW3Op of EcPath.path * Term.lsymbol * Term.lsymbol
exception MergeW3Ax of EcPath.path * Decl.prsymbol * Decl.prsymbol
exception MergeW3Id of Ident.ident * EcPath.path * EcPath.path

let merge_ty = 
  let check p t1 t2 = 
    if not (Ty.ts_equal t1 t2) then raise (MergeW3Ty(p,t1,t2)) in
  Mp.merge (merge check)

let merge_op =
  let check p (t1,_,_) (t2,_,_) = 
    if not (Term.ls_equal t1 t2) then raise (MergeW3Op(p,t1,t2)) in
  Mp.merge (merge check)

let merge_ax = 
  let check p t1 t2 = 
    if not (Decl.pr_equal t1 t2) then raise (MergeW3Ax(p,t1,t2)) in
  Mp.merge (merge check)

let merge_id = 
  let check p (t1,_) (t2,_) = 
    if not (EcPath.p_equal t1 t2) then raise (MergeW3Id(p,t1,t2)) in
  Ident.Mid.merge (merge check)

let add_ts env path ts decl =
  if Mp.mem path env.env_ty then 
    (assert (Ty.ts_equal ts (Mp.find path env.env_ty)); env)
  else 
    { env with 
      env_ty = Mp.add path ts env.env_ty;
      logic_task = add_decl_with_tuples env.logic_task decl }

let add_ls env path ls tparams decl odecl =
  let ls', add' =
    match odecl with
    | None -> ls, fun t -> t
    | Some(ls', decl', decl_s) -> 
        ls', fun t ->
          let t = add_decl_with_tuples t decl' in
          add_decl_with_tuples t decl_s in
  { env with 
    env_op = Mp.add path (ls,ls',tparams) env.env_op;
    logic_task = add' (add_decl_with_tuples env.logic_task decl) }

let add_param env path ls = 
  let decl = Decl.create_param_decl ls in
  { env with
    env_pa = Mp.add path (Term.t_app_infer ls []) env.env_pa;
    logic_task = add_decl_with_tuples env.logic_task decl}

    
let mk_highorder_func ls =
  let targs = ls.Term.ls_args in
  let tres = ls.Term.ls_value in
  if targs = [] then None 
  else
    let pid = Ident.id_clone ls.Term.ls_name in
    let codom = (odfl Ty.ty_bool tres) in
    let ty = List.fold_right Ty.ty_func ls.Term.ls_args codom in
    let ls' = Term.create_fsymbol pid [] ty in
    let decl' = Decl.create_param_decl ls' in
    let pr = Decl.create_prsymbol pid in
    let preid = Ident.id_fresh "x" in
    let params = List.map (Term.create_vsymbol preid) targs in
    let args = List.map Term.t_var params in
    let f_app' = 
      List.fold_left Term.t_func_app (Term.fs_app ls' [] ty) args in
    let f_app = Term.t_app ls args tres in
    let spec =
      match tres with
      | None -> Term.t_iff (Term.t_equ f_app' Term.t_bool_true) f_app
      | Some _ -> Term.t_equ f_app' f_app in
    let spec = Term.t_forall_close params [] spec in
    let decl_s = Decl.create_prop_decl Decl.Paxiom pr spec in
    Some(ls',decl',decl_s)
    
let add_pr env path pr decl =
  if Mp.mem path env.env_ax then 
    (assert (Decl.pr_equal pr (Mp.find path env.env_ax)); env)
  else 
    { env with 
      env_ax = Mp.add path pr env.env_ax;
      logic_task = add_decl_with_tuples env.logic_task decl }

let rebind_item env = function
  | RBuse w3 ->
      let task = Task.use_export env.logic_task w3.rb_th in
      let task = List.fold_left Task.add_decl task w3.rb_decl in
      { env with 
        logic_task = task;
        env_ty = merge_ty env.env_ty w3.rb_ty;
        env_op = merge_op env.env_op w3.rb_op;
        env_ax = merge_ax env.env_ax w3.rb_ax;
        env_w3 = merge_id env.env_w3 w3.rb_w3;
      }
  | RBty(p,ts,decl) -> add_ts env p ts decl
  | RBop(p,(ls,tvs),decl,odecl) -> add_ls env p ls tvs decl odecl
  | RBax(p,pr,decl) -> add_pr env p pr decl
  | RBpa(p,ls)      -> add_param env p ls 

let rebind = List.fold_left rebind_item

(* ---------------------------------------------------------------------- *)
(* -----------------------  Import why3 theory -------------------------- *)
(* ---------------------------------------------------------------------- *)
type renaming_kind =
  | RDts 
  | RDls
  | RDpr

type renaming_decl = (string list * renaming_kind * EcSymbols.symbol) list

let w3_id_string id = id.Ident.id_string

module Renaming = struct 
  type renaming = {
      r_ts : EcSymbols.symbol Ty.Mts.t;
      r_ls : EcSymbols.symbol Term.Mls.t;
      r_pr : EcSymbols.symbol Decl.Mpr.t
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
        w3_id_string id

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
        s

  let get_pr rn pr = 
    try Decl.Mpr.find pr rn.r_pr 
    with _ ->
      let id = pr.Decl.pr_name in
        w3_id_string id
end
      
module Wtvm = 
  struct

    type t = EcIdent.t Ty.Mtv.t ref 

    let create () = ref Ty.Mtv.empty 

    let get tvm tv = 
      try Ty.Mtv.find tv !tvm 
      with _ ->
        let s = w3_id_string tv.Ty.tv_name in
        assert (String.length s <> 0);
        let s = if s.[0] = '\'' then s else String.concat "" ["\'"; s] in
        let id = EcIdent.create s in
        tvm := Ty.Mtv.add tv id !tvm;
        id

    let tparams tvm = Ty.Mtv.values !tvm 
      
  end
      
exception UnknownWhy3Ident of Ident.ident 

let path_of_id env id = 
  try Ident.Mid.find id env.env_w3 
  with _ -> raise (UnknownWhy3Ident id) 

let rec import_w3_ty env tvm ty = 
  match ty.Ty.ty_node with
  | Ty.Tyvar v -> tvar (Wtvm.get tvm v)
  | Ty.Tyapp(t, args) ->
      let args = List.map (import_w3_ty env tvm) args in
      try 
        let path,_ = path_of_id env t.Ty.ts_name in
        tconstr path args
      with e ->
        if Ty.is_ts_tuple t then ttuple args
        else if Ty.ts_equal t Ty.ts_func then 
          let t1,t2 = List.hd2 args in
          tfun t1 t2
        else if Ty.ts_equal t Ty.ts_pred then
          let t1,t2 = List.hd args, tbool in
          tfun t1 t2
        else raise e
  
let exists_w3 env id = 
  Ident.Mid.mem id env.env_w3 

let add_w3_ty env p ty = 
  { env with 
    env_ty = Mp.add p ty env.env_ty;
    env_w3 = Ident.Mid.add (ty.Ty.ts_name) (p,[]) env.env_w3 }

let rbadd_w3_ty rb p ty = 
  { rb with
    rb_ty = Mp.add p ty rb.rb_ty;
    rb_w3 = Ident.Mid.add (ty.Ty.ts_name) (p,[]) rb.rb_w3 } 

type zipper_elem =
  | Zenter of EcSymbols.symbol
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
  let rb  = rbadd_w3_ty rb p ty in 
    (env, rb, Zdecl (Th_type (eid, td)) :: z)

let force_bool codom = 
  match codom with
  | None ->  EcTypes.tbool
  | Some t -> t 

exception CanNotTranslate
exception UnboundLS of Term.lsymbol

let import_w3_quant = function
  | Term.Tforall -> Lforall
  | Term.Texists -> Lexists

let is_asym t = 
  Ident.Slab.mem Term.asym_label t.Term.t_label
  
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
  let rec import vm t =
    match t.Term.t_node with
    | Term.Tvar v -> f_local (Term.Mvs.find v vm) (import_ty t.Term.t_ty)
    | Term.Tconst _ -> raise CanNotTranslate (* FIXME *)
    | Term.Tapp(f,wargs) ->
        let args = List.map (import vm) wargs in
        let import_ty = import_w3_ty env tvm in
        let wty = t.Term.t_ty in
        let codom = odfl tbool (omap wty import_ty) in
        begin try 
          let p,tvs = 
            try Ident.Mid.find f.Term.ls_name env.env_w3 
            with _ -> raise (UnboundLS f) in
          let s = Term.ls_app_inst f wargs wty in
          let tys = List.map (fun vs -> import_ty (Ty.Mtv.find vs s)) tvs in
          let dom = List.map EcFol.ty args in
          let op = f_op p tys (toarrow dom codom) in
          f_app op args codom
        with UnboundLS f as e ->
          if Term.is_fs_tuple f then f_tuple args
          else 
            if (Term.ls_equal f Term.fs_func_app || 
            Term.ls_equal f Term.ps_pred_app) then
              let a1,a2 = List.hd2 args in
              f_app a1 [a2] codom
            else raise e 
        end
          
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
        let ids = List.map (fun (x, ty) -> (x, GTty ty)) ids in
        let f = import vm t in
        f_quant (import_w3_quant q) ids f
    | Term.Tbinop(op,t1,t2) ->
        let f1 = import vm t1 in
        let f2 = import vm t2 in
        begin match op with
        | Term.Tand     -> 
            if is_asym t1 then f_anda f1 f2 else f_and f1 f2
        | Term.Tor      -> 
            if is_asym t1 then f_ora f1 f2 else f_or f1 f2
        | Term.Timplies -> f_imp f1 f2
        | Term.Tiff     -> f_iff f1 f2
        end
    | Term.Tnot t -> f_not (import vm t)
    | Term.Ttrue  -> f_true
    | Term.Tfalse -> f_false in
  import_ty, add_locals, import 

let add_w3_ls env p ls wparams odecl = 
  let ls' = match odecl with None -> ls | Some (ls',_,_) -> ls' in
  { env with 
    env_op = Mp.add p (ls,ls',wparams) env.env_op; 
    env_w3 = Ident.Mid.add ls.Term.ls_name (p,wparams) env.env_w3 }
    
let rbadd_w3_ls rb p ls wparams odecl = 
  let ls',rb_decl = 
    match odecl with 
    | None -> ls, rb.rb_decl
    | Some (ls',d',ds) -> ls', ds::d'::rb.rb_decl in
  { rb with 
    rb_op = Mp.add p (ls,ls',wparams) rb.rb_op; 
    rb_w3 = Ident.Mid.add ls.Term.ls_name (p,wparams) rb.rb_w3;
    rb_decl = rb_decl;
  }

let import_w3_ls rn path (env,rb,z) ls = 
  let tvm = Wtvm.create () in
  let dom = List.map (import_w3_ty env tvm) ls.Term.ls_args in
  let codom = omap ls.Term.ls_value (import_w3_ty env tvm) in
  let wparams = Ty.Stv.elements (Term.ls_ty_freevars ls) in
  let params = List.map (Wtvm.get tvm) wparams in
  let eid = Renaming.get_ls rn ls in
  let op = mk_op params dom (force_bool codom) None in
  let p = EcPath.extend (Some path) eid in
  let odecl = mk_highorder_func ls in
  let env = add_w3_ls env p ls wparams odecl in 
  let rb  = rbadd_w3_ls rb p ls wparams odecl in 
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
    env_w3 = Ident.Mid.add (pr.Decl.pr_name) (p,[]) env.env_w3 }

let rbadd_w3_pr rb p pr = 
  { rb with 
    rb_ax = Mp.add p pr rb.rb_ax;
    rb_w3 = Ident.Mid.add (pr.Decl.pr_name) (p,[]) rb.rb_w3 }

let import_w3_pr rn path (env,rb,z as envld) k pr t =
  match k with
  | Decl.Plemma | Decl.Paxiom ->
      let eid = Renaming.get_pr rn pr in
      let tvm = Wtvm.create () in
      let _, _, import = import_w3_term env tvm in
      let spec = 
        try Some (import Term.Mvs.empty t);
        with CanNotTranslate -> None in
      let ax = { 
        ax_params = Wtvm.tparams tvm; (* FIXME assert unicity of string *)
        ax_spec = spec;
        ax_kind = if k = Decl.Plemma then assert false (*FIXME Lemma *)
        else Axiom } in
      let p = EcPath.extend (Some path) eid in
      let env = add_w3_pr env p pr in
      let rb  = rbadd_w3_pr rb p pr in 
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

let import_decls rn path env rb decls =
  let rec diff ls ls' = 
    match ls, ls' with
    | s::ls, s'::ls' when s = s' -> diff ls ls'
    | _, _ -> List.rev ls, ls' in
  let rec close accu ls path z = 
    match ls, z, path.EcPath.p_node with
    | [], _, _ -> path, z 
    | s::ls, Zenter id:: z, EcPath.Pqname(p,id') ->
        assert (s = id && EcSymbols.equal id id');
        close [] ls p (Zdecl (Th_theory (id, accu)) :: z)
    | _s::_ls, Zenter _id:: _z, _ -> assert false
    | _, Zdecl d::z, _ -> close (d::accu) ls path z
    | _, [], _ -> assert false in
  let open_ ls path z = 
    List.fold_left (fun (path, z) s -> 
      EcPath.extend (Some path) s, (Zenter s) :: z) (path, z) ls
  in
    
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
  aux [] path (env,rb,[]) decls

let import_w3 env path th rd =
  let rb = rb_empty th in
  let rn = Renaming.init rd th in
  let task = Task.use_export None th in
  let ths = Ident.Mid.remove th.Theory.th_name (Task.used_theories task) in
  let others = Task.used_symbols ths in
  let decls = Task.local_decls task others in
  let _env,rb,ld = import_decls rn path env rb decls in
  let rb = { rb with rb_decl = List.rev rb.rb_decl } in
  ld, RBuse rb
  
(* ----------------------------------------------------------------------- *)
(* ------------------------ Exporting to why3 ---------------------------- *)
(* ----------------------------------------------------------------------- *)
let preid id = 
  Ident.id_fresh (EcIdent.name id)

let str_p p = 
  let ls,s = EcPath.toqsymbol p in
  List.fold_right (fun s1 s2 -> s1 ^ "_" ^ s2) ls s
  
let preid_p p = Ident.id_fresh (str_p p)

let create_tvsymbol id = 
  Ty.create_tvsymbol (preid id)

type vmap = {
    vm_tv : Ty.ty Mid.t; 
    vm_id : Term.term Mid.t;
  }

let empty_vmap =
  { vm_tv = Mid.empty;
    vm_id = Mid.empty; }

exception UnboundTypeVariable of EcIdent.t
      

(* ------------------------ Types -----------------------------------------*)

let trans_pty env p = 
  try Mp.find p env.env_ty 
  with _ -> assert false

let trans_tv vm tv = 
  try Mid.find tv vm.vm_tv
  with _ -> raise (UnboundTypeVariable tv)

let rec trans_ty env vm ty = 
  match ty.ty_node with
  | Tunivar _ -> assert false
  | Tvar id -> trans_tv vm id
  | Ttuple tys -> Ty.ty_tuple (trans_tys env vm tys)
  | Tconstr(p,tys) ->
      let id = trans_pty env p in
      Ty.ty_app id (trans_tys env vm tys)
  | Tfun(t1,t2) -> Ty.ty_func (trans_ty env vm t1) (trans_ty env vm t2)

and trans_tys env vm tys = List.map (trans_ty env vm) tys

let trans_oty env vm oty =
  match oty with
  | None -> None 
  | Some t -> Some (trans_ty env vm t)

let trans_typarams vm tparams = 
  let vm = ref vm in
  let trans_tv id = 
    assert (not (Mid.mem id !vm.vm_tv));
    let tv = create_tvsymbol id in
    vm := {!vm with vm_tv = Mid.add id (Ty.ty_var tv) !vm.vm_tv };
    tv in
  let tparams = List.map trans_tv tparams in
  tparams, !vm
  
let trans_tydecl env path td =
  let pid = preid_p path in
  let tparams, vm = trans_typarams empty_vmap td.tyd_params in
  let body = omap td.tyd_type (trans_ty env vm) in
  Ty.create_tysymbol pid tparams body 

(* --------------------------- Formulas ------------------------------- *)


let trans_lv vm lv = 
  try Mid.find lv vm.vm_id with _ -> assert false

let trans_pa env p = try Mp.find p env.env_pa with _ -> assert false

exception TranslateLocalPV of prog_var 

let trans_pv env vm pv mem =
  if pv.pv_kind = PVloc then raise (TranslateLocalPV pv);
  let p   = EcPath.path_of_mpath pv.pv_name in
  let v   = trans_pa env p in
  let m   = trans_lv vm mem in
  getvar v m 
  
let create_vsymbol id ty = Term.create_vsymbol (preid id) ty 

let add_id vm id ty =
  assert (not (Mid.mem id vm.vm_id));
  let wid = create_vsymbol id ty in
  let vm = { vm with
             vm_id = Mid.add id (Term.t_var wid) vm.vm_id } in
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
  | OK_and   of bool
  | OK_or    of bool
  | OK_imp
  | OK_iff
  | OK_eq
  | OK_other 

let op_kind = 
  let l = [EcCoreLib.p_true, OK_true; EcCoreLib.p_false, OK_false;
           EcCoreLib.p_not, OK_not; 
           EcCoreLib.p_anda, OK_and true; EcCoreLib.p_and, OK_and false; 
           EcCoreLib.p_ora,  OK_or true;  EcCoreLib.p_or,  OK_or  false; 
           EcCoreLib.p_imp, OK_imp; EcCoreLib.p_iff, OK_iff;
           EcCoreLib.p_eq, OK_eq] in
  let m = List.fold_left (fun m (p,k) -> Mp.add p k m) Mp.empty l in
  fun p -> try Mp.find p m with _ -> OK_other

let mk_not args  =
  match args with
  | [e] -> Term.t_not e
  | _ -> assert false

let mk_pred2 f l = 
  match l with
  | [e1;e2] -> f e1 e2
  | _ -> assert false

let mk_anda = mk_pred2 Term.t_and_asym
let mk_and = mk_pred2 Term.t_and
let mk_ora  = mk_pred2 Term.t_or_asym
let mk_or  = mk_pred2 Term.t_or
let mk_imp = mk_pred2 Term.t_implies
let mk_iff = mk_pred2 Term.t_iff
let mk_eq  = mk_pred2 Term.t_equ
  
let trans_op env vm p tys =
  match op_kind p with
  | OK_true  -> ([],None), w3_ls_true, fun _ -> Term.t_true
  | OK_false -> ([],None), w3_ls_false, fun _ -> Term.t_false
  | OK_not   -> ([None],None), w3_ls_not, mk_not
  | OK_and true  -> ([None;None],None), w3_ls_anda, mk_anda
  | OK_and false -> ([None;None],None), w3_ls_and, mk_and
  | OK_or  true  -> ([None;None],None), w3_ls_ora, mk_ora
  | OK_or  false -> ([None;None],None), w3_ls_or, mk_or
  | OK_imp   -> ([None;None],None), w3_ls_imp, mk_imp
  | OK_iff   -> ([None;None],None), w3_ls_iff, mk_iff
  | OK_eq    -> 
      let ty = trans_ty env vm (List.hd tys) in
      ([Some ty;Some ty],None), w3_ls_eq, mk_eq
  | OK_other ->
      let ls,ls', tvs = 
        try Mp.find p env.env_op 
        with _ -> 
          Format.printf "can not find %s@." (EcPath.tostring p);
          assert false in (* FIXME error message *)
      let mtv = 
        try 
          List.fold_left2 (fun mtv tv ty ->
            Ty.Mtv.add tv (trans_ty env vm ty) mtv) Ty.Mtv.empty
            tvs tys 
        with e -> Format.printf "ICI %s@." (EcPath.tostring p); raise e
      in
      let targs = List.map (fun t -> Some (Ty.ty_inst mtv t)) ls.Term.ls_args in
      let tres  = omap ls.Term.ls_value (Ty.ty_inst mtv) in
      let mk args = Term.t_app ls args tres in
      (targs,tres), ls', mk
 
let apply_highorder f args = 
  List.fold_left (fun f a -> Term.t_func_app f (force_bool a)) f args

let cast_arg a ty = 
  match a.Term.t_ty, ty with
  | None, None -> a
  | None, Some _ -> force_bool a
  | Some _, None -> force_prop a
  | Some _,Some _ -> a

let cast_app mk args targs = mk (List.map2 cast_arg args targs)
 
let rec highorder_type targs tres = 
  match targs with
  | [] -> odfl Ty.ty_bool tres
  | a::targs -> Ty.ty_func a (highorder_type targs tres)
  
let trans_app env vm p tys args = 
  let (targs,tres), ls', mk = trans_op env vm p tys in
  let arity = List.length targs in
  let nargs = List.length args in
  if arity = nargs then cast_app mk args targs
  else if arity < nargs then
    let args1,args2 = List.take_n arity args in
    apply_highorder (cast_app mk args1 targs) args2
  else (* arity > nargs *)
    let targs = List.map (odfl Ty.ty_bool) targs in
    let fty = highorder_type targs tres in
    apply_highorder (Term.fs_app ls' [] fty) args 

let destr_ty_tuple t =
  match t.Ty.ty_node with
  | Ty.Tyapp (ts, lt) -> assert (Ty.is_ts_tuple ts); lt
  | _ -> assert false 

let trans_quant = function
  | Lforall -> Term.Tforall
  | Lexists -> Term.Texists

let merge_branches lb = 
  if List.exists (fun b -> b.Term.t_ty = None) lb then List.map force_prop lb
  else lb

exception CanNotTranslate of form

let rec trans_mod env vm mp = 

  let is_mod ks = match ks with EcPath.PKmodule::_ -> true | _ -> false in

  let rec aux p ks args =
    match p.EcPath.p_node, ks, args with
    | Pident id, _, [a] ->
        let mo = trans_lv vm id in
        app_mod mo a
    | Psymbol _, [EcPath.PKmodule], [a] -> 
        let mo = trans_pa env p in
        app_mod mo a
    | Pqname(p',_), EcPath.PKmodule::ks, a::args -> 
        if is_mod ks then
          let mo = aux p' ks args in
          let mn = trans_pa env p in
          app_mod (getmod mo mn) a
        else
          let mo = trans_pa env p in
          app_mod mo a 
    | _, _, _ -> assert false
  and app_mod mo a =
    if a = [] then mo else
    let a = List.map (trans_mod env vm) a in
    List.fold_left appmod mo a in
  aux mp.EcPath.m_path mp.EcPath.m_kind mp.EcPath.m_args
  
let trans_fun env vm mp = 
  let p = EcPath.path_of_mpath mp in
  let fn = trans_pa env p in
  let mp,_,_,_ = oget (EcPath.m_split mp) in
  let mo = trans_mod env vm mp in
  mo, fn

let trans_gty env vm gty =
  match gty with
  | GTty ty -> trans_ty env vm ty
  | GTmodty _ -> ty_mod
  | GTmem     -> ty_mem

let trans_gtys env vm gtys =
  List.map (trans_gty env vm) gtys

let trans_form env vm f =
  let env = ref env in
  let rb  = ref [] in
  
  let rec trans_form vm f = 
    match f.f_node with
    | Fquant(q,b,f) ->
        let ids, tys = List.split b in
        let tys = trans_gtys !env vm tys in
        let vs, vm = add_ids vm ids tys in
        let f = trans_form vm f in
        Term.t_quant_close (trans_quant q) vs [] (force_prop f)

    | Fif(f1,f2,f3) ->
        let f1 = trans_form vm f1 in
        let f2 = trans_form vm f2 in
        let f3 = trans_form vm f3 in
        let f2,f3 = 
          match merge_branches [f2;f3] with
          | [f2;f3] -> f2, f3
          | _ -> assert false in
        Term.t_if_simp (force_prop f1) f2 f3

    | Flet(lp,f1,f2) ->
        let f1 = trans_form_b vm f1 in
        begin match lp with
        | LSymbol id -> 
            let id, vm = add_id vm id (Term.t_type f1) in
            let f2 = trans_form vm f2 in
            Term.t_let f1 (Term.t_close_bound id f2)
        | LTuple ids ->
            let t1 = Term.t_type f1 in
            let ids, vm = add_ids vm ids (destr_ty_tuple t1) in
            let pat = 
              Term.pat_app (Term.fs_tuple (List.length ids)) 
                (List.map Term.pat_var ids) t1 in
            let f2 = trans_form vm f2 in
            let br = Term.t_close_branch pat f2 in
            Term.t_case f1 [br] 
        end

    | Fint n ->
        let n = Term.ConstInt(Term.IConstDecimal (string_of_int n)) in
        Term.t_const n 

    | Flocal id -> trans_lv vm id

    | Fop(p,tys) -> trans_app !env vm p tys [] 

    | Fapp({f_node = Fop(p,tys) },args) ->
        let args = List.map (trans_form vm) args in
        trans_app !env vm p tys args

    | Fapp(e,args) ->
        let args = List.map (trans_form vm) args in
        apply_highorder (trans_form vm e) args
          
    | Ftuple args ->
        let args = List.map (trans_form_b vm) args in
        Term.t_tuple args

    | Fhoare _ | FhoareF _ | FhoareS _ | FequivF _  | FequivS _ -> 
        raise (CanNotTranslate f)
          
    | Fpvar(pv,m) -> trans_pv !env vm pv m 

    | Fpr(mem,mp,args,ev) -> 
        let mem   = trans_lv vm mem in
        let mo, f = trans_fun !env vm mp in 
        let args  = List.map (trans_form_b vm) args in
        let ev    = trans_ev vm ev in
        getpr mo f mem args ev

  and trans_form_b vm f = force_bool (trans_form vm f)
  and trans_ev _vm _ev = assert false in
  let f = trans_form vm f in
  !env, !rb, f

let trans_oper_body env vm ls = function
  | OB_oper None | OB_pred None -> env,[],Decl.create_param_decl ls
  | OB_oper (Some (ids,body)) ->
      let ids, vm = add_ids vm ids ls.Term.ls_args in
      let body = EcFol.form_of_exp EcFol.mstd body in
      let env,rb,e = trans_form env vm body in
      let e = if ls.Term.ls_value = None then force_prop e else e in
      env,rb,Decl.create_logic_decl [Decl.make_ls_defn ls ids e]
  | OB_pred (Some(ids,body) ) ->
      let ids,vm = add_ids vm ids ls.Term.ls_args in
      let env,rb,e = trans_form env vm body in
      let e = force_prop e in 
      env,rb,Decl.create_logic_decl [Decl.make_ls_defn ls ids e]

let trans_oper env path op = 
  let wparams,vm = trans_typarams empty_vmap op.op_params in
  let pid = preid_p path in
  let dom = trans_tys env vm op.op_dom in
  let codom = trans_ty env vm op.op_codom in
  let codom = if Ty.ty_equal codom Ty.ty_bool then None else Some codom in
  let ls = Term.create_lsymbol pid dom codom in
  let env, rb, body = trans_oper_body env vm ls op.op_kind in
  env, rb, ls, wparams, body

let add_ty env path td =
  let ts = trans_tydecl env path td in
  let decl = Decl.create_ty_decl ts in
  add_ts env path ts decl, [RBty(path,ts,decl)]

let add_op env path op =
  let env, rb, ls, wparams, decl = trans_oper env path op in
  let odecl = mk_highorder_func ls in
  let env = add_ls env path ls wparams decl odecl in
  let rb = RBop(path,(ls,wparams),decl,odecl)::rb in
  env, rb

let add_ax env path ax =
  let pr = Decl.create_prsymbol (preid_p path) in
  let _,vm = trans_typarams empty_vmap ax.ax_params in
  match ax.ax_spec with
  | None -> assert false
  | Some f ->
      let env,rb,f = trans_form env vm f in
      let decl = Decl.create_prop_decl Decl.Paxiom pr f in
      add_pr env path pr decl, RBax(path,pr,decl)::rb

(*let rec add_mod_exp env path me = *)
  
  

(* -------------------------------------------------------------------- *)
(* ---------------------- Calling prover ------------------------------ *)
(* -------------------------------------------------------------------- *)



exception UnknownProver of string

let get_prover name =
  List.find (fun (s,_,_) -> s = name) (Config.provers ())

let check_prover_name name = 
  try ignore(get_prover name); true with _ -> false 

(* -------------------------------------------------------------------- *)
let restartable_syscall (call : unit -> 'a) : 'a =
  let output = ref None in
    while !output = None do
      try  output := Some (call ())
      with
      | Unix.Unix_error (errno, _, _) when errno = Unix.EINTR -> ()
    done;
    EcUtils.oget !output

let para_call max_provers provers timelimit task = 
  let module CP = Call_provers in

  let pcs    = Array.create max_provers None in

  (* Run process, ignoring prover failing to start *)
  let run i prover =
    try 
      let (_, pr, dr)  = get_prover prover in
(*      Format.printf "Start prover %s@." prover; *)
      let pc =
        Driver.prove_task ~command:pr.Whyconf.command ~timelimit dr task () in
      begin
        try
          ExtUnix.All.setpgid (CP.prover_call_pid pc) 0
        with Unix.Unix_error _ -> ()
      end;
      pcs.(i) <- Some(prover, pc)
 (*  Format.printf "Prover %s started and set at %i@." prover i *)
    with e -> 
      Format.printf "Error when starting %s: %a" prover 
        EcPexception.exn_printer e;
      ()
  in

  (* Start the provers, at most max_provers run in the same time *)
  let nb_provers = Array.length provers in
  let min = if max_provers < nb_provers then max_provers else nb_provers in
  for i = 0 to min - 1 do run i provers.(i) done; 
  (* Other provers are set in a queue *)
  let pqueue = Queue.create () in
  for i = min to nb_provers - 1 do Queue.add provers.(i) pqueue done;
  
  (* Wait for the first prover giving a definitive answer *)    
  let status = ref None in
  EcUtils.try_finally
    (fun () ->
      let alives = ref (-1) in
      while !alives <> 0 && !status = None do
        let pid, st = restartable_syscall Unix.wait in
        alives := 0;
        for i = 0 to (Array.length pcs) - 1 do
          match pcs.(i) with
          | None -> ()
          | Some (_prover, pc) ->
              if CP.prover_call_pid pc = pid then begin
                pcs.(i) <- None;            (* DO IT FIRST *)
                let ans = (CP.post_wait_call pc st ()).CP.pr_answer in
                (*Format.eprintf "prover `%s' return %a@."
                  prover CP.print_prover_answer ans; *)
                match ans with
                | CP.Valid   -> status := Some true
                | CP.Invalid -> status := Some false
                | _          -> 
                    if not (Queue.is_empty pqueue) then 
                      run i (Queue.take pqueue)
              end;
              if pcs.(i) <> None then incr alives
        done
      done;
      !status)

    (* Clean-up: hard kill + wait for remaining provers *)
    (fun () ->
      for i = 0 to (Array.length pcs) - 1 do
        match pcs.(i) with
        | None    -> ()
        | Some (_prover,pc) ->
            let pid = CP.prover_call_pid pc in
            pcs.(i) <- None;
            begin try
(*              Format.printf
                "Killing (SIGTERM) prover `%s' (pid = %d)@."
                prover pid; *)
              Unix.kill (-pid) 15;      (* kill process group *)
            with Unix.Unix_error _ -> ()
            end;
(*            Format.printf "prover %s finished@." prover; *)
            let _, st =
              restartable_syscall (fun () -> Unix.waitpid [] pid)
            in
            ignore (CP.post_wait_call pc st ());
      done)





type prover_infos = 
  { prover_max_run   : int;
    prover_names     : string array;
    prover_timelimit : int; }    

let dft_prover_infos = 
  { prover_max_run   = 7;       
    prover_names     = [||];
    prover_timelimit = 3; }

let call_prover_task pi task =
  para_call pi.prover_max_run pi.prover_names pi.prover_timelimit task = 
  Some true

let check_w3_formula pi task f = 
  let pr   = Decl.create_prsymbol (Ident.id_fresh "goal") in
  let decl = Decl.create_prop_decl Decl.Pgoal pr f in
  let task = add_decl_with_tuples task decl in
  call_prover_task pi task
  
exception CanNotProve of axiom

let check_goal env pi (hyps, concl) = 
  let vm = ref empty_vmap in
  let env = ref env in
  let trans_tv id = 
    let ts = Ty.create_tysymbol (preid id) [] None in
    let decl = Decl.create_ty_decl ts in
    vm := { !vm with vm_tv = Mid.add id (Ty.ty_app ts []) !vm.vm_tv};
    env := { !env with 
             logic_task = add_decl_with_tuples !env.logic_task decl } in
  let trans_hyp (id,ld) =
    let decl = 
      match ld with
      | LD_var (ty,body) -> 
          let codom = trans_ty !env !vm ty in
          let pid = preid id in
          let ls = Term.create_lsymbol pid [] (Some codom) in
          let decl = match body with
          | None -> Decl.create_param_decl ls
          | Some e -> 
              let nenv, _, e = trans_form !env !vm e in 
              env := nenv;
              Decl.create_logic_decl [Decl.make_ls_defn ls [] e] in
          vm := { !vm 
                with vm_id = Mid.add id (t_app ls [] codom) !vm.vm_id };
          decl
      | LD_hyp f -> 
          let nenv, _, f = trans_form !env !vm f in
          env := nenv;
          let pr = Decl.create_prsymbol (preid id) in
          Decl.create_prop_decl Decl.Paxiom pr f
      | LD_mem     -> assert false        (* FIXME *)
      | LD_modty _ -> assert false        (* FIXME *) in
    env := { !env with
             logic_task = add_decl_with_tuples !env.logic_task decl };
  in
  List.iter trans_tv hyps.h_tvar;
  List.iter trans_hyp (List.rev hyps.h_local);
  let env, _, concl = trans_form !env !vm concl in
  check_w3_formula pi env.logic_task concl
