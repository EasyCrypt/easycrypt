open EcUtil
open Global

(** List of provers *)
let current_provers =
  let check name = 
    try EcWhy3.check_prover_name name; true
    with _ -> false in
  let default_list = 
    List.filter check ["alt-ergo";"vampire";"z3";"cvc3";"eprover";"yices"] in
  ref default_list 
 
let set_prover_option names = 
  if names = [] then user_error "you should give at least one prover";
  List.iter EcWhy3.check_prover_name names;
  current_provers := names;
  let s = if List.length names <= 1 then " is" else "s are" in
  debug db_glob "current prover%s %a@." s 
    (pp_list ~sep:", " (fun fmt s -> Format.fprintf fmt "%s" s)) names

(*let _ = Global.add_list_register current_provers*)

open Ast
open EcWhy3
open Why3

let add_theories task = 
  List.fold_left Task.use_export task !EcWhy3.theories
      
let add_type task tdef =
  if tdef.t_native_why then task 
  else
    let ty_decl = tdef.t_wsymbol, Decl.Tabstract in
    Task.add_ty_decl task [ty_decl] 

let add_cnst task c = 
  if c.c_native_why then task 
  else
    Task.add_logic_decl task [c.c_why3]

let add_op task op = 
  if op.op_native_why then task 
  else
    Task.add_logic_decl task [op.op_why3]  

let add_one_def task = function
  | Global.WE_type tdef -> add_type task tdef
  | Global.WE_cnst c -> add_cnst task c
  | Global.WE_op op -> add_op task op
  | Global.WE_pred pr -> Task.add_logic_decl task [Fol.logic_decl pr] 

let add_defs task =
  List.fold_left add_one_def task (List.rev !Global.why_export)

let add_axioms task =
  let task = ref task in
  let add (_,(r,_,(pr,t))) = 
    if r then 
      task := Why3.Task.add_prop_decl !task Why3.Decl.Paxiom pr t in
  Global.Axioms.iter add;
  !task
 
let add_tuple task = 
  let add_injectivity _i task = 
(*    let id = Why3.Ident.id_fresh ("tuple_inj_" ^ (string_of_int i)) in
    let prs = Why3.Decl.create_prsymbol id in
    let is =
      let rec aux acc i = 
        if i <= 0 then acc else aux (string_of_int i :: acc) (i-1) in
      aux [] i in
    let init_ty i = 
      let id = Why3.Ident.id_fresh ("'a"^ i) in
      Why3.Ty.ty_var (Why3.Ty.create_tvsymbol id) in
    let types = List.map init_ty is in
    let init_v s i t =
      let id = Why3.Ident.id_fresh (s ^ i) in
      Why3.Term.create_vsymbol id t in
    let xs = List.map2 (init_v "x") is types in
    let txs = List.map Why3.Term.t_var xs in
    let ys = List.map2 (init_v "y") is types in
    let tys = List.map Why3.Term.t_var ys in
    let xtuple = Why3.Term.t_tuple txs in
    let ytuple = Why3.Term.t_tuple tys in
    let eqxy = Why3.Term.t_equ xtuple ytuple in
    let concl = Why3.Term.t_and_simp_l (List.map2 Why3.Term.t_equ txs tys) in
    let concl = Why3.Term.t_implies eqxy concl in
    let ax = Why3.Term.t_forall_close (xs @ ys) [[eqxy]] concl in
    Why3.Task.add_prop_decl task Why3.Decl.Paxiom prs ax*) task in
  Hashtbl.fold 
    (fun i () task ->
      try 
        let ts = Why3.Ty.ts_tuple i in
        let fs = Why3.Term.fs_tuple i in 
        let ty_decl = ts, Why3.Decl.Talgebraic [fs] in
        let task = Task.add_ty_decl task [ty_decl] in
        add_injectivity i task
      with _ -> task) EcWhy3.htuple task 
          
let init_task () =
  let task = None in
  let task = EcTerm.decl_bitstring task in
  let task = add_theories task in 
  let task = add_tuple task in
  let task = add_defs task in
  add_axioms task
 
let check_why3 ?timeout ?(pp_failure=true) ?(goal_name="why_goal") p =
  (*verbose "check_why3 %a@." Fol.pp_pred p; *)
  let p = Fol.pclos p in
  (* Format.printf "check_why3_pclos %a@." Fol.pp_pred p; *)
  let pr,t = Fol.mk_axiom goal_name p in
  let task = init_task () in
  let task = Why3.Task.add_prop_decl task Why3.Decl.Pgoal pr t in
  let timeout = 
    match timeout with
    | None -> Global.Timeout.get ()
    | Some t -> t in
  EcWhy3.para_call !current_provers timeout pp_failure goal_name task 

(** Checking probability *)

let find_pr (f,e) tbl =
  let test ((f',e'),_) = EcTerm.eq_fct f f' && EcTerm.eq_exp e e' in
  snd (List.find test tbl)

let mk_name_tbl l (e:Ast.real_exp) = 
  let tbl = ref [] in
  let count = ref (-1) in
  let rec add_name = function
    | Ast.Ecnst _ -> ()
    | Ast.Ebase(f,e) ->
  begin 
    try let _ = find_pr (f,e) !tbl in ()
    with Not_found ->
      incr count;
            let id = Why3.Ident.id_fresh (Format.sprintf "Pr%i" !count) in
            let ls = Why3.Term.create_fsymbol id [] EcWhy3.ty_real in
            let t = Why3.Term.t_app_infer ls [] in
      tbl := ((f,e),(ls,t))::!tbl
  end
    | Ast.Eapp(_, args) -> List.iter add_name args
    | Ast.Ernd _ | Ast.Epair _ | Ast.Eif _ | Ast.Elet _ -> assert false in
  List.iter (fun (_,e) -> add_name e) l;
  add_name e;
  !tbl


let rzero = 
  Term.t_const (Term.ConstReal (Term.RConstDecimal("0","0",None)))

let rone = 
  Term.t_const (Term.ConstReal (Term.RConstDecimal("1","0",None)))

let mk_bound t =
  Term.t_and 
    (Term.ps_app EcWhy3.ps_le_real [rzero; t])
    (Term.ps_app EcWhy3.ps_le_real [t; rone])

let mk_form_of_real_exp tbl =
  let term_of_rbase _ b = snd (find_pr b tbl) in
  EcTerm.g_term_of_exp (fun _ _ -> ()) EcTerm.add_why3_var term_of_rbase

let add_tbl =
   List.fold_left 
      (fun task (_,(fs,t)) ->
        (* We declare the symbol *)
        let task = Task.add_logic_decl task [(fs,None)] in
        (* We add the bound *)
        let id = 
          Ident.id_fresh (fs.Term.ls_name.Ident.id_string ^ "_bounded") in
        let pr = Decl.create_prsymbol id in 
        Task.add_prop_decl task Decl.Paxiom pr (mk_bound t))

let check_pr name pr_list rcmp = 
  let task = init_task () in
  let pr_list = List.map snd (List.filter (fun (r,_) -> !r) pr_list) in
  let tbl = mk_name_tbl pr_list rcmp in
  (* Add the globals names *)
  let task = add_tbl task tbl in
  (* Add already proved lemmas on global names *)
  let _,mk_cmp = mk_form_of_real_exp tbl in
  let task =
    List.fold_left (fun task (name, e) ->
      let pr = Decl.create_prsymbol (Ident.id_fresh name) in
      Task.add_prop_decl task Decl.Paxiom pr (mk_cmp [] [] e)) task pr_list in
  let pr = Decl.create_prsymbol (Ident.id_fresh name) in
  let task = Task.add_prop_decl task Decl.Pgoal pr (mk_cmp [] [] rcmp) in
  EcWhy3.para_call !current_provers (Global.Timeout.get ()) true name task

let my_check_computed_pr_cond name cond bound concl =
  let task = init_task () in
  (* Add already proved lemmas on global names *)
  let fv_cond = 
    List.fold_left (fun fv a -> EcTerm.Vset.union (EcTerm.fv_exp a) fv)
      (EcTerm.fv_exp concl) cond in
  let fv = 
    List.fold_left 
      (fun fv (e1,e2) ->
  EcTerm.Vset.union 
    (EcTerm.fv_exp e1) (EcTerm.Vset.union (EcTerm.fv_exp e2) fv))
      fv_cond bound in
  (* We build the goal *)
  let tenv,env,vs = EcTerm.add_why3_vars [] [] (EcTerm.Vset.elements fv) in
  let concl = EcTerm.form_of_exp tenv env concl in
  let concl = 
    List.fold_right (fun c concl ->
      Term.t_implies (EcTerm.form_of_exp tenv env c) concl) cond concl in
  let concl =
    List.fold_right (fun (x,b) concl ->
      let x = EcTerm.term_of_exp tenv env x in
      let b = EcTerm.term_of_exp tenv env b in
      Term.t_implies (Term.ps_app EcWhy3.ps_le_real [rzero;x])
        (Term.t_implies (Term.ps_app EcWhy3.ps_le_real [x;b]) concl))
      bound concl in
  let concl = Term.t_forall_close vs [] concl in 
  let pr = Decl.create_prsymbol (Ident.id_fresh name) in
  let task = Task.add_prop_decl task Decl.Pgoal pr concl in
  EcWhy3.para_call !current_provers (Global.Timeout.get ()) true name task

let check_computed_pr_cond name pr_list cond (bound, ep) le r =
  let task = init_task () in
  let pr_list = List.map snd (List.filter (fun (r,_) -> !r) pr_list) in
  let tbl = mk_name_tbl pr_list r in
  (* Add the globals names *)
  let task = add_tbl task tbl in
  (* Add already proved lemmas on global names *)
  let mk_term, mk_cmp = mk_form_of_real_exp tbl in
  let task =
    List.fold_left (fun task (name, e) ->
      let pr = Decl.create_prsymbol (Ident.id_fresh name) in
      Task.add_prop_decl task Decl.Paxiom pr (mk_cmp [] [] e)) task pr_list in
  let fv_cond = 
    List.fold_left (fun fv a -> EcTerm.Vset.union (EcTerm.fv_exp a) fv)
      EcTerm.Vset.empty cond in
  let fv = 
    List.fold_left 
      (fun fv (e1,e2) ->
  EcTerm.Vset.union 
    (EcTerm.fv_exp e1) (EcTerm.Vset.union (EcTerm.fv_exp e2) fv))
      (EcTerm.Vset.union fv_cond (EcTerm.fv_exp ep)) bound in
  (* We build the goal *)
  let tenv,env,vs = EcTerm.add_why3_vars [] [] (EcTerm.Vset.elements fv) in
  let concl = 
    let t1 = EcTerm.term_of_exp tenv env ep in
    let t2 = mk_term [] [] r in
    if le then Term.ps_app EcWhy3.ps_le_real [t1; t2]
    else Term.t_equ t1 t2 in
  let concl = 
    List.fold_right (fun c concl ->
      Term.t_implies (EcTerm.form_of_exp tenv env c) concl) cond concl in
  let concl =
    List.fold_right (fun (x,b) concl ->
      let x = EcTerm.term_of_exp tenv env x in
      let b = EcTerm.term_of_exp tenv env b in
      Term.t_implies (Term.ps_app EcWhy3.ps_le_real [rzero;x])
        (Term.t_implies (Term.ps_app EcWhy3.ps_le_real [x;b]) concl))
      bound concl in
  let concl = Term.t_forall_close vs [] concl in 
  let pr = Decl.create_prsymbol (Ident.id_fresh name) in
  let task = Task.add_prop_decl task Decl.Pgoal pr concl in
  EcWhy3.para_call !current_provers (Global.Timeout.get ()) true name task


let check_computed_pr name pr_list  = check_computed_pr_cond name pr_list []
 
(* let check ?(pp_failure=true) ?(goal_name="why_goal") p = *)
(*   check_why3 ~pp_failure ~goal_name p *)

(*
  let p = Fol.pclos p in
  let pp_goal fmt goal = PpLogic.pp_goal_why fmt goal_name goal in
  let why_file = export pp_goal p in
  WhyRun.check ~pp_failure goal_name why_file (get_prover_option())
(*  WhyRun.para_check ~timeout pp_failure goal_name why_file *)
*)

type hyp =
  | Hforall of Fol.lvar
  | Hlet of Fol.lvar list * Fol.term
  | Himplies of Fol.pred

(* type hyps = hyp list *)

let add_forall hyps x = Hforall x :: hyps
let add_let hyps x t = Hlet(x,t)::hyps
let add_hyp hyps p = Himplies p :: hyps

let implies_hyp p h =
  match h with
  | Hforall x -> Fol.forall_pred ~fresh:false x p
  | Hlet(x,t) -> Fol.let_pred ~fresh:false x t p
  | Himplies p' -> Fol.pimplies p' p

let implies_hyps hyps p =
  List.fold_left implies_hyp p hyps

let absurd_hyps ?(goal_name="absurd_branches") hyps =
  let p = implies_hyps hyps Fol.Pfalse in
  let timeout = max (Global.Timeout.get () / 2) 1 in
  check_why3 ~timeout ~pp_failure:false ~goal_name p

let check_split_opt stop_first ?(split_and=false) 
    ?(goal_name="why_goal") hyps p =
  let i = ref (-1) in
  let rec aux split_and hyps p =
    match p with
    | Fol.Pif(split_info, e,p1,p2) ->
        let ep = Fol.pred_of_term e in
        let nep = Fol.pnot ep in
        let thyps = add_hyp hyps ep in
        let fhyps = add_hyp hyps nep in
        let q1 =
          if split_info && absurd_hyps thyps then Fol.Ptrue
          else aux split_and thyps p1 in
        let q2 = 
          if stop_first && q1 <> Fol.Ptrue then p2
          else
            if split_info && absurd_hyps fhyps then Fol.Ptrue
            else aux split_and fhyps p2 in
        Fol.pif ~split_info e q1 q2
      | Fol.Pimplies(p1,p2) ->
        Fol.pimplies p1 (aux split_and (add_hyp hyps p1) p2)
      | Fol.Pforall(x,_,p) ->
        Fol.forall_pred ~fresh:false x (aux split_and (add_forall hyps x) p)
      | Fol.Plet(x,t,p) ->
        Fol.let_pred ~fresh:false x t (aux split_and (add_let hyps x t) p)
      | Fol.Pand(p1,p2) ->
        if split_and then
          let q1 = aux split_and hyps p1 in
          let q2 = 
            if stop_first && q1 <> Fol.Ptrue then p2
            else aux split_and hyps p2 in
          Fol.pand q1 q2 
        else
          let name = incr i;Format.sprintf "%s%i" goal_name !i in
          if check_why3 ~goal_name:name ~pp_failure:false
              (implies_hyps hyps p) 
          then Fol.Ptrue 
          else (decr i; aux true hyps p)
      | Fol.Piff(p1,p2) ->
        if split_and then
          aux split_and hyps 
            (Fol.pand (Fol.pimplies p1 p2) (Fol.pimplies p2 p1))
        else
          let name = incr i;Format.sprintf "%s%i" goal_name !i in
          if check_why3 ~goal_name:name ~pp_failure:false
              (implies_hyps hyps p) 
          then Fol.Ptrue 
          else (decr i;aux true hyps p)
      | _ -> 
        let name = incr i;Format.sprintf "%s%i" goal_name !i in
        if check_why3 ~goal_name:name (implies_hyps hyps p) then Fol.Ptrue 
        else p in
  aux split_and hyps p

let prove p = check_split_opt true [] p = Fol.Ptrue

let check_implies p1 p2 = 
  prove (Fol.pimplies p1 p2)

let simplify_post stop_first p1 p2 =
  check_split_opt stop_first ~goal_name:"implies_goal" [Himplies p1] p2


