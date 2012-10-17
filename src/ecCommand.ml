(** High level function to build and type check {!Ast} from the parser results.
    * Add the newly defined objects into the {!Global} environment.
*)

open EcUtil
open Ast


(** Types *)
let mk_type_exp = EcTyping.mk_type_exp

let process_type pos ((args,name), def_opt) =
  let tdef = EcTyping.mk_type_def pos args name def_opt in
  Global.add_type tdef
(*
  let def =
    match def_opt with
      | None -> None
      | Some def -> Some (mk_type_exp pos def) in
  Global.add_type { t_name = name; t_pos = pos; t_def = def } *)

(** Constants *)

let process_cnst pos ((name_list, typ), def_opt) =
  let poly, t = EcTyping.mk_poly_type_exp pos typ in
  let tv_assoc, wt = EcTerm.add_why3_type [] t in
  let def, wdef =
    match def_opt with
    | None -> None, None
    | Some def -> 
        let def = EcTyping.mk_cst_def poly t def in
        let wdef = EcTerm.term_of_exp tv_assoc [] def in
        Some def, Some wdef in
  
  let do_cnst name =
    let ls = 
      Why3.Term.create_lsymbol (Why3.Ident.id_fresh name) [] (Some wt) in
    let why3 = 
      match wdef with
      | None -> ls, None
      | Some t -> Why3.Decl.make_ls_defn ls [] t in
    Global.add_cnst 
      { c_name = name; 
        c_poly = poly; c_type = t; c_pos = pos; c_def = def;
        c_why3 = why3; c_native_why = false
      } in
  List.iter do_cnst name_list

(** Operators *)
let process_op assoc prec pos (infix,op_name) body why_name =
  let op_sig, op_body = 
    match body with
      | AstYacc.OpDecl op_sig -> EcTyping.mk_op_sig pos op_sig, None
      | AstYacc.OpDef (params, body) -> 
        let op_sig, op_body = EcTyping.mk_op_def pos params body in
        op_sig, Some op_body in
  let why_name = 
    match why_name with
      | None -> 
        if infix then
          pos_error pos "infix operator should be declared with why name";
        (op_name,false)
      | Some id -> (id,false) in
  let ob = EcTerm.mk_op_body 
    op_name None why_name op_sig op_body infix pos assoc prec in
  Global.add_op ~prob:false ob

let process_pop pos (pop_name, body) = 
  let pop_sig, pop_body = 
    match body with 
      | AstYacc.PopDecl pop_sig ->  
        let op_sig = EcTyping.mk_op_sig pos pop_sig in
        (snd op_sig :: fst op_sig, Ast.Treal), None
      | AstYacc.PopDef (params, (param,t), body) -> 
        let pop_sig, pop_body = EcTyping.mk_pop_def pos params (param,t) body in
        pop_sig, Some pop_body
  in
  let why_name = ("\\should_not_be_used//_" ^ pop_name, false) in
  let ob = 
    EcTerm.mk_op_body pop_name None why_name pop_sig pop_body false pos None 0 in
  Global.add_op ~prob:true ob
  

(** Predicates *)
let process_pred _pos (name, decl, body) =
  let pred = EcTyping.mk_predicate decl body in
  Global.add_predicate name pred

let process_apred pos (name, dom) =
  let dom = EcTyping.mk_apredicate (pos, dom) in
    Global.add_apredicate name dom

(** Axioms and Lemmas *)
let process_axiom _pos (name, is_axiom, p) =
  let ax = EcTyping.mk_axiom p in
  if is_axiom || not (Global.withproof ()) then Global.add_axiom true name ax
  else
    if WhyCmds.check_why3 ~goal_name:name ax then
      Global.add_axiom false name ax
    else user_error "Couldn't not prove %s" name
    


(** Adversaries *)
let process_adv pos adv =
  let adv = EcTyping.mk_adv_decl pos adv in
  Global.add_adv adv

(** Table of functions ast : useful for redefinition *)

let ast_fct_tbl = Hashtbl.create 100

let find_ast_fct pos name qualid =
  try
    match Hashtbl.find ast_fct_tbl qualid with
      | AstYacc.PEfun((_,decl,t_res),f_body) ->
        AstYacc.PEfun(((pos,name),decl,t_res),f_body)
      | AstYacc.PEabs(_,nadv,oracles) ->
        AstYacc.PEabs(name,nadv,oracles)
      | AstYacc.PEvar _ -> bug "get_ast_fct: PEvar"
      | AstYacc.PEredef _ -> bug "get_ast_fct: PEredef"
  with _ ->
    pos_error pos "Unknow function %s.%s" (fst qualid) (snd qualid)

let add_ast_fct fct pg_elem =
  let gname = fct.f_game.g_name in
  let fname = fct.f_name in
  Hashtbl.add ast_fct_tbl (gname,fname) pg_elem


(** Program element *)
let rec process_pg_elem (pos, pg_elem) =
  match pg_elem with
    | AstYacc.PEvar (name_list, t) ->
      let t = mk_type_exp pos t in
      let do_var (pos, name) = Global.add_global pos name t in
      List.iter do_var name_list
    | AstYacc.PEfun (f_decl, f_body) ->
      let game = Global.cur_game " process_pg_elem" in
      let fpos, name, params, t_res, body =
        EcTyping.mk_fct game pos f_decl f_body in
      let fct = Global.add_fct fpos name params t_res body in
      add_ast_fct fct pg_elem
    | AstYacc.PEredef(name, qualid) ->
      let pg_elem = find_ast_fct pos name qualid in
      process_pg_elem (pos, pg_elem)
    | AstYacc.PEabs (name, nadv, oracles) ->
      let adv = Global.find_adv nadv pos in
      let body = EcTyping.mk_adv_body pos adv oracles in
      let params = List.map
        (fun v -> EcTerm.mk_local v.v_name v.v_type pos)
        adv.adv_param
      in
      let fct = Global.add_fct pos name params adv.adv_res body in
      add_ast_fct fct pg_elem


(** Game *)
let process_game pos (game_name, game_body) =
  Global.start_game game_name pos;
  try
    begin match game_body with
      | AstYacc.PGdef pg_elem_list ->
        List.iter (process_pg_elem) pg_elem_list
      | AstYacc.PGredef (other_game, (remove, add), redef_list) ->
        let old_g =
          try Global.find_game other_game
          with Not_found ->
            pos_error pos "Couldn't find game '%s' to define '%s'"
              other_game game_name in
        let old_name = old_g.g_name in
        let remove = List.map snd remove in
        List.iter (fun (name, v) ->
          if not (List.mem name remove) then
            Global.add_global pos name v.v_type)
          old_g.g_vars;
        List.iter (fun (name_list, t) ->
          process_pg_elem (pos, AstYacc.PEvar (name_list, t))) add;
        let process_fct (name, _) =
          let pg_elem =
            try
              let body = List.assoc name redef_list in
              match find_ast_fct pos name (old_name, name) with
                | AstYacc.PEfun(decl, _) -> AstYacc.PEfun(decl, body)
                | AstYacc.PEabs _ -> pos_error pos "Couldn't define adversary"
                | _ -> assert false
            with Not_found ->
              AstYacc.PEredef(name, (old_name, name)) in
          process_pg_elem (pos, pg_elem) in
        List.iter process_fct old_g.g_functions
    end;
    Global.close_game ()
  with e -> Global.abort_game (); raise e

(** Annotation : build it and call {!EcDeriv} *)
let pp_cur_goal no_more =
  Format.printf "%a@." EcDeriv.pp_cur_goal no_more


(* TODO: I added just None in this case, don't know to which extent we use app *)

let rec process_claim pos (name, ((pe,h) as c)) = 
  match h with
  | AstYacc.Hauto ->
      let (e,_ as cl) = EcTyping.mk_claim pos (pe,AstYacc.Hnone) in
      if Global.withproof () then
        let (op,f1,e1,f2,e2) = 
          match e with
          | Eapp(op,[Ebase(f1, e1);Ebase(f2, e2)]) ->
              op, f1, e1, f2, e2 
          | _ ->
              user_error "do not know how to infer an equivalence relation" in
        let te1 = Fol.term_of_exp Fol.FVleft e1 in
        let te2 = Fol.term_of_exp Fol.FVright e2 in
        let post = 
          if EcTerm.is_op EQ op then Fol.peq te1 te2 
          else if EcTerm.is_op REAL_LE op then 
            Fol.pimplies (Fol.pred_of_term te1) (Fol.pred_of_term te2)
          else user_error "do not know how to infer an equivalence relation" in
        let inv = AstLogic.Inv_global (EcTyping.mkeq_globals f1 f2) in
        let pre,_ = FunLogic.build_inv_spec inv f1 f2 in
        let spec = EcStrategy.equiv_fct (inv,[]) f1 f2 pre post in
        let name = EcDeriv.spec_name spec in
        EcStrategy.proba true name (e, AstLogic.Pr_equiv name)
      else
        EcStrategy.proba false name cl
  | _ ->
      let cl = EcTyping.mk_claim pos c in
      EcStrategy.proba (Global.withproof ()) name cl


let process_equiv pos (name,f1,f2,concl,auto) = 
  let (f1,f2,pre,post,app as equiv) = EcTyping.mk_equiv pos f1 f2 concl in
  if Global.withproof() then 
    match auto, app with
    | None, _ ->
        EcStrategy.open_equiv name equiv;
        Format.printf "Proving %a@." EcDeriv.pp_cur_spec ();
        pp_cur_goal true
    | Some _, Some _ ->
        not_implemented "process_equiv : approx auto"
    | Some info, None ->
        match info with
        | AstLogic.Helper_inv (Some _, _ as info) ->
            let inv = EcTyping.mk_info f1 f2 info in
            ignore (EcStrategy.equiv_fct ~find:false
                      ~name:(Some name) inv f1 f2 pre post)
        | AstLogic.Helper_inv (None, l) ->
            let inv = 
              match concl with
              | AstYacc.Aequiv_inv inv -> Some inv
              | _ -> None in
            let inv = EcTyping.mk_info f1 f2 (inv,l) in
            ignore (EcStrategy.equiv_fct ~find:false 
                      ~name:(Some name) inv f1 f2 pre post)
        | AstLogic.Helper_eager s ->
            let s = EcTyping.mk_eager f1 f2 s in
            EcStrategy.eager name equiv s;
            pp_cur_goal true
  else
    begin
      EcStrategy.open_equiv name equiv;
      let sg = EcDeriv.cur_tac EcDeriv.admit_tac in
      Format.printf "length sg = %i@." (List.length sg);
      assert (sg = []); 
      EcDeriv.save ()
    end
      
      

let process_axiom _pos (name, is_axiom, p) =
  let ax = EcTyping.mk_axiom p in
  if is_axiom || not (Global.withproof ()) then Global.add_axiom true name ax
  else
    if WhyCmds.check_why3 ~goal_name:name ax then
      Global.add_axiom false name ax
    else user_error "Couldn't not prove %s" name






let rec get_inv pexp = 
  assert (not (EcTerm.is_var_exp pexp));
  match pexp with
    | Ernd _ -> (fun x -> x), pexp
    | Eapp (op,[t1;t2]) 
        when EcTerm.eq_op op Global.op_real_add && 
             EcTerm.is_var_exp t1 -> 
      let finv, pexp = get_inv t2 in
      (fun x -> finv (Eapp(Global.op_real_sub,[x;t1]))), pexp
    | Eapp (op,[t2;t1]) 
        when EcTerm.eq_op op Global.op_real_add && 
             EcTerm.is_var_exp t1 -> 
      let finv, pexp = get_inv t2 in
      (fun x -> finv (Eapp(Global.op_real_sub,[x;t1]))), pexp
    | Eapp (op,[t1;t2]) 
        when EcTerm.eq_op op Global.op_int_add && 
             EcTerm.is_var_exp t1 -> 
      let finv, pexp = get_inv t2 in
      (fun x -> finv (Eapp(Global.op_int_sub,[x;t1]))), pexp
    | Eapp (op,[t2;t1]) 
        when EcTerm.eq_op op Global.op_int_add && 
             EcTerm.is_var_exp t1 -> 
      let finv, pexp = get_inv t2 in
      (fun x -> finv (Eapp(Global.op_int_sub,[x;t1]))), pexp
    | Eapp (op,_)
      -> cannot_apply "get_inv" "cannot compute inverse function for %a" PpAst.pp_op op
    | _ -> cannot_apply "get_inv" "cannot compute inverse function for %a" PpAst.pp_exp pexp


let prove_popspec name
    ((largvars,argvars),(l_x1,pexp1,cond1),
     (l_x2,pexp2,cond2),(pre,post,app):Fol.pop_spec) =
  begin
    match cond1, cond2 with None, None -> () | _ -> not_implemented "prove_popspec"
  end;
  match post with 
    | Fol.Papp (pred, [t1;t2]) when Fol.is_eq_pred pred && 
        ((Fol.eq_term t1 (Ebase l_x1) && Fol.eq_term t2 (Ebase l_x2)) ||
            (Fol.eq_term t1 (Ebase l_x2) && Fol.eq_term t2 (Ebase l_x1))) ->
      let (f_inv1,pexp1), (f_inv2,pexp2) = get_inv pexp1, get_inv pexp2 in
      begin
        match pexp1, pexp2 with
          | Ernd (Rapp(op1,es1)), Ernd (Rapp(op2,es2)) when EcTerm.eq_op op1 op2 ->
            begin
              let (_,op1,_), (_,op2,_) = op1, op2 in
              match op1.op_body, op2.op_body with
                | Some (vs1,e1), Some (vs2,e2) ->
                  let alpha,delta = match app with
                    | Some (alpha,delta) -> alpha,delta
                    | None -> Global.rone, Global.rzero
                  in
                  (* let leq = Global.find_predicate "<=" in *)
                  let z1 = List.hd vs1 in
                  let z2 = List.hd vs2 in
                  let vs1 = List.tl vs1 in
                  let vs2 = List.tl vs2 in
                  assert (EcTerm.seq_type z1.v_type z2.v_type);
                  let z = Fol.logic_lvar "l" z1.v_type in
                  let f_inv1_z1 = Fol.term_of_exp Fol.FVleft (f_inv1 (Ebase z1)) in
                  let f_inv2_z2 = Fol.term_of_exp Fol.FVright (f_inv2 (Ebase z2)) in
                  let f_inv1_z = Fol.subst_var_in_term (Fol.lvar_of_var z1 Fol.FVleft) (Ebase z) f_inv1_z1 in
                  let f_inv2_z = Fol.subst_var_in_term (Fol.lvar_of_var z2 Fol.FVright) (Ebase z) f_inv2_z2 in
                  (* let t = Fol.term_of_exp side e in *)
                  let f side t = 
                    List.fold_left 
                      (fun t (v,lv) -> (Fol.subst_var_in_term (Fol.lvar_of_var v side) (Ebase lv) t)) t 
                      (List.combine argvars largvars)
                  in
                  let f_inv1_z = f Fol.FVleft f_inv1_z in
                  let f_inv2_z = f Fol.FVright f_inv2_z in
                  let ts1:Fol.term list = List.map (Fol.term_of_exp Fol.FVleft) es1 in
                  let ts2:Fol.term list  = List.map (Fol.term_of_exp Fol.FVright) es2 in
                  let ts1:Fol.term list = List.map (f Fol.FVleft) ts1 in
                  let ts2:Fol.term list  = List.map (f Fol.FVright) ts2 in
                  let t1:Fol.term = Fol.term_of_exp Fol.FVleft e1 in
                  let t1:Fol.term = List.fold_left (fun t (lv,t') -> Fol.subst_var_in_term lv t' t) t1 
                    (List.combine (List.map (fun v -> Fol.lvar_of_var v Fol.FVleft) vs1) ts1) in
                  let t2:Fol.term = Fol.term_of_exp Fol.FVright e2 in
                  let t2:Fol.term = List.fold_left (fun t (lv,t') -> Fol.subst_var_in_term lv t' t) t2 
                    (List.combine (List.map (fun v -> Fol.lvar_of_var v Fol.FVright) vs2) ts2) in
                  let t2:Fol.term = Eapp (Global.op_real_add,[Eapp(Global.op_real_mul,[alpha;t2]);delta]) in
                  let p:Fol.pred = Fol.Pterm(Eapp(Global.op_real_le,[t1;t2])) in 
                  let p = Fol.subst_in_pred (Fol.lvar_of_var z1 Fol.FVleft) f_inv1_z p in
                  let p = Fol.subst_in_pred (Fol.lvar_of_var z2 Fol.FVright) f_inv2_z p in
                  Format.printf "Prove @[%a@]@\n" Fol.pp_pred (Fol.pimplies pre p); 
                  WhyCmds.check_why3 ~goal_name:name (Fol.pimplies pre p)
                | None , _ | _, None -> user_error "Undefined pop operator"
            end
          | _ -> false
      end
    | _ -> false





let process_popspec _pos (name, is_axiom, popspec) =
  let popspec = EcTyping.mk_popspec popspec in
  if is_axiom || not (Global.withproof ()) then
    Global.add_popspec (* true *) name popspec
  else
    if prove_popspec name popspec then
      Global.add_popspec (* false *) name popspec
    else user_error "Couldn't not prove %s" name

let process_pop_aspec _pos (name, pop_aspec) =
  let pop_aspec = EcTyping.mk_pop_aspec pop_aspec in
  Global.add_pop_aspec name pop_aspec

(* let process_popwpspec _pos (name, popwpspec) = *)
(*   let popwpspec = EcTyping.mk_popwpspec popwpspec in *)
(*   Global.add_popwpspec name popwpspec *)

(* let process_pred _pos (name, decl, body) = *)
(*   let pred = EcTyping.mk_predicate decl body in *)
(*   Global.add_predicate name pred *)

let process_save _ =
  if Global.withproof() then
    (EcDeriv.save (); pp_cur_goal false)

let process_abort _ =
  if Global.withproof() then
    let s = EcDeriv.abort () in
    Format.printf "Abort %s@." s;
    pp_cur_goal false

module T = EcDeriv
module S = EcStrategy

let process_tac _pos tac =
  let rec aux1 tac lg =
    try
      match tac with
        | AstLogic.Tsubgoal lt -> T.subgoal_tac (List.map aux2 lt) lg
        | _ -> T.on_subgoal_tac (aux2 tac) lg
    with e -> List.iter (fun g -> ignore (T.reset_tac g)) lg; raise e
  and aux2 tac =
    match tac with
      | AstLogic.Tidtac -> T.id_tac 
      | AstLogic.Tcall info -> S.wp_call_tac info 
      | AstLogic.Tinline info -> S.inline_tac info
      | AstLogic.Tasgn -> T.wp_asgn_tac
      | AstLogic.Trnd (way,info) -> S.rnd_tac (way,info)
      | AstLogic.Tswap info -> T.swap_tac info
      | AstLogic.Ttrivial -> S.trivial_tac
      | AstLogic.Teqobsin (geqs,inv,eqs,l) -> 
          S.eqobs_in_tac geqs inv eqs l
      | AstLogic.Tauto info -> S.auto_tac info
      | AstLogic.Twp info -> T.wp_simpl_tac ~pos:info
      | AstLogic.Tsp info -> T.sp_simpl_tac ~pos:info
      | AstLogic.Tautosync -> S.autosync_tac
      | AstLogic.Tderandomize s -> S.derandomize_tac s
      | AstLogic.Tcase info -> T.case_tac info
      | AstLogic.Tif info -> T.cond_tac info
      | AstLogic.Tifsync info -> S.ifsync_tac info
      | AstLogic.Tifneg info -> S.ifneg_tac info
      | AstLogic.Treduce info -> S.reduce_cond_tac info
      | AstLogic.Twhile info -> S.while_tac info
      | AstLogic.TwhileApp info -> T.whileapp_tac info
      | AstLogic.Tunroll info -> S.unroll_tac info
      | AstLogic.Tsplitwhile info -> S.splitwhile_tac info
      | AstLogic.Tpopspec info -> T.popspec_tac info
      | AstLogic.Tprhl -> T.prhl_tac
      | AstLogic.Taprhl -> T.aprhl_tac
      | AstLogic.TwhileAppGen info -> T.whileappgen_tac info
      | AstLogic.Tapp(k1,k2,p,app) -> S.app_tac (k1,k2) p app
      | AstLogic.Tset info -> S.set_tac info
      | AstLogic.Tadmit -> T.admit_tac
      | AstLogic.Ttry tac -> T.try_tac (aux2 tac)
      | AstLogic.Tseq (tac1, tac2) ->
        (fun g ->
          try aux1 tac2 (aux2 tac1 g)
          with e -> ignore (T.reset_tac g); raise e)
      | AstLogic.Trepeat tac -> T.repeat_tac (aux2 tac)
      | AstLogic.Tdo(n,tac) -> T.do_tac n (aux2 tac)
      | AstLogic.Tsubgoal _ -> fun g -> aux1 tac [g] 
      | AstLogic.Tunfold l -> T.unfold_tac l 
      | AstLogic.Tsimplify_post -> S.prove_tac
  in  
  if Global.withproof() then
    (ignore (T.cur_tac (aux2 tac)); pp_cur_goal true)

let process_undo global depth proof timeout tactic =
  EcDeriv.un_save depth;
  Global.restore_global global;
  Global.set_timeout timeout;
  Global.set_withproof (if proof = "T" then true else false);
  EcDeriv.forget_all_from tactic; pp_cur_goal false

let process_check name = 
  Global.find_and_show_cnst name;
  Global.find_and_show_op   name;
  Global.find_and_show_pop  name;
  Global.find_and_show_adv  name

let process_print info = 
  match info with
  | AstYacc.Pi_string name ->
      Global.find_and_show_type name;
      Global.find_and_show_game name;
      Global.find_and_show_axiom name;
      Global.find_and_show_pred name;
      Global.find_and_show_op name;
      Global.find_and_show_pop name
  | AstYacc.Pi_fct f -> Global.find_and_show_fct f
  | AstYacc.Pi_set_axiom b -> Global.print_set_axiom b
  | AstYacc.Pi_all_axiom -> Global.print_all_axiom ()
  | AstYacc.Pi_all_op -> Global.print_all_op ()
  | AstYacc.Pi_all_cnst -> Global.print_all_cnst ()
  | AstYacc.Pi_all_pred -> Global.print_all_pred ()
  | AstYacc.Pi_all_type -> Global.print_all_type ()

let process_set_all b =
  Global.set_all_axiom b

let process_set b s =
  if b then Global.set_axiom s else Global.unset_axiom s;
  if b then EcProba.set_Pr s else EcProba.unset_Pr s

let rec process_file path src =
  let src = Filename.concat path src in
  let path = Filename.dirname src in
  let lexbuf = EcLexer.new_lexbuf (Some src) in
  try parse_and_add false path lexbuf
  with StopParsing -> () (* either a Drop global command or EOF *)
and parse_and_add top path lexbuf =
  if top then begin
    EcUtil.print_prompt 
        (Global.get_num_instr ()) 
        (EcDeriv.get_proof_depth ())
        (if Global.withproof () then "T" else "F")
        (Global.get_timeout ())
        (!EcDeriv.rhl_cntr ); 
  end;
  let ast, stop = EcLexer.read lexbuf in
  Parsing.clear_parser (); (*Could be not necessary this line. I'm no sure*)
  if top then Lexing.flush_input lexbuf;
  List.iter (process_global path) ast;
  if stop then raise StopParsing
  else parse_and_add top path lexbuf
and process_global path (pos, g) = 
  begin
    match g with
      | AstYacc.Ginclude filename -> process_file path filename
      | AstYacc.Gtype type_decl -> process_type pos type_decl
      | AstYacc.Gcnst cnst_decl -> process_cnst pos cnst_decl
      | AstYacc.Gop (pos, (assoc, prec, id, decl, why)) -> 
          process_op assoc prec pos id decl why 
      | AstYacc.Gpop op_decl -> process_pop pos op_decl  
      | AstYacc.Gpred pred -> process_pred pos pred
      | AstYacc.Gapred apred -> process_apred pos apred
      | AstYacc.Gaxiom ax -> process_axiom pos ax
      | AstYacc.Ggame game -> process_game pos game
      | AstYacc.Gclaim claim -> process_claim pos claim;
      | AstYacc.Gadv adv -> process_adv pos adv
      | AstYacc.Gpop_spec popspec -> process_popspec pos popspec
      | AstYacc.Gpop_aspec pop_aspec -> process_pop_aspec pos pop_aspec
      | AstYacc.Gset (b,s) -> process_set b s
      | AstYacc.Gset_all b -> process_set_all b
      | AstYacc.Gequiv equiv -> process_equiv pos equiv
      | AstYacc.Gtactic tac -> process_tac pos tac
      | AstYacc.Gsave -> process_save pos
      | AstYacc.Gabort -> process_abort pos
      | AstYacc.Gprover prover -> 
          WhyCmds.set_prover_option prover
      | AstYacc.Gtimeout n ->  Global.set_timeout n
      | AstYacc.Gwithproof -> Global.change_withproof()
      | AstYacc.Gopacity(b,names) -> 
          let set_opacity name =
            try 
              let pr = Global.find_predicate name in
              Fol.set_opacity b pr 
            with Not_found ->
              pos_error pos "unknow predicate %s" name in
          List.iter set_opacity names
      |  _ -> ()
  end ;
  match g with
    (** This functions not change the global state (in global) *)
    | AstYacc.Gundo (global,depth,proof,timeout,tactic) -> 
      process_undo global depth proof timeout tactic
    | AstYacc.Gcheck name -> process_check name
    | AstYacc.Gprint info -> process_print info
    | AstYacc.Gtactic _ -> ()
    (** For all the other function we save the state for future undo's *)
    | _ -> Global.save_global ()
      

let parse_equiv _str = not_implemented "EcCommand : parse_equiv"
(*
  let (pos, ast) =  EcLexer.read_glob str in
  match ast with
    | AstYacc.Gequiv (name, equiv) -> name, EcTyping.mk_equiv pos equiv
    | _ -> user_error "This is not an 'equiv' property"
*)
let parse_rnd_info str =
  let str = "rnd "^str in
  let (_pos, ast) =  EcLexer.read_glob str in
  match ast with
    | AstYacc.Gtactic (AstLogic.Trnd (AstLogic.Backwards,rnd_info)) -> rnd_info
    | AstYacc.Gtactic (AstLogic.Trnd (_,_)) -> 
      not_implemented "parse_rnd_info:Forwards"
    | _ -> user_error "This is not a 'rnd_info' expression"


(** Parse the standard input and catch errors *)
(*   When an exception happen the unprocessed part will be lost
 * because we lost the reference. This is the reason for create
 * the lexbuf inside 'try' instead of create before 'try'. 
 *   In this context, we don't need to 'wait' for the end of the
 * command *)
let parse () =
  let rec parse_and_catch () =
    try
       let lexbuf = Lexing.from_channel stdin in
        parse_and_add true "" lexbuf
    with 
      | StopParsing -> ()
      | e -> catch_exn e; parse_and_catch ()
  in parse_and_catch ()


(** Set up a flag to know that the output is for emacs.
 * Save the current state for the undo  *)
let emacs_parse () =
  EcUtil.set_emacs_mode true;
  parse ()


(** Parse a file starting form the current env. Catch error if any. *)
let parse_file filename =
  try process_file "" filename
  with e -> catch_exn e

let parse_files filenames =
  List.iter (process_file "") filenames
  (* try List.iter (process_file "") filenames *)
  (* with e -> catch_exn e *)
