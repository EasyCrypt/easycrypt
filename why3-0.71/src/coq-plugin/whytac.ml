(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Names
open Nameops
open Term
open Termops
open Tacmach
open Util
open Coqlib
open Hipattern
open Typing
open Libnames
open Declarations
open Pp

open Why3
open Call_provers
open Whyconf
open Ty
open Term

let debug =
  try let _ = Sys.getenv "WHYDEBUG" in true
  with Not_found -> false

let config = Whyconf.read_config None
let main = Whyconf.get_main config
let cprovers = Whyconf.get_provers config

let timelimit = timelimit main

let env = Lexer.create_env (loadpath main)

let provers = Hashtbl.create 17

let get_prover s =
  try
    Hashtbl.find provers s
  with Not_found ->
    let cp = Util.Mstr.find s cprovers in
    let drv = Driver.load_driver env cp.driver in
    Hashtbl.add provers s (cp, drv);
    cp, drv

let print_constr fmt c = pp_with fmt (Termops.print_constr c)
let print_tvm fmt m =
  Idmap.iter (fun id tv -> Format.fprintf fmt "%s->%a@ "
                 (string_of_id id) Why3.Pretty.print_tv tv) m
let print_bv fmt m =
  Idmap.iter (fun id vs -> Format.fprintf fmt "%s->%a@ "
                 (string_of_id id) Why3.Pretty.print_vsty vs) m

(* Coq constants *)
let logic_dir = ["Coq";"Logic";"Decidable"]

let coq_modules =
  init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules
    @ [["Coq"; "ZArith"; "BinInt"];
       ["Coq"; "Reals"; "Rdefinitions"];
       ["Coq"; "Reals"; "Raxioms";];
       ["Coq"; "Reals"; "Rbasic_fun";];
       ["Coq"; "Reals"; "R_sqrt";];
       ["Coq"; "Reals"; "Rfunctions";]]
    @ [["Coq"; "omega"; "OmegaLemmas"]]

let constant = gen_constant_in_modules "why" coq_modules

let coq_Z = lazy (constant "Z")
let coq_Zplus = lazy (constant "Zplus")
let coq_Zmult = lazy (constant "Zmult")
let coq_Zopp = lazy (constant "Zopp")
let coq_Zminus = lazy (constant "Zminus")
let coq_Zdiv = lazy (constant "Zdiv")
let coq_Zs = lazy (constant "Zs")
let coq_Zgt = lazy (constant "Zgt")
let coq_Zle = lazy (constant "Zle")
let coq_Zge = lazy (constant "Zge")
let coq_Zlt = lazy (constant "Zlt")
let coq_Z0 = lazy (constant "Z0")
let coq_Zpos = lazy (constant "Zpos")
let coq_Zneg = lazy (constant "Zneg")
let coq_xH = lazy (constant "xH")
let coq_xI = lazy (constant "xI")
let coq_xO = lazy (constant "xO")

let coq_R = lazy (constant "R")
let coq_R0 = lazy (constant "R0")
let coq_R1 = lazy (constant "R1")
let coq_Rgt = lazy (constant "Rgt")
let coq_Rle = lazy (constant "Rle")
let coq_Rge = lazy (constant "Rge")
let coq_Rlt = lazy (constant "Rlt")
let coq_Rplus = lazy (constant "Rplus")
let coq_Rmult = lazy (constant "Rmult")
let coq_Ropp = lazy (constant "Ropp")
let coq_Rinv = lazy (constant "Rinv")
let coq_Rminus = lazy (constant "Rminus")
let coq_Rdiv = lazy (constant "Rdiv")
let coq_powerRZ = lazy (constant "powerRZ")

let coq_iff = lazy (constant "iff")

let is_constant t c = try t = Lazy.force c with _ -> false

(* not first-order expressions *)
exception NotFO

(* the task under construction *)
let task = ref None

let why_constant path t s =
  let th = Env.find_theory env path t in
  task := Task.use_export !task th;
  Theory.ns_find_ls th.Theory.th_export s

(* coq_rename_vars env [(x1,t1);...;(xn,tn)] renames the xi outside of
   env names, and returns the new variables together with the new
   environment *)
let coq_rename_vars env vars =
  let avoid = ref (ids_of_named_context (Environ.named_context env)) in
  List.fold_right
    (fun (na,t) (newvars, newenv) ->
       let id = next_name_away na !avoid in
       avoid := id :: !avoid;
       id :: newvars, Environ.push_named (id, None, t) newenv)
    vars ([],env)

let coq_rename_var env (na,t) =
  let avoid = ids_of_named_context (Environ.named_context env) in
  let id = next_name_away na avoid in
  id, Environ.push_named (id, None, t) env

let preid_of_id id = Ident.id_fresh (string_of_id id)

(* rec_names_for c [|n1;...;nk|] builds the list of constant names for
   identifiers n1...nk with the same path as c, if they exist; otherwise
   raises Not_found *)
let rec_names_for c =
  let mp,dp,_ = Names.repr_con c in
  array_map_to_list
    (function
       | Name id ->
           let c' = Names.make_con mp dp (label_of_id id) in
           ignore (Global.lookup_constant c');
           (* msgnl (Printer.pr_constr (mkConst c')); *)
           c'
       | Anonymous ->
           raise Not_found)

(* extract the prenex type quantifications i.e.
   type_quantifiers env (A1:Set)...(Ak:Set)t = A1...An, (env+Ai), t *)
let decomp_type_quantifiers env t =
  let rec loop vars t = match kind_of_term t with
    | Prod (n, a, t) when is_Set a || is_Type a ->
        loop ((n,a) :: vars) t
    | _ ->
        let vars, env = coq_rename_vars env vars in
        let t = substl (List.map mkVar vars) t in
        let add m id =
          let tv = Ty.create_tvsymbol (preid_of_id id) in
          Idmap.add id tv m, tv
        in
        Util.map_fold_left add Idmap.empty vars, env, t
  in
  loop [] t

(* decomposes the first n type lambda abstractions correspondings to
   the list of type variables vars *)
let decomp_type_lambdas tvm env vars t =
  let rec loop tvm env vars t = match vars, kind_of_term t with
    | [], _ ->
        tvm, env, t
    | tv :: vars, Lambda (n, a, t) when is_Set a || is_Type a ->
        let id, env = coq_rename_var env (n, a) in
        let t = subst1 (mkVar id) t in
        let tvm = Idmap.add id tv tvm in
        loop tvm env vars t
    | _ ->
        assert false (*TODO: eta-expansion*)
  in
  loop tvm env vars t

let decompose_arrows =
  let rec arrows_rec l c = match kind_of_term c with
    | Prod (_,t,c) when not (dependent (mkRel 1) c) -> arrows_rec (t :: l) c
    | Cast (c,_,_) -> arrows_rec l c
    | _ -> List.rev l, c
  in
  arrows_rec []

let decomp_lambdas _dep _tvm bv env vars t =
  let rec loop bv vsl env vars t = match vars, kind_of_term t with
    | [], _ ->
        (bv, List.rev vsl), env, t
    | ty :: vars, Lambda (n, a, t) ->
        let id, env = coq_rename_var env (n, a) in
        let t = subst1 (mkVar id) t in
        let vs = create_vsymbol (preid_of_id id) ty in
        let bv = Idmap.add id vs bv in
        loop bv (vs :: vsl) env vars t
    | _ ->
        assert false (*TODO: eta-expansion*)
  in
  loop bv [] env vars t



let rec skip_k_args k cl = match k, cl with
  | 0, _ -> cl
  | _, _ :: cl -> skip_k_args (k-1) cl
  | _, [] -> raise NotFO

(* Coq globals *)

(* Coq reference -> symbol *)
let global_ts = ref Refmap.empty
let global_ls = ref Refmap.empty

(* polymorphic arity (i.e. number of type variables) *)
let poly_arity = ref Mls.empty
let add_poly_arith ls n = poly_arity := Mls.add ls n !poly_arity
let get_poly_arity ls = assert (Mls.mem ls !poly_arity); Mls.find ls !poly_arity

(* ident -> decl *)
let global_decl = ref Ident.Mid.empty

(* dependencies: decl -> decl list *)
let global_dep = ref Decl.Mdecl.empty

let local_decl = ref Decl.Sdecl.empty

let rec add_local_decls d =
  if not (Decl.Sdecl.mem d !local_decl) then begin
    local_decl := Decl.Sdecl.add d !local_decl;
    assert (Decl.Mdecl.mem d !global_dep);
    let dep = Decl.Mdecl.find d !global_dep in
    Decl.Sdecl.iter add_local_decls dep;
    try
      task := Task.add_decl !task d
    with Decl.UnknownIdent id ->
      Format.eprintf "unknown ident %s@." id.Ident.id_string; exit 42
  end

let empty_dep () = ref Decl.Sdecl.empty
let add_dep r v = r := Decl.Sdecl.add v !r

let print_dep fmt =
  let print1 d dl =
    Format.fprintf fmt "@[%a -> @[%a@]@]@\n" Pretty.print_decl d
      (Pp.print_list Pp.newline Pretty.print_decl) (Decl.Sdecl.elements dl)
  in
  Decl.Mdecl.iter print1 !global_dep

(* synchronization *)
let () =
  Summary.declare_summary "Why globals"
    { Summary.freeze_function =
        (fun () ->
           !global_ts, !global_ls, !poly_arity, !global_decl, !global_dep);
      Summary.unfreeze_function =
        (fun (ts,ls,pa,gdecl,gdep) ->
           global_ts := ts; global_ls := ls; poly_arity := pa;
           global_decl := gdecl; global_dep := gdep);
      Summary.init_function =
        (fun () ->
           global_ts := Refmap.empty;
           global_ls := Refmap.empty;
           poly_arity := Mls.empty;
           global_decl := Ident.Mid.empty;
           global_dep := Decl.Mdecl.empty);
      Summary.survive_module = true;
      Summary.survive_section = true;
    }

let lookup_table table r = match Refmap.find r !table with
  | None -> raise NotFO
  | Some d -> d

let add_table table r v = table := Refmap.add r v !table

(* Arithmetic constants *)

exception NotArithConstant

(* translates a closed Coq term p:positive into a FOL term of type int *)

let big_two = Big_int.succ_big_int Big_int.unit_big_int

let rec tr_positive p = match kind_of_term p with
  | Construct _ when is_constant p coq_xH ->
      Big_int.unit_big_int
  | App (f, [|a|]) when is_constant f coq_xI ->
      (* Plus (Mult (Cst 2, tr_positive a), Cst 1) *)
      Big_int.succ_big_int (Big_int.mult_big_int big_two (tr_positive a))
  | App (f, [|a|]) when is_constant f coq_xO ->
      (* Mult (Cst 2, tr_positive a) *)
      Big_int.mult_big_int big_two (tr_positive a)
  | Cast (p, _, _) ->
      tr_positive p
  | _ ->
      raise NotArithConstant

let const_of_big_int b = Term.t_int_const (Big_int.string_of_big_int b)

(* translates a closed Coq term t:Z or R into a FOL term of type int or real *)
let rec tr_arith_constant t = match kind_of_term t with
  | Construct _ when is_constant t coq_Z0 ->
      Term.t_int_const "0"
  | App (f, [|a|]) when is_constant f coq_Zpos ->
      const_of_big_int (tr_positive a)
  | App (f, [|a|]) when is_constant f coq_Zneg ->
      const_of_big_int (Big_int.minus_big_int (tr_positive a))
  | Const _ when is_constant t coq_R0 ->
      Term.t_real_const (Term.RConstDecimal ("0", "0", None))
  | Const _ when is_constant t coq_R1 ->
      Term.t_real_const (Term.RConstDecimal ("1", "0", None))
(*   | App (f, [|a;b|]) when f = Lazy.force coq_Rplus -> *)
(*       let ta = tr_arith_constant a in *)
(*       let tb = tr_arith_constant b in *)
(*       begin match ta,tb with *)
(*         | RCst na, RCst nb -> RCst (Big_int.add_big_int na nb) *)
(*         | _ -> raise NotArithConstant *)
(*       end *)
(*   | App (f, [|a;b|]) when f = Lazy.force coq_Rmult -> *)
(*       let ta = tr_arith_constant a in *)
(*       let tb = tr_arith_constant b in *)
(*       begin match ta,tb with *)
(*         | RCst na, RCst nb -> RCst (Big_int.mult_big_int na nb) *)
(*         | _ -> raise NotArithConstant *)
(*       end *)
(*   | App (f, [|a;b|]) when f = Lazy.force coq_powerRZ -> *)
(*       tr_powerRZ a b *)
  | Cast (t, _, _) ->
      tr_arith_constant t
  | _ ->
      raise NotArithConstant

let rec tr_type dep tvm env t =
  let t = Reductionops.nf_betadeltaiota env Evd.empty t in
  if is_constant t coq_Z then
    Ty.ty_int
  else if is_constant t coq_R then
    Ty.ty_real
  else match kind_of_term t with
    | Var x when Idmap.mem x tvm ->
        Ty.ty_var (Idmap.find x tvm)
    | _ ->
        let f, cl = decompose_app t in
        begin try
          let r = global_of_constr f in
          let ts = tr_task_ts dep env r in
          assert (List.length ts.Ty.ts_args = List.length cl); (* since t:Set *)
          Ty.ty_app ts (List.map (tr_type dep tvm env) cl)
        with
          | Not_found ->
              raise NotFO
          | NotFO ->
              (* TODO: we need to abstract some part of (f cl) *)
              raise NotFO
        end

(* the type symbol for r *)
and tr_task_ts dep env r =
  let ts = tr_global_ts dep env r in
  if Ident.Mid.mem ts.ts_name !global_decl then begin
    let d = Ident.Mid.find ts.ts_name !global_decl in
    add_local_decls d
  end;
  ts

(* the type declaration for r *)
and tr_global_ts dep env r =
  try
    let ts = lookup_table global_ts r in
    begin try
      let d = Ident.Mid.find ts.ts_name !global_decl in add_dep dep d
    with Not_found -> () end;
    ts
  with Not_found ->
    add_table global_ts r None;
    let dep' = empty_dep () in
    match r with
      | VarRef _id ->
          assert false (*TODO*)
      | ConstructRef _ ->
          assert false
      | ConstRef c ->
          let ty = Global.type_of_global r in
          let (_,vars), _, t = decomp_type_quantifiers env ty in
          if not (is_Set t) && not (is_Type t) then raise NotFO;
          let id = preid_of_id (Nametab.id_of_global r) in
          let ts = match (Global.lookup_constant c).const_body with
            | Some b ->
                let b = force b in
                let tvm, env, t = decomp_type_lambdas Idmap.empty env vars b in
                let def = Some (tr_type dep' tvm env t) in
                Ty.create_tysymbol id vars def
                  (* FIXME: is it correct to use None when NotFO? *)
            | None ->
                Ty.create_tysymbol id vars None
          in
          let decl = Decl.create_ty_decl [ts, Decl.Tabstract] in
          add_dep dep decl;
          add_table global_ts r (Some ts);
          global_decl := Ident.Mid.add ts.ts_name decl !global_decl;
          global_dep := Decl.Mdecl.add decl !dep' !global_dep;
          ts
      | IndRef i ->
          let all_ids = ref [] in
          let mib, _ = Global.lookup_inductive i in
          (* first, the inductive types *)
          let make_one_ts j _ = (* j-th inductive *)
            let r = IndRef (ith_mutual_inductive i j) in
            let ty = Global.type_of_global r in
            let (_,vars), _, t = decomp_type_quantifiers env ty in
            if not (is_Set t) && not (is_Type t) then raise NotFO;
            let id = preid_of_id (Nametab.id_of_global r) in
            let ts = Ty.create_tysymbol id vars None in
            all_ids := ts.ts_name :: !all_ids;
            add_table global_ts r (Some ts)
          in
          Array.iteri make_one_ts mib.mind_packets;
          (* second, the declarations with constructors *)
          let make_one j oib = (* j-th inductive *)
            let j = ith_mutual_inductive i j in
            let ts = lookup_table global_ts (IndRef j) in
            let tyj = Ty.ty_app ts (List.map Ty.ty_var ts.Ty.ts_args) in
            let mk_constructor k _tyk = (* k-th constructor *)
              let r = ConstructRef (j, k+1) in
              let ty = Global.type_of_global r in
              let (_,vars), env, t = decomp_type_quantifiers env ty in
              let tvm =
                let add v1 v2 tvm =
                  Idmap.add (id_of_string v1.tv_name.Ident.id_string) v2 tvm
                in
                List.fold_right2 add vars ts.Ty.ts_args Idmap.empty
              in
              let l, _ = decompose_arrows t in
              let l = List.map (tr_type dep' tvm env) l in
              let id = preid_of_id (Nametab.id_of_global r) in
              let ls = Term.create_lsymbol id l (Some tyj) in
              all_ids := ls.Term.ls_name :: !all_ids;
              add_table global_ls r (Some ls);
              add_poly_arith ls (List.length vars);
              ls
            in
            let ls = Array.to_list (Array.mapi mk_constructor oib.mind_nf_lc) in
            ts, Decl.Talgebraic ls
          in
          let decl = Array.mapi make_one mib.mind_packets in
          let decl = Array.to_list decl in
          let decl = Decl.create_ty_decl decl in
          (* Format.printf "decl = %a@." Pretty.print_decl decl; *)
          add_dep dep decl;
          List.iter
            (fun id ->
               global_decl := Ident.Mid.add id decl !global_decl)
            !all_ids;
          global_dep := Decl.Mdecl.add decl !dep' !global_dep;
          lookup_table global_ts r

(* the function/predicate symbol for r *)
and tr_task_ls dep env r =
  let ls = tr_global_ls dep env r in
  if Ident.Mid.mem ls.ls_name !global_decl then begin
    let d = Ident.Mid.find ls.ls_name !global_decl in
    add_local_decls d
  end;
  ls

(* the function/predicate symbol declaration for r *)
and tr_global_ls dep env r =
  try
    let ls = lookup_table global_ls r in
    begin try
      let d = Ident.Mid.find ls.ls_name !global_decl in add_dep dep d
    with Not_found -> () end;
    ls
  with Not_found ->
    add_table global_ls r None;
    let dep' = empty_dep () in
    let ty = Global.type_of_global r in
    let (tvm, _), env, t = decomp_type_quantifiers env ty in
    if is_Set t || is_Type t then raise NotFO;
    let _, t = decompose_arrows t in
    match r with
      | ConstructRef _ ->
          if is_Prop t then raise NotFO; (*TODO? *)
          let s = type_of env Evd.empty t in
          if not (is_Set s || is_Type s) then raise NotFO;
          ignore (tr_type dep' tvm env t);
          lookup_table global_ls r
      | ConstRef c ->
          let ld = decompose_definition dep' env c in
(*           let ld = match defl with *)
(*             | [] -> *)
(*                 [make_def_decl dep env r None] *)
(*             | _ -> *)
(*                 List.map (fun (r, t) -> make_def_decl dep env r (Some t)) defl *)
(*           in *)
          let decl = Decl.create_logic_decl ld in
          add_dep dep decl;
          List.iter
            (fun (ls, _) ->
               global_decl := Ident.Mid.add ls.ls_name decl !global_decl)
            ld;
          global_dep := Decl.Mdecl.add decl !dep' !global_dep;
          lookup_table global_ls r
      | VarRef _ | IndRef _ ->
          raise NotFO

and decompose_definition dep env c =
  let dl = match (Global.lookup_constant c).const_body with
    | None ->
        [ConstRef c, None]
    | Some b ->
        let b = force b in
        let rec decomp vars t = match kind_of_term t with
          | Lambda (n, a, t) ->
              decomp ((n, a) :: vars) t
          | Fix (_, (names, _, bodies)) ->
              let lc = rec_names_for c names in
              let l = List.rev_map mkConst lc in
              let n = List.length vars in
              let db_vars = Array.init n (fun i -> mkRel (n - i)) in
              let l = List.map (fun t -> appvect (t, db_vars)) l in
              let bodies = Array.to_list bodies in
              let bodies = List.map (substl l) bodies in
              let add_lambdas b =
                List.fold_left (fun t (n,a) -> mkLambda (n,a,t)) b vars
              in
              let bodies = List.map add_lambdas bodies in
              List.fold_right2
                (fun c b acc -> (ConstRef c, Some b) :: acc) lc bodies []
          | _ ->
              [ConstRef c, Some b]
        in
        decomp [] b
  in
  let make_one_ls r =
    let ty = Global.type_of_global r in
    let (tvm, vars), env, t = decomp_type_quantifiers env ty in
    if is_Set t || is_Type t then raise NotFO;
    let l, t = decompose_arrows t in
    let args = List.map (tr_type dep tvm env) l in
    let ls =
      let id = preid_of_id (Nametab.id_of_global r) in
      if is_Prop t then
        (* predicate definition *)
        create_lsymbol id args None
      else
        let s = type_of env Evd.empty t in
        if is_Set s || is_Type s then
          (* function definition *)
          let ty = tr_type dep tvm env t in
          create_lsymbol id args (Some ty)
        else
          raise NotFO
    in
    add_table global_ls r (Some ls);
    add_poly_arith ls (List.length vars)
  in
  List.iter (fun (r, _) -> make_one_ls r) dl;
  let make_one_decl (r, b) =
    let ls = lookup_table global_ls r in
    match b with
      | None ->
          ls, None
      | Some b ->
          let ty = Global.type_of_global r in
          let (tvm, vars), env, ty = decomp_type_quantifiers env ty in
          let tyl, _ = decompose_arrows ty in
          let tyl = List.map (tr_type dep tvm env) tyl in
          let tvm, env, b = decomp_type_lambdas Idmap.empty env vars b in
          let (bv, vsl), env, b =
            decomp_lambdas dep tvm Idmap.empty env tyl b
          in
          begin match ls.ls_value with
            | None ->
                let b = tr_formula dep tvm bv env b in
                Decl.make_ps_defn ls vsl b
            | Some _ ->
                let b = tr_term dep tvm bv env b in
                Decl.make_fs_defn ls vsl b
          end
  in
  List.map make_one_decl dl

(***
          (* is it defined? *)
          let ld = match (Global.lookup_constant c).const_body with
            | Some b ->
                let b = force b in
                let b = match kind_of_term b with
                  (* a single recursive function *)
                  | Fix (_, (_,_,[|b|])) ->
                      subst1 (mkConst c) b
                  | Fix ((_,_i), (_names,_,_bodies)) ->
                      assert false (*TODO*)
                  | _ ->
                      b
                in
***)

(* translation of a Coq term
   assumption: t:T:Set *)
and tr_term dep tvm bv env t =
  try
    tr_arith_constant t
  with NotArithConstant -> match kind_of_term t with
    (* binary operations on integers *)
    | App (c, [|a;b|]) when is_constant c coq_Zplus ->
        let ls = why_constant ["int"] "Int" ["infix +"] in
        Term.t_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
          Ty.ty_int
    | App (c, [|a;b|]) when is_constant c coq_Zminus ->
        let ls = why_constant ["int"] "Int" ["infix -"] in
        Term.t_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
          Ty.ty_int
    | App (c, [|a;b|]) when is_constant c coq_Zmult ->
        let ls = why_constant ["int"] "Int" ["infix *"] in
        Term.t_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
          Ty.ty_int
    | App (c, [|a;b|]) when is_constant c coq_Zdiv ->
        let ls = why_constant ["int"] "EuclideanDivision" ["div"] in
        Term.t_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
          Ty.ty_int
    | App (c, [|a|]) when is_constant c coq_Zopp ->
        let ls = why_constant ["int"] "Int" ["prefix -"] in
        Term.t_app ls [tr_term dep tvm bv env a] Ty.ty_int
    (* binary operations on reals *)
    | App (c, [|a;b|]) when is_constant c coq_Rplus ->
        let ls = why_constant ["real"] "Real" ["infix +"] in
        Term.t_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
          Ty.ty_real
    | App (c, [|a;b|]) when is_constant c coq_Rminus ->
        let ls = why_constant ["real"] "Real" ["infix -"] in
        Term.t_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
          Ty.ty_real
    | App (c, [|a;b|]) when is_constant c coq_Rmult ->
        let ls = why_constant ["real"] "Real" ["infix *"] in
        Term.t_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
          Ty.ty_real
    | App (c, [|a;b|]) when is_constant c coq_Rdiv ->
        let ls = why_constant ["real"] "Real" ["infix /"] in
        Term.t_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
          Ty.ty_real
    | App (c, [|a|]) when is_constant c coq_Ropp ->
        let ls = why_constant ["real"] "Real" ["prefix -"] in
        Term.t_app ls [tr_term dep tvm bv env a] Ty.ty_real
    | App (c, [|a|]) when is_constant c coq_Rinv ->
        let ls = why_constant ["real"] "Real" ["inv"] in
        Term.t_app ls [tr_term dep tvm bv env a] Ty.ty_real
          (* first-order terms *)
    | Var id when Idmap.mem id bv ->
        Term.t_var (Idmap.find id bv)
    | Var id ->
        Format.eprintf "tr_term: unbound variable %s@." (string_of_id id);
        exit 1
    | Case (ci, _, e, br) ->
        let ty = type_of env Evd.empty e in
        let ty = tr_type dep tvm env ty in
        let e = tr_term dep tvm bv env e in
        let branch j bj =
          let tj = type_of env Evd.empty bj in
          let (_,tvars), _, tj = decomp_type_quantifiers env tj in
          let tyl, _ = decompose_arrows tj in
          let tyl = List.map (tr_type dep tvm env) tyl in
          let tvm, env, bj = decomp_type_lambdas tvm env tvars bj in
          let (bv, vars), env, bj = decomp_lambdas dep tvm bv env tyl bj in
          let cj = ith_constructor_of_inductive ci.ci_ind (j+1) in
          let ls = tr_global_ls dep env (ConstructRef cj) in
          if List.length vars <> List.length ls.ls_args then raise NotFO;
          let pat = pat_app ls (List.map pat_var vars) ty in
          t_close_branch pat (tr_term dep tvm bv env bj)
        in
        let ty = type_of env Evd.empty t in
        let _ty = tr_type dep tvm env ty in
        t_case e (Array.to_list (Array.mapi branch br))
    | _ ->
        let f, cl = decompose_app t in
        let r = global_of_constr f in
        let ls = tr_task_ls dep env r in
        begin match ls.Term.ls_value with
          | Some _ ->
              let k = get_poly_arity ls in
              let cl = skip_k_args k cl in
              let ty = type_of env Evd.empty t in
              let ty = tr_type dep tvm env ty in
              Term.t_app ls (List.map (tr_term dep tvm bv env) cl) ty
          | None  ->
              raise NotFO
        end
        (* TODO: we could abstract some part of (f cl) when not FO *)
(*               let rec abstract app = function *)
(*                   | [] -> *)
(*                       Fol.App (make_term_abstraction tv env app, []) *)
(*                   | x :: l as args -> *)
(*                       begin try *)
(*                         let s = make_term_abstraction tv env app in *)
(*                         Fol.App (s, List.map (tr_term dep tvm bv env) args) *)
(*                       with NotFO -> *)
(*                         abstract (applist (app, [x])) l *)
(*                       end *)
(*               in *)
(*               let app,l = match cl with *)
(*                   | x :: l -> applist (f, [x]), l | [] -> raise NotFO *)
(*               in *)
(*               abstract app l *)

and quantifiers n a b dep tvm bv env =
  let vars, env = coq_rename_vars env [n,a] in
  let id = match vars with [x] -> x | _ -> assert false in
  let b = subst1 (mkVar id) b in
  let t = tr_type dep tvm env a in
  let vs = Term.create_vsymbol (preid_of_id id) t in
  let bv = Idmap.add id vs bv in
  vs, t, bv, env, b

(* translation of a Coq formula
   assumption f:Prop *)
and tr_formula dep tvm bv env f =
  let c, args = decompose_app f in
  match kind_of_term c, args with
      (*
        | Var id, [] ->
        Fatom (Pred (rename_global (VarRef id), []))
      *)
    | _, [t;a;b] when c = build_coq_eq () ->
        let ty = type_of env Evd.empty t in
        if is_Set ty || is_Type ty then
          let _ = tr_type dep tvm env t in
          Term.t_equ (tr_term dep tvm bv env a) (tr_term dep tvm bv env b)
        else
          raise NotFO
    (* comparisons on integers *)
    | _, [a;b] when is_constant c coq_Zle ->
        let ls = why_constant ["int"] "Int" ["infix <="] in
        Term.f_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
    | _, [a;b] when is_constant c coq_Zlt ->
        let ls = why_constant ["int"] "Int" ["infix <"] in
        Term.f_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
    | _, [a;b] when is_constant c coq_Zge ->
        let ls = why_constant ["int"] "Int" ["infix >="] in
        Term.f_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
    | _, [a;b] when is_constant c coq_Zgt ->
        let ls = why_constant ["int"] "Int" ["infix >"] in
        Term.f_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
    (* comparisons on reals *)
    | _, [a;b] when is_constant c coq_Rle ->
        let ls = why_constant ["real"] "Real" ["infix <="] in
        Term.f_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
    | _, [a;b] when is_constant c coq_Rlt ->
        let ls = why_constant ["real"] "Real" ["infix <"] in
        Term.f_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
    | _, [a;b] when is_constant c coq_Rge ->
        let ls = why_constant ["real"] "Real" ["infix >="] in
        Term.f_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
    | _, [a;b] when is_constant c coq_Rgt ->
        let ls = why_constant ["real"] "Real" ["infix >"] in
        Term.f_app ls [tr_term dep tvm bv env a; tr_term dep tvm bv env b]
    (* propositional logic *)
    | _, [] when c = build_coq_False () ->
        Term.t_false
    | _, [] when c = build_coq_True () ->
        Term.t_true
    | _, [a] when c = build_coq_not () ->
        Term.t_not (tr_formula dep tvm bv env a)
    | _, [a;b] when c = build_coq_and () ->
        Term.t_and (tr_formula dep tvm bv env a) (tr_formula dep tvm bv env b)
    | _, [a;b] when c = build_coq_or () ->
        Term.t_or (tr_formula dep tvm bv env a) (tr_formula dep tvm bv env b)
    | _, [a;b] when c = Lazy.force coq_iff ->
        Term.t_iff (tr_formula dep tvm bv env a) (tr_formula dep tvm bv env b)
    | Prod (n, a, b), _ ->
        if is_imp_term f && is_Prop (type_of env Evd.empty a) then
          Term.t_implies
            (tr_formula dep tvm bv env a) (tr_formula dep tvm bv env b)
        else
          let vs, _t, bv, env, b = quantifiers n a b dep tvm bv env in
          Term.t_forall_close [vs] [] (tr_formula dep tvm bv env b)
    | _, [_; a] when c = build_coq_ex () ->
        begin match kind_of_term a with
          | Lambda(n, a, b) ->
              let vs, _t, bv, env, b = quantifiers n a b dep tvm bv env in
              Term.t_exists_close [vs] [] (tr_formula dep tvm bv env b)
          | _ ->
              (* unusual case of the shape (ex p) *)
              (* TODO: we could eta-expanse *)
              raise NotFO
        end
    | Case (ci, _, e, br), [] ->
        let ty = type_of env Evd.empty e in
        let ty = tr_type dep tvm env ty in
        let t = tr_term dep tvm bv env e in
        let branch j bj =
          let tj = type_of env Evd.empty bj in
          let (_,tvars), _, tj = decomp_type_quantifiers env tj in
          let tyl, _ = decompose_arrows tj in
          let tyl = List.map (tr_type dep tvm env) tyl in
          let tvm, env, bj = decomp_type_lambdas tvm env tvars bj in
          let (bv, vars), env, bj = decomp_lambdas dep tvm bv env tyl bj in
          let cj = ith_constructor_of_inductive ci.ci_ind (j+1) in
          let ls = tr_global_ls dep env (ConstructRef cj) in
          if List.length vars <> List.length ls.ls_args then raise NotFO;
          let pat = pat_app ls (List.map pat_var vars) ty in
          t_close_branch pat (tr_formula dep tvm bv env bj)
        in
        t_case t (Array.to_list (Array.mapi branch br))
    | Case _, _ :: _ ->
        raise NotFO (* TODO: we could possibly swap case and application *)
    | _ ->
        let r = global_of_constr c in (*TODO: may fail *)
        let ls = tr_task_ls dep env r in
        begin match ls.Term.ls_value with
          | None ->
              let k = get_poly_arity ls in
              let args = skip_k_args k args in
              Term.f_app ls (List.map (tr_term dep tvm bv env) args)
          | Some _ ->
              raise NotFO
        end

let tr_goal gl =
  local_decl := Decl.Sdecl.empty;
  let env = pf_env gl in
  let dep = empty_dep () in
  let rec tr_ctxt tvm bv = function
    | [] ->
        tr_formula dep tvm bv env (pf_concl gl)
    | (id, None, ty) :: ctxt when is_Set ty || is_Type ty ->
        let v = Ty.create_tvsymbol (preid_of_id id) in
        let tvm = Idmap.add id v tvm in
        tr_ctxt tvm bv ctxt
    | (id, None, ty) :: ctxt ->
        let t = type_of env Evd.empty ty in
        begin try
          if is_Set t || is_Type t then
            let ty = tr_type dep tvm env ty in (* DO NOT INLINE! *)
            let vs = Term.create_vsymbol (preid_of_id id) ty in
            let bv = Idmap.add id vs bv in
            Term.t_forall_close [vs] [] (tr_ctxt tvm bv ctxt)
          else if is_Prop t then
            let h = tr_formula dep tvm bv env ty in (* DO NOT INLINE! *)
            Term.t_implies h (tr_ctxt tvm bv ctxt)
          else
            raise NotFO
        with NotFO ->
          tr_ctxt tvm bv ctxt
        end
    | (id, Some d, ty) :: ctxt ->
        (* local definition -> let or skip *)
        let t = type_of env Evd.empty ty in
        begin try
          if not (is_Set t || is_Type t) then raise NotFO;
          let d = tr_term dep tvm bv env d in
          let ty = tr_type dep tvm env ty in
          let vs = Term.create_vsymbol (preid_of_id id) ty in
          let bv = Idmap.add id vs bv in
          Term.t_let_close vs d (tr_ctxt tvm bv ctxt)
        with NotFO ->
          tr_ctxt tvm bv ctxt
        end
  in
  let f = tr_ctxt Idmap.empty Idmap.empty (List.rev (pf_hyps gl)) in
  let pr = Decl.create_prsymbol (Ident.id_fresh "goal") in
  if debug then Format.printf "---@\n%a@\n---@." Pretty.print_fmla f;
  task := Task.add_prop_decl !task Decl.Pgoal pr f

let () = Printexc.record_backtrace true

let whytac s gl =
  (* print_dep Format.err_formatter; *)
  let concl_type = pf_type_of gl (pf_concl gl) in
  if not (is_Prop concl_type) then error "Conclusion is not a Prop";
  task := Task.use_export None Theory.builtin_theory;
  try
    tr_goal gl;
    let cp, drv = get_prover s in
    let command = cp.command in
    if debug then Format.printf "@[%a@]@\n---@." Pretty.print_task !task;
    if debug then Format.printf "@[%a@]@\n---@." (Driver.print_task drv) !task;
    let res = Driver.prove_task ~command ~timelimit drv !task () () in
    match res.pr_answer with
      | Valid -> Tactics.admit_as_an_axiom gl
      | Invalid -> error "Invalid"
      | Unknown s -> error ("Don't know: " ^ s)
      | Failure s -> error ("Failure: " ^ s)
      | Timeout -> error "Timeout"
      | HighFailure ->
          error ("Prover failure\n" ^ res.pr_output ^ "\n")
  with
    | NotFO ->
        error "Not a first order goal"
    | e ->
        Printexc.print_backtrace stderr;
        raise e



(*
Local Variables:
compile-command: "unset LANG; make -C ../.. src/coq-plugin/whytac.cmxs"
End:
*)
