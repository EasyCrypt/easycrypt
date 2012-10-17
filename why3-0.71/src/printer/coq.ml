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

(** Coq printer *)

open Format
open Pp
open Util
open Ident
open Ty
open Term
open Decl
open Printer

let black_list =
  [ "at"; "cofix"; "exists2"; "fix"; "IF"; "left"; "mod"; "Prop";
    "return"; "right"; "Set"; "Type"; "using"; "where"; ]

let iprinter =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer black_list ~sanitizer:isanitize

let forget_all () = forget_all iprinter

let tv_set = ref Sid.empty

(* type variables *)

let print_tv fmt tv =
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "%s" n

let print_tv_binder fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "(%s:Type)" n

let print_implicit_tv_binder fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "{%s:Type}" n

let print_ne_params fmt stv =
  Stv.iter
    (fun tv -> fprintf fmt "@ %a" print_tv_binder tv)
    stv

let print_ne_params_list fmt ltv =
  List.iter
    (fun tv -> fprintf fmt "@ %a" print_tv_binder tv)
    ltv

let print_params fmt stv =
  if Stv.is_empty stv then () else
    fprintf fmt "forall%a,@ " print_ne_params stv

let print_implicit_params fmt stv =
  Stv.iter (fun tv -> fprintf fmt "%a@ " print_implicit_tv_binder tv) stv

let print_params_list fmt ltv =
  match ltv with
    | [] -> ()
    | _ -> fprintf fmt "forall%a,@ " print_ne_params_list ltv

let forget_tvs () =
  Sid.iter (forget_id iprinter) !tv_set;
  tv_set := Sid.empty

(* logic variables *)
let print_vs fmt vs =
  let n = id_unique iprinter vs.vs_name in
  fprintf fmt "%s" n

let forget_var vs = forget_id iprinter vs.vs_name

let print_ts fmt ts =
  fprintf fmt "%s" (id_unique iprinter ts.ts_name)

let print_ls fmt ls =
  fprintf fmt "%s" (id_unique iprinter ls.ls_name)

let print_pr fmt pr =
  fprintf fmt "%s" (id_unique iprinter pr.pr_name)

(* info *)

type info = {
  info_syn : syntax_map;
  realization : (Theory.theory * ident_printer) Mid.t option;
}

let print_path = print_list (constant_string ".") string

let print_id fmt id = string fmt (id_unique iprinter id)

let print_id_real info fmt id = match info.realization with
  | Some m ->
      begin
        try let th,ipr = Mid.find id m in
        fprintf fmt "%a.%s.%s"
          print_path th.Theory.th_path
          th.Theory.th_name.id_string
          (id_unique ipr id)
        with Not_found -> print_id fmt id
      end
  | None -> print_id fmt id

let print_ls_real info fmt ls = print_id_real info fmt ls.ls_name
let print_ts_real info fmt ts = print_id_real info fmt ts.ts_name
let print_pr_real info fmt pr = print_id_real info fmt pr.pr_name

(** Types *)

let rec print_ty info fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      begin
        match tl with
          | []  -> fprintf fmt "unit"
          | [ty] -> print_ty info fmt ty
          | _   -> fprintf fmt "(%a)%%type" (print_list star (print_ty info)) tl
      end
  | Tyapp (ts, tl) ->
      begin match query_syntax info.info_syn ts.ts_name with
        | Some s -> syntax_arguments s (print_ty info) fmt tl
        | None ->
            begin
              match tl with
                | []  -> (print_ts_real info) fmt ts
                | l   -> fprintf fmt "(%a@ %a)" (print_ts_real info) ts
                    (print_list space (print_ty info)) l
            end
      end

(* can the type of a value be derived from the type of the arguments? *)
let unambig_fs fs =
  let rec lookup v ty = match ty.ty_node with
    | Tyvar u when tv_equal u v -> true
    | _ -> ty_any (lookup v) ty
  in
  let lookup v = List.exists (lookup v) fs.ls_args in
  let rec inspect ty = match ty.ty_node with
    | Tyvar u when not (lookup u) -> false
    | _ -> ty_all inspect ty
  in
  inspect (of_option fs.ls_value)

(** Patterns, terms, and formulas *)

let lparen_l fmt () = fprintf fmt "@ ("
let lparen_r fmt () = fprintf fmt "(@,"
let print_paren_l fmt x = print_list_delim lparen_l rparen comma fmt x
let print_paren_r fmt x = print_list_delim lparen_r rparen comma fmt x

let arrow fmt () = fprintf fmt "@ -> "
let print_arrow_list fmt x = print_list arrow fmt x
let print_space_list fmt x = print_list space fmt x

let rec print_pat info fmt p = match p.pat_node with
  | Pwild -> fprintf fmt "_"
  | Pvar v -> print_vs fmt v
  | Pas (p,v) ->
      fprintf fmt "(%a as %a)" (print_pat info) p print_vs v
  | Por (p,q) ->
      fprintf fmt "(%a|%a)" (print_pat info) p (print_pat info) q
  | Papp (cs,pl) when is_fs_tuple cs ->
      fprintf fmt "%a" (print_paren_r (print_pat info)) pl
  | Papp (cs,pl) ->
      begin match query_syntax info.info_syn cs.ls_name with
        | Some s -> syntax_arguments s (print_pat info) fmt pl
        | _ when pl = [] -> (print_ls_real info) fmt cs
        | _ -> fprintf fmt "(%a %a)"
          (print_ls_real info) cs (print_list space (print_pat info)) pl
      end

let print_vsty_nopar info fmt v =
  fprintf fmt "%a:%a" print_vs v (print_ty info) v.vs_ty

let print_vsty info fmt v =
  fprintf fmt "(%a)" (print_vsty_nopar info) v

let print_binop fmt = function
  | Tand -> fprintf fmt "/\\"
  | Tor -> fprintf fmt "\\/"
  | Timplies -> fprintf fmt "->"
  | Tiff -> fprintf fmt "<->"

let print_label fmt (l,_) = fprintf fmt "(*%s*)" l

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_term info fmt t = print_lrterm false false info fmt t
and     print_fmla info fmt f = print_lrfmla false false info fmt f
and print_opl_term info fmt t = print_lrterm true  false info fmt t
and print_opl_fmla info fmt f = print_lrfmla true  false info fmt f
and print_opr_term info fmt t = print_lrterm false true  info fmt t
and print_opr_fmla info fmt f = print_lrfmla false true  info fmt f

and print_lrterm opl opr info fmt t = match t.t_label with
  | _ -> print_tnode opl opr info fmt t
(*
  | [] -> print_tnode opl opr info fmt t
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_tnode false false info) t
*)

and print_lrfmla opl opr info fmt f = match f.t_label with
  | _ -> print_fnode opl opr info fmt f
(*
  | [] -> print_fnode opl opr info fmt f
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_fnode false false info) f
*)

and print_tnode opl opr info fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      let number_format = {
          Print_number.long_int_support = true;
          Print_number.dec_int_support = Print_number.Number_custom "%s%%Z";
          Print_number.hex_int_support = Print_number.Number_unsupported;
          Print_number.oct_int_support = Print_number.Number_unsupported;
          Print_number.bin_int_support = Print_number.Number_unsupported;
          Print_number.def_int_support = Print_number.Number_unsupported;
          Print_number.dec_real_support = Print_number.Number_unsupported;
          Print_number.hex_real_support = Print_number.Number_unsupported;
          Print_number.frac_real_support = Print_number.Number_custom
            (Print_number.PrintFracReal ("%s%%R", "(%s * %s)%%R", "(%s / %s)%%R"));
          Print_number.def_real_support = Print_number.Number_unsupported;
        } in
      Print_number.print number_format fmt c
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        (print_fmla info) f (print_term info) t1 (print_opl_term info) t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on opr "let %a :=@ %a in@ %a")
        print_vs v (print_opl_term info) t1 (print_opl_term info) t2;
      forget_var v
  | Tcase (t,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_term info) t
        (print_list newline (print_tbranch info)) bl
  | Teps fb ->
      let v,f = t_open_bound fb in
      fprintf fmt (protect_on opr "epsilon %a.@ %a")
        (print_vsty info) v (print_opl_fmla info) f;
      forget_var v
  | Tapp (fs,pl) when is_fs_tuple fs ->
      fprintf fmt "%a" (print_paren_r (print_term info)) pl
  | Tapp (fs, tl) ->
    begin match query_syntax info.info_syn fs.ls_name with
      | Some s ->
          syntax_arguments s (print_term info) fmt tl
      | _ -> if unambig_fs fs
          then
            if tl = [] then fprintf fmt "%a" (print_ls_real info) fs
            else fprintf fmt "(%a %a)" (print_ls_real info) fs
              (print_space_list (print_term info)) tl
          else fprintf fmt (protect_on opl "(%a%a:%a)") (print_ls_real info) fs
            (print_paren_r (print_term info)) tl (print_ty info) (t_type t)
    end
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fnode opl opr info fmt f = match f.t_node with
  | Tquant (Tforall,fq) ->
      let vl,_tl,f = t_open_quant fq in
      fprintf fmt (protect_on opr "forall %a,@ %a")
        (print_space_list (print_vsty info)) vl
        (* (print_tl info) tl *) (print_fmla info) f;
      List.iter forget_var vl
  | Tquant (Texists,fq) ->
      let vl,_tl,f = t_open_quant fq in
      let rec aux fmt vl =
        match vl with
          | [] -> print_fmla info fmt f
          | v::vr ->
              fprintf fmt (protect_on opr "exists %a,@ %a")
                (print_vsty_nopar info) v
                aux vr
      in
      aux fmt vl;
      List.iter forget_var vl
  | Ttrue ->
      fprintf fmt "True"
  | Tfalse ->
      fprintf fmt "False"
  | Tbinop (b,f1,f2) ->
      fprintf fmt (protect_on (opl || opr) "%a %a@ %a")
        (print_opr_fmla info) f1 print_binop b (print_opl_fmla info) f2
  | Tnot f ->
      fprintf fmt (protect_on opr "~ %a") (print_opl_fmla info) f
  | Tlet (t,f) ->
      let v,f = t_open_bound f in
      fprintf fmt (protect_on opr "let %a :=@ %a in@ %a")
        print_vs v (print_opl_term info) t (print_opl_fmla info) f;
      forget_var v
  | Tcase (t,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_term info) t
        (print_list newline (print_fbranch info)) bl
  | Tif (f1,f2,f3) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        (print_fmla info) f1 (print_fmla info) f2 (print_opl_fmla info) f3
  | Tapp (ps, tl) ->
    begin match query_syntax info.info_syn ps.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | _ -> fprintf fmt "(%a %a)" (print_ls_real info) ps
          (print_space_list (print_term info)) tl
    end
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and print_tbranch info fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a =>@ %a@]"
    (print_pat info) p (print_term info) t;
  Svs.iter forget_var p.pat_vars

and print_fbranch info fmt br =
  let p,f = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a =>@ %a@]"
    (print_pat info) p (print_fmla info) f;
  Svs.iter forget_var p.pat_vars

let print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

(** Declarations *)

let print_constr info ts fmt cs =
  match cs.ls_args with
    | [] ->
        fprintf fmt "@[<hov 4>| %a : %a %a@]" print_ls cs
          print_ts ts (print_list space print_tv) ts.ts_args
    | l ->
        fprintf fmt "@[<hov 4>| %a : %a -> %a %a@]" print_ls cs
          (print_arrow_list (print_ty info)) l
          print_ts ts (print_list space print_tv) ts.ts_args

let ls_ty_vars ls =
  let ty_vars_args = List.fold_left Ty.ty_freevars Stv.empty ls.ls_args in
  let ty_vars_value = option_fold Ty.ty_freevars Stv.empty ls.ls_value in
  (ty_vars_args, ty_vars_value, Stv.union ty_vars_args ty_vars_value)

let print_implicits fmt ls ty_vars_args ty_vars_value all_ty_params =
  if not (Stv.is_empty all_ty_params) then
    begin
      let need_context = not (Stv.subset ty_vars_value ty_vars_args) in
      if need_context then fprintf fmt "Set Contextual Implicit.@\n";
      fprintf fmt "Implicit Arguments %a.@\n" print_ls ls;
      if need_context then fprintf fmt "Unset Contextual Implicit.@\n"
    end

let definition fmt info =
  fprintf fmt "%s" (if info.realization <> None then "Definition" else "Parameter")

(*

  copy of old user scripts

*)

let copy_user_script begin_string end_string ch fmt =
  fprintf fmt "%s@\n" begin_string;
  try
    while true do
      let s = input_line ch in
      fprintf fmt "%s@\n" s;
      if s = end_string then raise Exit
    done
  with
    | Exit -> fprintf fmt "@\n"
    | End_of_file -> fprintf fmt "%s@\n@\n" end_string

let proof_begin = "(* YOU MAY EDIT THE PROOF BELOW *)"
let proof_end = "(* DO NOT EDIT BELOW *)"
let context_begin = "(* YOU MAY EDIT THE CONTEXT BELOW *)"
let context_end = "(* DO NOT EDIT BELOW *)"

(* current kind of script in an old file *)
type old_file_state = InContext | InProof | NoWhere

let copy_proof s ch fmt =
  copy_user_script proof_begin proof_end ch fmt;
  s := NoWhere

let copy_context s ch fmt =
  copy_user_script context_begin context_end ch fmt;
  s := NoWhere

let lookup_context_or_proof old_state old_channel =
  match !old_state with
    | InProof | InContext -> ()
    | NoWhere ->
        let rec loop () =
          let s = input_line old_channel in
          if s = proof_begin then old_state := InProof else
            if s = context_begin then old_state := InContext else
              loop ()
        in
        try loop ()
        with End_of_file -> ()

let print_empty_context fmt =
  fprintf fmt "%s@\n" context_begin;
  fprintf fmt "@\n";
  fprintf fmt "%s@\n@\n" context_end

let print_empty_proof ?(def=false) fmt =
  fprintf fmt "%s@\n" proof_begin;
  if not def then fprintf fmt "intuition.@\n";
  fprintf fmt "@\n";
  fprintf fmt "%s.@\n" (if def then "Defined" else "Qed");
  fprintf fmt "%s@\n@\n" proof_end

(*
let print_next_proof ?def ch fmt =
  try
    while true do
      let s = input_line ch in
      if s = proof_begin then
        begin
          fprintf fmt "%s@\n" proof_begin;
          while true do
            let s = input_line ch in
            fprintf fmt "%s@\n" s;
            if s = proof_end then raise Exit
          done
        end
    done
  with
    | End_of_file -> print_empty_proof ?def fmt
    | Exit -> fprintf fmt "@\n"
*)

let print_context ~old fmt =
  match old with
    | None -> print_empty_context fmt
    | Some(s,ch) ->
        lookup_context_or_proof s ch;
        match !s with
          | InProof | NoWhere -> print_empty_context fmt
          | InContext -> copy_context s ch fmt

let print_proof ~old ?def fmt =
  match old with
    | None -> print_empty_proof ?def fmt
    | Some(s,ch) ->
        lookup_context_or_proof s ch;
        match !s with
          | InContext | NoWhere -> print_empty_proof ?def fmt
          | InProof -> copy_proof s ch fmt

let produce_remaining_contexts_and_proofs ~old fmt =
  match old with
    | None -> ()
    | Some(s,ch) ->
        let rec loop () =
          lookup_context_or_proof s ch;
          match !s with
            | NoWhere -> ()
            | InContext -> copy_context s ch fmt; loop ()
            | InProof -> copy_proof s ch fmt; loop ()
        in
        loop ()

(*
let produce_remaining_proofs ~old fmt =
  match old with
    | None -> ()
    | Some ch ->
  try
    while true do
      let s = input_line ch in
      if s = proof_begin then
        begin
          fprintf fmt "(* OBSOLETE PROOF *)@\n";
          try while true do
            let s = input_line ch in
            if s = proof_end then
              begin
                fprintf fmt "(* END OF OBSOLETE PROOF *)@\n@\n";
                raise Exit
              end;
            fprintf fmt "%s@\n" s;
          done
          with Exit -> ()
        end
    done
  with
    | End_of_file -> fprintf fmt "@\n"
*)

let realization ~old ?def fmt produce_realization =
  if produce_realization then
    print_proof ~old ?def fmt
(*
    begin match old with
      | None -> print_empty_proof ?def fmt
      | Some ch -> print_next_proof ?def ch fmt
    end
*)
  else
    fprintf fmt "@\n"

let print_type_decl ~old info fmt (ts,def) =
  if is_ts_tuple ts then () else
  match def with
    | Tabstract -> begin match ts.ts_def with
        | None ->
            fprintf fmt "@[<hov 2>%a %a : %aType.@]@\n%a"
              definition info
              print_ts ts print_params_list ts.ts_args
              (realization ~old ~def:true) (info.realization <> None)
        | Some ty ->
            fprintf fmt "@[<hov 2>Definition %a %a :=@ %a.@]@\n@\n"
              print_ts ts (print_list space print_tv_binder) ts.ts_args
              (print_ty info) ty
      end
    | Talgebraic csl ->
        fprintf fmt "@[<hov 2>Inductive %a %a :=@\n@[<hov>%a@].@]@\n"
          print_ts ts (print_list space print_tv_binder) ts.ts_args
          (print_list newline (print_constr info ts)) csl;
        List.iter
          (fun cs ->
             let ty_vars_args, ty_vars_value, all_ty_params = ls_ty_vars cs in
             print_implicits fmt cs ty_vars_args ty_vars_value all_ty_params)
          csl;
        fprintf fmt "@\n"

let print_type_decl ~old info fmt d =
  if not (Mid.mem (fst d).ts_name info.info_syn) then
    (print_type_decl ~old info fmt d; forget_tvs ())

let print_ls_type ?(arrow=false) info fmt ls =
  if arrow then fprintf fmt " ->@ ";
  match ls with
  | None -> fprintf fmt "Prop"
  | Some ty -> print_ty info fmt ty

let print_logic_decl ~old info fmt (ls,ld) =
  let ty_vars_args, ty_vars_value, all_ty_params = ls_ty_vars ls in
  begin
    match ld with
      | Some ld ->
          let vl,e = open_ls_defn ld in
          fprintf fmt "@[<hov 2>Definition %a%a%a: %a :=@ %a.@]@\n"
            print_ls ls
            print_ne_params all_ty_params
            (print_space_list (print_vsty info)) vl
            (print_ls_type info) ls.ls_value
            (print_expr info) e;
          List.iter forget_var vl
      | None ->
          fprintf fmt "@[<hov 2>%a %a: %a%a%a.@]@\n%a"
            definition info
            print_ls ls
            print_params all_ty_params
            (print_arrow_list (print_ty info)) ls.ls_args
            (print_ls_type ~arrow:(ls.ls_args <> []) info) ls.ls_value
            (realization ~old ~def:true) (info.realization <> None)
  end;
  print_implicits fmt ls ty_vars_args ty_vars_value all_ty_params;
  fprintf fmt "@\n"

let print_logic_decl ~old info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn) then
    (print_logic_decl ~old info fmt d; forget_tvs ())

let print_recursive_decl info tm fmt (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let il = try Mls.find ls tm with Not_found -> assert false in
  let i = match il with [i] -> i | _ -> assert false in
  begin match ld with
    | Some ld ->
        let vl,e = open_ls_defn ld in
        fprintf fmt "%a%a%a {struct %a}: %a :=@ %a.@]@\n"
          print_ls ls
          print_ne_params all_ty_params
          (print_space_list (print_vsty info)) vl
          print_vs (List.nth vl i)
          (print_ls_type info) ls.ls_value
          (print_expr info) e;
        List.iter forget_var vl
    | None ->
        assert false
  end

let print_recursive_decl info fmt dl =
  let tm = check_termination dl in
  let d, dl = match dl with d :: dl -> d, dl | [] -> assert false in
  fprintf fmt "Set Implicit Arguments.@\n";
  fprintf fmt "@[<hov 2>Fixpoint ";
  print_recursive_decl info tm fmt d; forget_tvs ();
  List.iter
    (fun d ->
       fprintf fmt "@[<hov 2>with ";
       print_recursive_decl info tm fmt d; forget_tvs ())
    dl;
  fprintf fmt "Unset Implicit Arguments.@\n@\n"

let print_ind info fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a : %a@]" print_pr pr (print_fmla info) f

let print_ind_decl info fmt (ps,bl) =
  let ty_vars_args, ty_vars_value, all_ty_params = ls_ty_vars ps in
  fprintf fmt "@[<hov 2>Inductive %a%a : %a -> Prop :=@ @[<hov>%a@].@]@\n"
     print_ls ps print_implicit_params all_ty_params
    (print_arrow_list (print_ty info)) ps.ls_args
     (print_list newline (print_ind info)) bl;
  print_implicits fmt ps ty_vars_args ty_vars_value all_ty_params;
  fprintf fmt "@\n"

let print_ind_decl info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn) then
    (print_ind_decl info fmt d; forget_tvs ())

let print_pkind info fmt = function
  | Paxiom ->
      if info.realization <> None then
        fprintf fmt "Lemma"
      else
        fprintf fmt "Axiom"
  | Plemma -> fprintf fmt "Lemma"
  | Pgoal  -> fprintf fmt "Theorem"
  | Pskip  -> assert false (* impossible *)

let print_proof ~old info fmt = function
  | Plemma | Pgoal ->
      realization ~old fmt true
  | Paxiom ->
      realization ~old fmt (info.realization <> None)
  | Pskip -> ()

let print_proof_context ~old info fmt = function
  | Plemma | Pgoal ->
      print_context ~old fmt
  | Paxiom ->
      if info.realization <> None then print_context ~old fmt
  | Pskip -> ()

let print_decl ~old info fmt d = match d.d_node with
  | Dtype tl  ->
      print_list nothing (print_type_decl ~old info) fmt tl
  | Dlogic [s,_ as ld] when not (Sid.mem s.ls_name d.d_syms) ->
      print_logic_decl ~old info fmt ld
  | Dlogic ll ->
      print_recursive_decl info fmt ll
  | Dind il   ->
      print_list nothing (print_ind_decl info) fmt il
  | Dprop (_,pr,_) when Mid.mem pr.pr_name info.info_syn ->
      ()
  | Dprop (k,pr,f) ->
      print_proof_context ~old info fmt k;
      let params = t_ty_freevars Stv.empty f in
      fprintf fmt "@[<hov 2>%a %a : %a%a.@]@\n%a"
        (print_pkind info) k
        print_pr pr
        print_params params
        (print_fmla info) f (print_proof ~old info) k;
      forget_tvs ()

let print_decls ~old info fmt dl =
  fprintf fmt "@[<hov>%a@\n@]" (print_list nothing (print_decl ~old info)) dl

let init_printer th =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let pr = create_ident_printer black_list ~sanitizer:isanitize in
  Sid.iter (fun id -> ignore (id_unique pr id)) th.Theory.th_local;
  pr

let print_task env pr thpr realize ?old fmt task =
  forget_all ();
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let realization,decls =
    if realize then
      let used = Task.used_theories task in
      let used = Mid.filter (fun _ th -> th.Theory.th_path <> []) used in
      (* 2 cases: goal is clone T with [] or goal is a real goal *)
      let used = match task with
        | None -> assert false
        | Some { Task.task_decl = { Theory.td_node = Theory.Clone (th,_) }} ->
            Sid.iter
              (fun id -> ignore (id_unique iprinter id))
              th.Theory.th_local;
            Mid.remove th.Theory.th_name used
        | _ -> used
      in
      (* output the Require commands *)
      List.iter
        (fprintf fmt "Add Rec LoadPath \"%s\".@\n")
        (Env.get_loadpath env);
      Mid.iter
        (fun id th -> fprintf fmt "Require %a.%s.@\n"
          print_path th.Theory.th_path id.id_string)
        used;
      let symbols = Task.used_symbols used in
      (* build the printers for each theories *)
      let printers = Mid.map init_printer used in
      let decls = Task.local_decls task symbols in
      let symbols =
        Mid.map (fun th -> (th,Mid.find th.Theory.th_name printers))
          symbols
      in
      Some symbols, decls
    else
      None, Task.task_decls task
  in
  let info = {
    info_syn = get_syntax_map task;
    realization = realization;
  }
  in
  let old = match old with
    | None -> None
    | Some ch -> Some(ref NoWhere,ch)
  in
  print_decls ~old info fmt decls

let print_task_full env pr thpr ?old fmt task =
  print_task env pr thpr false ?old fmt task

let print_task_real env pr thpr ?old fmt task =
  print_task env pr thpr true  ?old fmt task

let () = register_printer "coq" print_task_full
let () = register_printer "coq-realize" print_task_real

(* specific printer for realization of theories *)
(* OBSOLETE

open Theory

let print_tdecl ~old info fmt d = match d.td_node with
  | Decl d ->
      print_decl ~old info fmt d
  | Use t ->
      fprintf fmt "Require %s.@\n@\n"
        (id_unique iprinter t.th_name)
  | Meta _ -> assert false (* TODO ? *)
  | Clone _ -> assert false (* TODO *)

let print_tdecls ~old info fmt dl =
  fprintf fmt "@[<hov>%a@\n@]"
    (print_list nothing (print_tdecl ~old info)) dl

let print_theory _env pr thpr ?old fmt th =
  forget_all ();
  print_prelude fmt pr;
  print_prelude_for_theory th fmt thpr;
  let info = {
    info_syn = (Mid.empty : string Ident.Mid.t)
      (* get_syntax_map_of_theory th*);
    realization = true;
  }
  in
  let old = match old with
    | None -> None
    | Some ch -> Some(ref NoWhere,ch)
  in
  print_tdecls ~old info fmt th.th_decls;
  produce_remaining_contexts_and_proofs ~old fmt

*)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. "
End:
*)
