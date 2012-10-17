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

(** Alt-ergo printer *)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Task
open Printer

let meta_ac = Theory.register_meta "AC" [Theory.MTlsymbol]

let ident_printer =
  let bls = [
    "ac"; "and"; "array"; "as"; "axiom"; "bool"; "distinct"; "else"; "exists";
    "false"; "forall"; "function"; "goal"; "if"; "int"; "bitv";
    "logic"; "not"; "or"; "parameter"; "predicate";
    "prop"; "real"; "then"; "true"; "type"; "unit"; "void";
    "select"; "store";
  ]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let forget_var v = forget_id ident_printer v.vs_name

let tv_printer =
  let san = sanitizer char_to_lalpha char_to_alnumus in
  create_ident_printer [] ~sanitizer:san

let print_tvsymbol fmt tv =
  fprintf fmt "'%s" (id_unique tv_printer tv.tv_name)

let forget_tvs () = forget_all tv_printer

type info = {
  info_syn : syntax_map;
  info_ac  : Sls.t;
}

let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar id ->
      print_tvsymbol fmt id
  | Tyapp (ts, tl) -> begin match query_syntax info.info_syn ts.ts_name with
      | Some s -> syntax_arguments s (print_type info) fmt tl
      | None -> fprintf fmt "%a%a" (print_tyapp info) tl print_ident ts.ts_name
    end

and print_tyapp info fmt = function
  | [] -> ()
  | [ty] -> fprintf fmt "%a " (print_type info) ty
  | tl -> fprintf fmt "(%a) " (print_list comma (print_type info)) tl

let rec print_term info fmt t = match t.t_node with
  | Tconst c ->
      let number_format = {
          Print_number.long_int_support = true;
          Print_number.dec_int_support = Print_number.Number_default;
          Print_number.hex_int_support = Print_number.Number_unsupported;
          Print_number.oct_int_support = Print_number.Number_unsupported;
          Print_number.bin_int_support = Print_number.Number_unsupported;
          Print_number.def_int_support = Print_number.Number_unsupported;
          Print_number.dec_real_support = Print_number.Number_default;
          Print_number.hex_real_support = Print_number.Number_default;
          Print_number.frac_real_support = Print_number.Number_unsupported;
          Print_number.def_real_support = Print_number.Number_unsupported;
        } in
      Print_number.print number_format fmt c
  | Tvar { vs_name = id } ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> fprintf fmt "%a%a" print_ident ls.ls_name (print_tapp info) tl
    end
  | Tlet _ -> unsupportedTerm t
      "alt-ergo : you must eliminate let in term"
  | Tif _ -> unsupportedTerm t
      "alt-ergo : you must eliminate if_then_else"
  | Tcase _ -> unsupportedTerm t
      "alt-ergo : you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "alt-ergo : you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_tapp info fmt = function
  | [] -> ()
  | tl -> fprintf fmt "(%a)" (print_list comma (print_term info)) tl

let rec print_fmla info fmt f = match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> fprintf fmt "%a(%a)" print_ident ls.ls_name
                    (print_list comma (print_term info)) tl
    end
  | Tquant (q, fq) ->
      let vl, tl, f = t_open_quant fq in
      let q, tl = match q with
        | Tforall -> "forall", tl
        | Texists -> "exists", [] (* Alt-ergo has no triggers for exists *)
      in
      let forall fmt v =
        fprintf fmt "%s %a:%a" q print_ident v.vs_name (print_type info) v.vs_ty
      in
      fprintf fmt "@[(%a%a.@ %a)@]" (print_list dot forall) vl
        (print_triggers info) tl (print_fmla info) f;
      List.iter forget_var vl
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "(%a and@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "(%a or@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "(%a ->@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "(%a <->@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Tnot f ->
      fprintf fmt "(not %a)" (print_fmla info) f
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tif (f1, f2, f3) ->
      fprintf fmt "((%a and %a) or (not %a and %a))"
        (print_fmla info) f1 (print_fmla info) f2 (print_fmla info)
        f1 (print_fmla info) f3
  | Tlet _ -> unsupportedTerm f
      "alt-ergo : you must eliminate let in formula"
  | Tcase _ -> unsupportedTerm f
      "alt-ergo : you must eliminate match"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

and print_triggers info fmt tl =
  let filter = function
    | { t_ty = Some _ } -> true
    | { t_node = Tapp (ps,_) } -> not (ls_equal ps ps_equ)
    | _ -> false in
  let tl = List.map (List.filter filter) tl in
  let tl = List.filter (function [] -> false | _::_ -> true) tl in
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_expr info))) tl

let print_logic_binder info fmt v =
  fprintf fmt "%a: %a" print_ident v.vs_name (print_type info) v.vs_ty

let print_type_decl fmt ts = match ts.ts_args with
  | [] -> fprintf fmt "type %a@\n@\n"
      print_ident ts.ts_name
  | [tv] -> fprintf fmt "type %a %a@\n@\n"
      print_tvsymbol tv print_ident ts.ts_name
  | tl -> fprintf fmt "type (%a) %a@\n@\n"
      (print_list comma print_tvsymbol) tl print_ident ts.ts_name

let print_type_decl info fmt = function
  | ts, Tabstract when Mid.mem ts.ts_name info.info_syn -> ()
  | ts, Tabstract -> print_type_decl fmt ts; forget_tvs ()
  | _, Talgebraic _ -> unsupported
      "alt-ergo : algebraic datatype are not supported"

let print_logic_decl info fmt ls = function
    | None ->
        let sac = if Sls.mem ls info.info_ac then "ac " else "" in
        fprintf fmt "@[<hov 2>logic %s%a : %a%s%a@]@\n@\n"
          sac print_ident ls.ls_name
          (print_list comma (print_type info)) ls.ls_args
          (if ls.ls_args = [] then "" else " -> ")
          (print_option_or_default "prop" (print_type info)) ls.ls_value
    | Some ld ->
        let vl,e = open_ls_defn ld in
        begin match e.t_ty with
          | Some _ ->
              (* TODO AC? *)
              fprintf fmt "@[<hov 2>function %a(%a) : %a =@ %a@]@\n@\n"
                print_ident ls.ls_name
                (print_list comma (print_logic_binder info)) vl
                (print_type info) (Util.of_option ls.ls_value)
                (print_term info) e
          | None ->
              fprintf fmt "@[<hov 2>predicate %a(%a) =@ %a@]@\n@\n"
                print_ident ls.ls_name
                (print_list comma (print_logic_binder info)) vl
                (print_fmla info) e
        end;
        List.iter forget_var vl

let print_logic_decl info fmt (ls,ld) =
  if Mid.mem ls.ls_name info.info_syn then () else
  print_logic_decl info fmt ls ld; forget_tvs ()

let print_prop_decl info fmt k pr f = match k with
  | Paxiom ->
      fprintf fmt "@[<hov 2>axiom %a :@ %a@]@\n@\n"
        print_ident pr.pr_name (print_fmla info) f
  | Pgoal ->
      fprintf fmt "@[<hov 2>goal %a :@ %a@]@\n"
        print_ident pr.pr_name (print_fmla info) f
  | Plemma| Pskip -> assert false

let print_prop_decl info fmt k pr f =
  if Mid.mem pr.pr_name info.info_syn then () else
  print_prop_decl info fmt k pr f; forget_tvs ()

let print_decl info fmt d = match d.d_node with
  | Dtype dl ->
      print_list nothing (print_type_decl info) fmt dl
  | Dlogic dl ->
      print_list nothing (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d
      "alt-ergo : inductive definition are not supported"
  | Dprop (k,pr,f) -> print_prop_decl info fmt k pr f

let print_decl info fmt = catch_unsupportedDecl (print_decl info fmt)

let print_task_old pr thpr fmt task =
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let info = {
    info_syn = get_syntax_map task;
    info_ac  = Task.on_tagged_ls meta_ac task }
  in
  let decls = Task.task_decls task in
  fprintf fmt "%a@." (print_list nothing (print_decl info)) decls

let () = register_printer "alt-ergo-old"
  (fun _env pr thpr ?old:_ fmt task ->
     forget_all ident_printer;
     print_task_old pr thpr fmt task)

let print_decls =
  let print ac sm fmt d =
    let info = {
      info_syn = sm;
      info_ac  = ac } in
    print_decl info fmt d in
  Trans.on_tagged_ls meta_ac (fun ac ->
    Printer.sprint_decls (print ac))

let print_task _env pr thpr ?old:_ fmt task =
  (* In trans-based p-printing [forget_all] is a no-no *)
  (* forget_all ident_printer; *)
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  fprintf fmt "%a@." (print_list nothing string)
    (List.rev (Trans.apply print_decls task))

let () = register_printer "alt-ergo" print_task

(*
let print_goal info fmt (id, f, task) =
  print_task info fmt task;
  fprintf fmt "@\n@[<hov 2>goal %a : %a@]@\n" print_ident id (print_fmla info) f
*)

