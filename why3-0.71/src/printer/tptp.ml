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

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Task
open Printer

let ident_printer =
  let bls = ["fof"; "axiom"; "conjecture"; "itef"] in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_symbol fmt id =
  let san = String.uncapitalize in
  fprintf fmt "%s" (id_unique ~sanitizer:san ident_printer id)

let print_var fmt {vs_name = id} =
  let san = String.capitalize in
  fprintf fmt "%s" (id_unique ~sanitizer:san ident_printer id)

let forget_var v = forget_id ident_printer v.vs_name

type info = {
  info_syn : syntax_map;
}

let rec print_term info fmt t = match t.t_node with
  | Tvar v -> print_var fmt v
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> begin match tl with (* toto() is not accepted *)
          | [] -> fprintf fmt "@[%a@]" print_symbol ls.ls_name
          | _ -> fprintf fmt "@[%a(%a)@]"  print_symbol ls.ls_name
                (print_list comma (print_term info)) tl
          end
      end
  | Tconst _ -> unsupportedTerm t
      "tptp : you must eliminate constants"
  | Tlet (_,_) -> unsupportedTerm t
      "tptp : you must eliminate let"
  | Tif (f1,t1,t2) ->
      fprintf fmt "@[itef(%a,@ %a,@ %a)@]"
        (print_fmla info) f1 (print_term info) t1 (print_term info) t2
  | Tcase _ -> unsupportedTerm t
      "tptp : you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "tptp : you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fmla info fmt f = match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
      print_symbol fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> fprintf fmt "@[%a(%a)@]"
              print_symbol ls.ls_name (print_list comma (print_term info)) tl
      end
  | Tquant (q, fq) ->
      let q = match q with Tforall -> "!" | Texists -> "?" in
      let vl, _tl, f = t_open_quant fq in
      fprintf fmt "%s [%a] :@ %a" q (print_list comma print_var) vl (print_fmla info) f;
      List.iter forget_var vl
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "@[(%a@ & %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "@[(%a@ | %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "@[(%a@ => %a)@]"
        (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "@[(%a@ <=> %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tnot f ->
      fprintf fmt "@[~@ (%a)@]" (print_fmla info) f
  | Ttrue ->
      fprintf fmt "$true"
  | Tfalse ->
      fprintf fmt "$false"
  | Tif (_,_,_) -> unsupportedTerm f "Tif not supported"
      (* fprintf fmt "@[(if_then_else %a@ %a@ %a)@]"
        (print_fmla info) f1 (print_fmla info) f2 (print_fmla info) f3 *)
  | Tlet (_, _) -> unsupportedTerm f "Tlet not supported"
      (* let v, f2 = t_open_bound tb in
      fprintf fmt "@[(let (%a %a)@ %a)@]" print_var v
        (print_term info) t1 (print_fmla info) f2;
      forget_var v *)
  | Tcase _ -> unsupportedTerm f
      "tptp : you must eliminate match"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

let print_logic_decl _ _ (_,ld) = match ld with
  | None -> ()
  | Some _ -> unsupported "Predicate and function definition aren't supported"

let print_logic_decl info fmt d =
  if Mid.mem (fst d).ls_name info.info_syn then
    false else (print_logic_decl info fmt d; true)

let print_decl info fmt d = match d.d_node with
  | Dtype _ -> false
      (* print_list_opt newline (print_type_decl info) fmt dl *)
  | Dlogic dl ->
      print_list_opt newline (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d
      "tptp : inductive definition are not supported"
  | Dprop (Paxiom, pr, _) when Mid.mem pr.pr_name info.info_syn -> false
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[<hov 2>fof(%s, axiom,@ %a).@]@\n"
        (id_unique ~sanitizer:String.uncapitalize ident_printer pr.pr_name)
        (print_fmla info) f; true
  | Dprop (Pgoal, pr, f) -> (* TODO : what is pr ? *)
      fprintf fmt "@[<hov 2>fof(%s, conjecture,@ %a ).@]@\n"
        (id_unique ~sanitizer:String.uncapitalize ident_printer pr.pr_name)
        (print_fmla info) f; true
      (* fprintf fmt "@[;; %a@]@\n" print_ident pr.pr_name; *)
  | Dprop ((Plemma|Pskip), _, _) -> assert false

let print_decl info fmt = catch_unsupportedDecl (print_decl info fmt)

let print_task pr thpr fmt task =
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let info = {
    info_syn = get_syntax_map task }
  in
  ignore (print_list_opt (add_flush newline2)
    (print_decl info) fmt (Task.task_decls task))

let () = register_printer "tptp"
  (fun _env pr thpr ?old:_ fmt task ->
     forget_all ident_printer;
     print_task pr thpr fmt task)

