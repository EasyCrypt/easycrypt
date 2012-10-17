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
open Theory
open Task

(** Register printers *)

type prelude = string list
type prelude_map = prelude Mid.t

type 'a pp = formatter -> 'a -> unit

type printer = Env.env -> prelude -> prelude_map -> ?old:in_channel -> task pp

let printers : (string, printer) Hashtbl.t = Hashtbl.create 17

exception KnownPrinter of string
exception UnknownPrinter of string

let register_printer s p =
  if Hashtbl.mem printers s then raise (KnownPrinter s);
  Hashtbl.replace printers s p

let lookup_printer s =
  try Hashtbl.find printers s
  with Not_found -> raise (UnknownPrinter s)

let list_printers ()  = Hashtbl.fold (fun k _ acc -> k::acc) printers []

let () = register_printer "(null)" (fun _ _ _ ?old:_ _ _ -> ())

(** Syntax substitutions *)

let opt_search_forward re s pos =
  try Some (Str.search_forward re s pos) with Not_found -> None

let global_substitute_fmt expr repl_fun text fmt =
  let rec replace start last_was_empty =
    let startpos = if last_was_empty then start + 1 else start in
    if startpos > String.length text then
      pp_print_string fmt (Str.string_after text start)
    else
      match opt_search_forward expr text startpos with
      | None ->
          pp_print_string fmt (Str.string_after text start)
      | Some pos ->
          let end_pos = Str.match_end () in
          pp_print_string fmt (String.sub text start (pos - start));
          repl_fun text fmt;
          replace end_pos (end_pos = pos)
  in
  replace 0 false

let iter_group expr iter_fun text =
  let rec iter start last_was_empty =
    let startpos = if last_was_empty then start + 1 else start in
    if startpos < String.length text then
      match opt_search_forward expr text startpos with
      | None -> ()
      | Some pos ->
          let end_pos = Str.match_end () in
          iter_fun text;
          iter end_pos (end_pos = pos)
  in
  iter 0 false

let regexp_arg_pos = Str.regexp "%\\([0-9]+\\)"
let regexp_arg_pos_typed = Str.regexp "%\\([t]?[0-9]+\\)"

exception BadSyntaxIndex of int
exception BadSyntaxArity of int * int

let check_syntax s len =
  let arg s =
    let i = int_of_string (Str.matched_group 1 s) in
    if i <= 0 then raise (BadSyntaxIndex i);
    if i > len then raise (BadSyntaxArity (len,i));
  in
  iter_group regexp_arg_pos arg s

let check_syntax_typed s len ret =
  let arg s =
    let grp = (Str.matched_group 1 s) in
    if grp.[0] = 't'
    then
      let grp = String.sub grp 1 (String.length grp - 1) in
      let i = int_of_string grp in
      if i < 0 || (not ret && i = 0) then raise (BadSyntaxIndex i);
      if i > len then raise (BadSyntaxArity (len,i));
    else
      let i = int_of_string grp in
      if i <= 0 then raise (BadSyntaxIndex i);
      if i > len then raise (BadSyntaxArity (len,i));
  in
  iter_group regexp_arg_pos_typed arg s

let syntax_arguments s print fmt l =
  let args = Array.of_list l in
  let repl_fun s fmt =
    let i = int_of_string (Str.matched_group 1 s) in
    print fmt args.(i-1) in
  global_substitute_fmt regexp_arg_pos repl_fun s fmt

let syntax_arguments_typed s print_arg print_type t fmt l =
  let args = Array.of_list l in
  let repl_fun s fmt =
    let grp = (Str.matched_group 1 s) in
    if grp.[0] = 't'
    then
      let grp = String.sub grp 1 (String.length grp - 1) in
      let i = int_of_string grp in
      if i = 0
      then print_type fmt (t_type (Util.of_option t))
      else print_type fmt (t_type args.(i-1))
    else
      let i = int_of_string grp in
      print_arg fmt args.(i-1) in
  global_substitute_fmt regexp_arg_pos_typed repl_fun s fmt

(** {2 use printers} *)

let print_prelude fmt pl =
  let println fmt s = fprintf fmt "%s@\n" s in
  print_list nothing println fmt pl

let print_prelude_of_theories th_used fmt pm =
  List.iter (fun th ->
               let prel = Mid.find_default th.th_name [] pm in
               print_prelude fmt prel) th_used

let print_th_prelude task fmt pm =
  let th_used = task_fold (fun acc -> function
    | { td_node = Clone (th,sm) } when is_empty_sm sm -> th::acc
    | _ -> acc) [] task
  in
  print_prelude_of_theories th_used fmt pm

let print_prelude_for_theory th fmt pm =
  let th_used = List.fold_left (fun acc -> function
    | { td_node = Clone (th,sm) } when is_empty_sm sm -> th::acc
    | _ -> acc) [] th.th_decls
  in
  print_prelude_of_theories th_used fmt pm

exception KnownTypeSyntax of tysymbol
exception KnownLogicSyntax of lsymbol

let meta_syntax_type  = register_meta "syntax_type" [MTtysymbol; MTstring]
let meta_syntax_logic = register_meta "syntax_logic" [MTlsymbol; MTstring]
let meta_remove_prop  = register_meta "remove_prop" [MTprsymbol]

let syntax_type ts s =
  check_syntax s (List.length ts.ts_args);
  create_meta meta_syntax_type [MAts ts; MAstr s]

let syntax_logic ls s =
  check_syntax_typed s (List.length ls.ls_args) (ls.ls_value <> None);
  create_meta meta_syntax_logic [MAls ls; MAstr s]

let remove_prop pr =
  create_meta meta_remove_prop [MApr pr]

type syntax_map = string Mid.t

let sm_add_ts sm = function
  | [MAts ts; MAstr rs] -> Mid.add_new ts.ts_name rs (KnownTypeSyntax ts) sm
  | _ -> assert false

let sm_add_ls sm = function
  | [MAls ls; MAstr rs] -> Mid.add_new ls.ls_name rs (KnownLogicSyntax ls) sm
  | _ -> assert false

let sm_add_pr sm = function
  | [MApr pr] -> Mid.add pr.pr_name "" sm
  | _ -> assert false

let get_syntax_map task =
  let sm = Mid.empty in
  let sm = Task.on_meta meta_syntax_type sm_add_ts sm task in
  let sm = Task.on_meta meta_syntax_logic sm_add_ls sm task in
  let sm = Task.on_meta meta_remove_prop sm_add_pr sm task in
  sm

(*
let get_syntax_map_of_theory theory =
  let sm = Mid.empty in
  let sm = Theory.on_meta meta_syntax_type sm_add_ts sm theory in
  let sm = Theory.on_meta meta_syntax_logic sm_add_ls sm theory in
  let sm = Theory.on_meta meta_remove_prop sm_add_pr sm theory in
  sm
*)

let query_syntax sm id = Mid.find_option id sm

let fold_tdecls fn acc =
  Trans.on_meta meta_syntax_type (fun sts ->
  Trans.on_meta meta_syntax_logic (fun sls ->
  Trans.on_meta meta_remove_prop (fun spr ->
    let sm = Mid.empty in
    let sm = List.fold_left sm_add_ts sm sts in
    let sm = List.fold_left sm_add_ls sm sls in
    let sm = List.fold_left sm_add_pr sm spr in
    Trans.fold (fun t -> fn sm t.task_decl) acc)))

let sprint_tdecls (fn : syntax_map -> tdecl pp) =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  let print sm td acc =
    Buffer.reset buf;
    Format.fprintf fmt "%a@?" (fn sm) td;
    Buffer.contents buf :: acc in
  fold_tdecls print []

let sprint_decls (fn : syntax_map -> decl pp) =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  let print sm td acc = match td.td_node with
    | Decl d ->
        Buffer.reset buf;
        Format.fprintf fmt "%a@?" (fn sm) d;
        Buffer.contents buf :: acc
    | _ -> acc in
  fold_tdecls print []

(** {2 exceptions to use in transformations and printers} *)

exception UnsupportedType of ty   * string
exception UnsupportedTerm of term * string
exception UnsupportedDecl of decl * string
exception NotImplemented  of        string
exception Unsupported     of        string

(** {3 functions that catch inner error} *)

let unsupportedType e s = raise (UnsupportedType (e,s))
let unsupportedTerm e s = raise (UnsupportedTerm (e,s))
let unsupportedDecl e s = raise (UnsupportedDecl (e,s))
let notImplemented    s = raise (NotImplemented s)
let unsupported       s = raise (Unsupported s)

let catch_unsupportedType f e =
  try f e with Unsupported s -> unsupportedType e s

let catch_unsupportedTerm f e =
  try f e with Unsupported s -> unsupportedTerm e s

let catch_unsupportedDecl f e =
  try f e with Unsupported s -> unsupportedDecl e s

let () = Exn_printer.register (fun fmt exn -> match exn with
  | KnownPrinter s ->
      fprintf fmt "Printer '%s' is already registered" s
  | UnknownPrinter s ->
      fprintf fmt "Unknown printer '%s'" s
  | KnownTypeSyntax ts ->
      fprintf fmt "Syntax for type symbol %a is already defined"
        Pretty.print_ts ts
  | KnownLogicSyntax ls ->
      fprintf fmt "Syntax for logical symbol %a is already defined"
        Pretty.print_ls ls
  | BadSyntaxIndex i ->
      fprintf fmt "Bad argument index %d, must start with 1" i
  | BadSyntaxArity (i1,i2) ->
      fprintf fmt "Bad argument index %d, must end with %d" i2 i1
  | Unsupported s ->
      fprintf fmt "@[<hov 3> Uncatched exception 'Unsupported %s'@]" s
  | UnsupportedType (e,s) ->
      fprintf fmt "@[@[<hov 3> This type isn't supported:@\n%a@]@\n %s@]"
        Pretty.print_ty e s
  | UnsupportedTerm (e,s) ->
      fprintf fmt "@[@[<hov 3> This expression isn't supported:@\n%a@]@\n %s@]"
        Pretty.print_term e s
  | UnsupportedDecl (d,s) ->
      fprintf fmt "@[@[<hov 3> This declaration isn't supported:@\n%a@]@\n %s@]"
        Pretty.print_decl d s
  | NotImplemented (s) ->
      fprintf fmt "@[<hov 3> Unimplemented feature:@\n%s@]" s
  | e -> raise e)

