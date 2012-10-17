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
open Why3
open Pp
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task

let keyword fmt s =
  pp_print_as fmt 0 "<span class=\"keyword\">";
  pp_print_string fmt s;
  pp_print_as fmt 0 "</span>"

let iprinter,tprinter,lprinter,pprinter =
  let bl = ["theory"; "type"; "logic"; "inductive"; "meta";
            "axiom"; "lemma"; "goal"; "use"; "clone"; "prop";
            "namespace"; "import"; "export"; "end";
            "forall"; "exists"; "and"; "or"; "not";
            "true"; "false"; "if"; "then"; "else";
            "let"; "in"; "match"; "with"; "as"; "epsilon" ]
  in
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
  let usanitize = sanitizer char_to_ualpha char_to_alnumus in
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:usanitize

let forget_all () =
  forget_all iprinter;
  forget_all tprinter;
  forget_all lprinter;
  forget_all pprinter

let tv_set = ref Sid.empty

(* type variables always start with a quote *)
let print_tv fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let sanitizer n = "'" ^ n in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer tv.tv_name)

let forget_tvs () =
  Sid.iter (forget_id iprinter) !tv_set;
  tv_set := Sid.empty

(* logic variables always start with a lower case letter *)
let print_vs fmt vs =
  let sanitizer = String.uncapitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer vs.vs_name)

let forget_var vs = forget_id iprinter vs.vs_name

(* pretty-print infix and prefix logic symbols *)

let extract_op ls =
  let s = ls.ls_name.id_string in
  let len = String.length s in
  if len < 7 then None else
  let inf = String.sub s 0 6 in
  if inf = "infix "  then Some (String.sub s 6 (len - 6)) else
  let prf = String.sub s 0 7 in
  if prf = "prefix " then Some (String.sub s 7 (len - 7)) else
  None

let tight_op s = let c = String.sub s 0 1 in c = "!" || c = "?"

let escape_op s =
  let s = Str.replace_first (Str.regexp "^\\*.") " \\0" s in
  let s = Str.replace_first (Str.regexp ".\\*$") "\\0 " s in
  s

(* theory names always start with an upper case letter *)
let print_th fmt th =
  let sanitizer = String.capitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer th.th_name)

let print_ts fmt ts =
  fprintf fmt "%s" (id_unique tprinter ts.ts_name)

let print_ls fmt ls = match extract_op ls with
  | Some s -> fprintf fmt "(%s)" (escape_op s)
  | None   -> fprintf fmt "%s" (id_unique lprinter ls.ls_name)

let print_cs fmt ls =
  let sanitizer = String.capitalize in
  fprintf fmt "%s" (id_unique lprinter ~sanitizer ls.ls_name)

let print_pr fmt pr =
  fprintf fmt "%s" (id_unique pprinter pr.pr_name)

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_ty_node inn fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, tl) when is_ts_tuple ts -> fprintf fmt "(%a)"
      (print_list comma (print_ty_node false)) tl
  | Tyapp (ts, []) -> print_ts fmt ts
  | Tyapp (ts, tl) -> fprintf fmt (protect_on inn "%a@ %a")
      print_ts ts (print_list space (print_ty_node true)) tl

let print_ty = print_ty_node false

let print_const fmt = function
  | ConstInt s -> fprintf fmt "%s" s
  | ConstReal (RConstDecimal (i,f,None)) -> fprintf fmt "%s.%s" i f
  | ConstReal (RConstDecimal (i,f,Some e)) -> fprintf fmt "%s.%se%s" i f e
  | ConstReal (RConstHexa (i,f,e)) -> fprintf fmt "0x%s.%sp%s" i f e

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

let rec print_pat_node pri fmt p = match p.pat_node with
  | Pwild ->
      fprintf fmt "_"
  | Pvar v ->
      print_vs fmt v
  | Pas (p, v) ->
      fprintf fmt (protect_on (pri > 1) "%a as %a")
        (print_pat_node 1) p print_vs v
  | Por (p, q) ->
      fprintf fmt (protect_on (pri > 0) "%a | %a")
        (print_pat_node 0) p (print_pat_node 0) q
  | Papp (cs, pl) when is_fs_tuple cs ->
      fprintf fmt (protect_on (pri > 0) "%a")
        (print_list comma (print_pat_node 1)) pl
  | Papp (cs, []) ->
      print_cs fmt cs
  | Papp (cs, pl) ->
      fprintf fmt (protect_on (pri > 1) "%a@ %a")
        print_cs cs (print_list space (print_pat_node 2)) pl

let print_pat = print_pat_node 0

let print_vsty fmt v =
  fprintf fmt "%a:@,%a" print_vs v print_ty v.vs_ty

let print_quant fmt = function
  | Fforall -> fprintf fmt "forall"
  | Fexists -> fprintf fmt "exists"

let print_binop fmt = function
  | Fand -> fprintf fmt "and"
  | For -> fprintf fmt "or"
  | Fimplies -> fprintf fmt "->"
  | Fiff -> fprintf fmt "<->"

let prio_binop = function
  | Fand -> 3
  | For -> 2
  | Fimplies -> 1
  | Fiff -> 1

let print_label fmt l =
  if l = "" then () else fprintf fmt "\"%s\"" l

let rec print_term fmt t = print_lterm 0 fmt t
and     print_fmla fmt f = print_lfmla 0 fmt f

and print_lterm pri fmt t = match t.t_label with
  | [] -> print_tnode pri fmt t
  | ll -> fprintf fmt (protect_on (pri > 0) "%a %a")
      (print_list space print_label) ll (print_tnode 0) t

and print_lfmla pri fmt f = match f.f_label with
  | [] -> print_fnode pri fmt f
  | ll -> fprintf fmt (protect_on (pri > 0) "%a %a")
      (print_list space print_label) ll (print_fnode 0) f

and print_app pri ls fmt tl = match extract_op ls, tl with
  | _, [] ->
      print_ls fmt ls
  | Some s, [t1] when tight_op s ->
      fprintf fmt (protect_on (pri > 6) "%s%a")
        s (print_lterm 6) t1
  | Some s, [t1] ->
      fprintf fmt (protect_on (pri > 4) "%s %a")
        s (print_lterm 5) t1
  | Some s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 4) "%a %s@ %a")
        (print_lterm 5) t1 s (print_lterm 5) t2
  | _, tl ->
      fprintf fmt (protect_on (pri > 5) "%a@ %a")
        print_ls ls (print_list space (print_lterm 6)) tl

and print_tnode pri fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      print_const fmt c
  | Tapp (fs, tl) when is_fs_tuple fs ->
      fprintf fmt "(%a)" (print_list comma print_term) tl
  | Tapp (fs, tl) when unambig_fs fs ->
      print_app pri fs fmt tl
  | Tapp (fs, tl) ->
      fprintf fmt (protect_on (pri > 0) "%a:%a")
        (print_app 5 fs) tl print_ty t.t_ty
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on (pri > 0) "if @[%a@] then %a@ else %a")
        print_fmla f print_term t1 print_term t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on (pri > 0) "let %a = @[%a@] in@ %a")
        print_vs v (print_lterm 4) t1 print_term t2;
      forget_var v
  | Tcase (t1,bl) ->
      fprintf fmt "match @[%a@] with@\n@[<hov>%a@]@\nend"
        print_term t1 (print_list newline print_tbranch) bl
  | Teps fb ->
      let v,f = t_open_bound fb in
      fprintf fmt (protect_on (pri > 0) "epsilon %a.@ %a")
        print_vsty v print_fmla f;
      forget_var v

and print_fnode pri fmt f = match f.f_node with
  | Fapp (ps,tl) ->
      print_app pri ps fmt tl
  | Fquant (q,fq) ->
      let vl,tl,f = t_open_quant fq in
      fprintf fmt (protect_on (pri > 0) "%a %a%a.@ %a") print_quant q
        (print_list comma print_vsty) vl print_tl tl print_fmla f;
      List.iter forget_var vl
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fbinop (b,f1,f2) ->
      let p = prio_binop b in
      fprintf fmt (protect_on (pri > p) "%a %a@ %a")
        (print_lfmla (p + 1)) f1 print_binop b (print_lfmla p) f2
  | Fnot f ->
      fprintf fmt (protect_on (pri > 4) "not %a") (print_lfmla 4) f
  | Fif (f1,f2,f3) ->
      fprintf fmt (protect_on (pri > 0) "if @[%a@] then %a@ else %a")
        print_fmla f1 print_fmla f2 print_fmla f3
  | Flet (t,f) ->
      let v,f = t_open_bound f in
      fprintf fmt (protect_on (pri > 0) "let %a = @[%a@] in@ %a")
        print_vs v (print_lterm 4) t print_fmla f;
      forget_var v
  | Fcase (t,bl) ->
      fprintf fmt "match @[%a@] with@\n@[<hov>%a@]@\nend"
        print_term t (print_list newline print_fbranch) bl

and print_tbranch fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_term t;
  Svs.iter forget_var p.pat_vars

and print_fbranch fmt br =
  let p,f = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_fmla f;
  Svs.iter forget_var p.pat_vars

and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_expr)) tl

and print_expr fmt = t_select (print_term fmt) (print_fmla fmt)

(** Declarations *)

let print_tv_arg fmt tv = fprintf fmt "@ %a" print_tv tv
let print_ty_arg fmt ty = fprintf fmt "@ %a" (print_ty_node true) ty
let print_vs_arg fmt vs = fprintf fmt "@ (%a)" print_vsty vs

let print_constr ty fmt cs =
  let ty_val = of_option cs.ls_value in
  let m = ty_match Mtv.empty ty_val ty in
  let tl = List.map (ty_inst m) cs.ls_args in
  fprintf fmt "@[<hov 4>| %a%a@]" print_cs cs
    (print_list nothing print_ty_arg) tl

let print_type_decl fst fmt (ts,def) = match def with
  | Tabstract -> begin match ts.ts_def with
      | None ->
          fprintf fmt "@[<hov 2>%a %a%a@]"
            keyword (if fst then "type" else "with") print_ts ts
            (print_list nothing print_tv_arg) ts.ts_args
      | Some ty ->
          fprintf fmt "@[<hov 2>%a %a%a =@ %a@]"
            keyword (if fst then "type" else "with") print_ts ts
            (print_list nothing print_tv_arg) ts.ts_args print_ty ty
      end
  | Talgebraic csl ->
      let ty = ty_app ts (List.map ty_var ts.ts_args) in
      fprintf fmt "@[<hov 2>%a %a%a =@\n@[<hov>%a@]@]"
        keyword (if fst then "type" else "with") print_ts ts
        (print_list nothing print_tv_arg) ts.ts_args
        (print_list newline (print_constr ty)) csl

let print_type_decl fst fmt d = print_type_decl fst fmt d; forget_tvs ()

let print_ls_type fmt = fprintf fmt " :@ %a" print_ty

let print_logic_decl fst fmt (ls,ld) = match ld with
  | Some ld ->
      let vl,e = open_ls_defn ld in
      fprintf fmt "@[<hov 2>%a %a%a%a =@ %a@]"
        keyword (if fst then "logic" else "with") print_ls ls
        (print_list nothing print_vs_arg) vl
        (print_option print_ls_type) ls.ls_value print_expr e;
      List.iter forget_var vl
  | None ->
      fprintf fmt "@[<hov 2>%a %a%a%a@]"
        keyword (if fst then "logic" else "with") print_ls ls
        (print_list nothing print_ty_arg) ls.ls_args
        (print_option print_ls_type) ls.ls_value

let print_logic_decl fst fmt d = print_logic_decl fst fmt d; forget_tvs ()

let print_ind fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a : %a@]" print_pr pr print_fmla f

let print_ind_decl fst fmt (ps,bl) =
  fprintf fmt "@[<hov 2>%a %a%a =@ @[<hov>%a@]@]"
    keyword (if fst then "inductive" else "with") print_ls ps
    (print_list nothing print_ty_arg) ps.ls_args
    (print_list newline print_ind) bl;
  forget_tvs ()

let sprint_pkind = function
  | Paxiom -> "axiom"
  | Plemma -> "lemma"
  | Pgoal  -> "goal"
  | Pskip  -> "skip"

let print_pkind fmt k = fprintf fmt "%a" keyword (sprint_pkind k)

let print_prop_decl fmt (k,pr,f) =
  fprintf fmt "@[<hov 2>%a %a : %a@]" print_pkind k
    print_pr pr print_fmla f;
  forget_tvs ()

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r -> print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let print_decl fmt d = match d.d_node with
  | Dtype tl  -> print_list_next newline print_type_decl fmt tl
  | Dlogic ll -> print_list_next newline print_logic_decl fmt ll
  | Dind il   -> print_list_next newline print_ind_decl fmt il
  | Dprop p   -> print_prop_decl fmt p

let print_next_type_decl  = print_type_decl false
let print_type_decl       = print_type_decl true
let print_next_logic_decl = print_logic_decl false
let print_logic_decl      = print_logic_decl true
let print_next_ind_decl   = print_ind_decl false
let print_ind_decl        = print_ind_decl true

let print_inst_ts fmt (ts1,ts2) =
  fprintf fmt "type %a = %a" print_ts ts1 print_ts ts2

let print_inst_ls fmt (ls1,ls2) =
  fprintf fmt "logic %a = %a" print_ls ls1 print_ls ls2

let print_inst_pr fmt (pr1,pr2) =
  fprintf fmt "prop %a = %a" print_pr pr1 print_pr pr2

let print_meta_arg_type fmt = function
  | MTty       -> fprintf fmt "[type]"
  | MTtysymbol -> fprintf fmt "[type symbol]"
  | MTlsymbol  -> fprintf fmt "[logic symbol]"
  | MTprsymbol -> fprintf fmt "[proposition]"
  | MTstring   -> fprintf fmt "[string]"
  | MTint      -> fprintf fmt "[integer]"

let print_meta_arg fmt = function
  | MAty ty -> fprintf fmt "type %a" print_ty ty
  | MAts ts -> fprintf fmt "type %a" print_ts ts
  | MAls ls -> fprintf fmt "logic %a" print_ls ls
  | MApr pr -> fprintf fmt "prop %a" print_pr pr
  | MAstr s -> fprintf fmt "\"%s\"" s
  | MAint i -> fprintf fmt "%d" i

let print_tdecl fmt td = match td.td_node with
  | Decl d ->
      print_decl fmt d
  | Use th ->
      fprintf fmt "@[<hov 2>(* use %a *)@]" print_th th
  | Clone (th,sm) when is_empty_sm sm ->
      fprintf fmt "@[<hov 2>(* use %a *)@]" print_th th
  | Clone (th,sm) ->
      let tm = Mts.fold (fun x y a -> (x,y)::a) sm.sm_ts [] in
      let lm = Mls.fold (fun x y a -> (x,y)::a) sm.sm_ls [] in
      let pm = Mpr.fold (fun x y a -> (x,y)::a) sm.sm_pr [] in
      fprintf fmt "@[<hov 2>(* clone %a with %a,@ %a,@ %a *)@]"
        print_th th (print_list comma print_inst_ts) tm
                    (print_list comma print_inst_ls) lm
                    (print_list comma print_inst_pr) pm
  | Meta (m,al) ->
      fprintf fmt "@[<hov 2>(* meta %s %a *)@]"
        m.meta_name (print_list comma print_meta_arg) al

let print_theory fmt th =
  fprintf fmt "@[<hov 2>%a %a@\n%a@]@\n%a@."
    keyword "theory"
    print_th th (print_list newline2 print_tdecl) th.th_decls
    keyword "end"

(* HTML stuff *)

let print_header fmt ?(title="") ?css () =
  fprintf fmt "<html>@\n<head>@\n";
  begin match css with
    | None -> ()
    | Some f -> fprintf fmt
        "<link rel=\"stylesheet\" href=\"%s\" type=\"text/css\">@\n" f
  end;
  fprintf fmt "<title>%s</title>@\n" title;
  fprintf fmt "</head>@\n<body>@\n<pre>@\n"

let print_footer fmt () =
  fprintf fmt "</pre></body>@."

let style_css fname =
  let c = open_out fname in
  output_string c
"a:visited {color : #416DFF; text-decoration : none; }
a:link {color : #416DFF; text-decoration : none;}
a:hover {color : Red; text-decoration : none; background-color: #5FFF88}
a:active {color : Red; text-decoration : underline; }
.keyword { font-weight : bold ; color : Red }
.keywordsign { color : #C04600 }
.superscript { font-size : 4 }
.subscript { font-size : 4 }
.comment { color : Green }
.constructor { color : Blue }
.type { color : #5C6585 }
.string { color : Maroon }
.warning { color : Red ; font-weight : bold }
.info { margin-left : 3em; margin-right : 3em }
.code { color : #465F91 ; }
h1 { font-size : 20pt ; text-align: center; }
h2 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90BDFF ;padding: 2px; }
h3 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90DDFF ;padding: 2px; }
h4 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90EDFF ;padding: 2px; }
h5 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90FDFF ;padding: 2px; }
h6 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90BDFF ; padding: 2px; }
div.h7 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90DDFF ; padding: 2px; }
div.h8 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #F0FFFF ; padding: 2px; }
div.h9 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #FFFFFF ; padding: 2px; }
.typetable { border-style : hidden }
.indextable { border-style : hidden }
.paramstable { border-style : hidden ; padding: 5pt 5pt}
body { background-color : White }
tr { background-color : White }
td.typefieldcomment { background-color : #FFFFFF }
pre { margin-bottom: 4px }
div.sig_block {margin-left: 2em}";
  close_out c

