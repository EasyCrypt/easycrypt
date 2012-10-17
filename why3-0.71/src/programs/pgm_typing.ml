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
open Theory
open Pretty
open Denv
open Ptree
open Pgm_ttree
open Pgm_types
open Pgm_types.T
open Pgm_module

let debug = Debug.register_flag "program_typing"
let is_debug () = Debug.test_flag debug

exception Message of string

let error ?loc e = match loc with
  | None -> raise e
  | Some loc -> raise (Loc.Located (loc, e))

let errorm ?loc f =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
       Format.pp_print_flush fmt ();
       let s = Buffer.contents buf in
       Buffer.clear buf;
       error ?loc (Message s))
    fmt f

let () = Exn_printer.register (fun fmt e -> match e with
  | Message s -> fprintf fmt "%s" s
  | _ -> raise e)

let id_result = "result"

(* Table of record mutable fields ******************************************)

let mutable_fields = Hts.create 17 (* ts -> field:int -> region:int *)

let declare_mutable_field ts i j =
  Pgm_wp.declare_mutable_field ts i j;
  let h =
    try
      Hts.find mutable_fields ts
    with Not_found ->
      let h = Hashtbl.create 17 in Hts.add mutable_fields ts h; h
  in
  Hashtbl.add h i j

let mutable_field ts i =
  Hashtbl.find (Hts.find mutable_fields ts) i
let is_mutable_field ts i =
  Hashtbl.mem (Hts.find mutable_fields ts) i

(* phase 1: typing programs (using destructive type inference) **************)

let find_ts ~pure uc s =
  ns_find_ts (get_namespace (if pure then pure_uc uc else impure_uc uc)) [s]
let find_ls ~pure uc s =
  ns_find_ls (get_namespace (if pure then pure_uc uc else impure_uc uc)) [s]

(* TODO: improve efficiency *)
let dty_bool uc = tyapp (find_ts ~pure:true uc "bool") []

let dty_int   = tyapp Ty.ts_int []
let dty_unit  = tyapp (Ty.ts_tuple 0) []
let dty_mark  = tyapp ts_mark []

(* note: local variables are simultaneously in locals (to type programs)
   and in denv (to type logic elements) *)
type denv = {
  uc     : uc;
  locals : Denv.dty Mstr.t;
  denv   : Typing.denv; (* for user type variables only *)
}

let create_denv uc =
  { uc = uc;
    locals = Mstr.empty;
    denv = Typing.create_denv (); }

let loc_of_id id = Util.of_option id.Ident.id_loc

let loc_of_ls ls = ls.ls_name.Ident.id_loc

let dcurrying tyl ty =
  let make_arrow_type ty1 ty2 = tyapp ts_arrow [ty1; ty2] in
  List.fold_right make_arrow_type tyl ty

type region_policy = Region_var | Region_ret | Region_glob

let rec create_regions ~user n =
  if n = 0 then
    []
  else
    let tv = create_tvsymbol (id_fresh "rho") in
    tyvar (create_ty_decl_var ~user tv) :: create_regions ~user (n - 1)

(* region variables are collected in the following list of lists
   so that we can check after typing that two region variables in the same
   list (i.e. for the same symbol) are not mapped to the same region *)

let region_vars = ref []

let new_regions_vars () =
  region_vars := Htv.create 17 :: !region_vars

let push_region_var tv vloc = match !region_vars with
  | [] -> assert false
  | h :: _ -> Htv.replace h tv vloc

let check_region_vars () =
  let values = Htv.create 17 in
  let check tv (v, loc) = match view_dty (tyvar v) with
    | Tyvar v'  ->
        let tv' = tvsymbol_of_type_var v' in
        begin try
          let tv'' = Htv.find values tv' in
          if not (tv_equal tv tv'') then
            errorm ~loc "this application would create an alias";
        with Not_found ->
          Htv.add values tv' tv
        end
    | Tyapp _ ->
        assert false
  in
  List.iter (fun h -> Htv.clear values; Htv.iter check h) !region_vars;
  region_vars := []

let is_fresh_region r =
  r.R.r_tv.tv_name.id_string = "fresh"

let rec specialize_ty ?(policy=Region_var) ~loc htv ty = match ty.ty_node with
  | Ty.Tyvar _ ->
      Denv.specialize_ty ~loc htv ty
  | Ty.Tyapp (ts, tl) ->
      let n = (get_mtsymbol ts).mt_regions in
      let mk_region ty = match ty.ty_node with
        | Ty.Tyvar _ when policy = Region_ret ->
            tyvar (Typing.create_user_type_var "fresh")
        | Ty.Tyvar tv when policy = Region_var ->
            let v = Denv.find_type_var ~loc htv tv in
            push_region_var tv (v, loc);
            tyvar v
        | Ty.Tyvar tv (* policy = Region_glob *) ->
            tyvar (create_ty_decl_var ~user:true tv)
        | Ty.Tyapp _ ->
            assert false
      in
      let regions = List.map mk_region (Util.prefix n tl) in
      let tl = List.map (specialize_ty ~policy ~loc htv) (Util.chop n tl) in
      tyapp ts (regions @ tl)

let rec specialize_type_v ?(policy=Region_var) ~loc htv = function
  | Tpure ty ->
      specialize_ty ~policy ~loc htv ty
  | Tarrow (bl, c) ->
      (* global regions must be different from local regions *)
      let globals =
        List.fold_left
          (fun acc pv -> Sreg.diff acc pv.pv_regions)
          (Sreg.union c.c_effect.E.reads c.c_effect.E.writes) bl
      in
      Sreg.iter
        (fun r ->
           let v = create_ty_decl_var ~user:true r.R.r_tv in
           push_region_var r.R.r_tv (v, loc))
        globals;
      dcurrying
        (List.map (fun pv -> specialize_type_v ~loc htv pv.pv_tv) bl)
        (specialize_type_v ~policy:Region_ret ~loc htv c.c_result_type)

let specialize_lsymbol ?(policy=Region_var) ~loc htv s =
  List.map (specialize_ty ~policy ~loc htv) s.ls_args,
  option_map (specialize_ty ~policy:Region_ret ~loc htv) s.ls_value

let parameter x = "parameter " ^ x
let rec parameter_q = function
  | [] -> assert false
  | [x] -> [parameter x]
  | x :: q -> x :: parameter_q q

let dot fmt () = pp_print_string fmt "."
let print_qualids = print_list dot pp_print_string
let print_qualid fmt q =
  print_list dot pp_print_string fmt (Typing.string_list_of_qualid [] q)

let specialize_exception loc x uc =
  let s =
    try ns_find_ex (namespace uc) x
    with Not_found -> errorm ~loc "@[unbound exception %a@]" print_qualids x
  in
  match Denv.specialize_lsymbol ~loc s with
    | tyl, Some ty -> s, tyl, ty
    | _, None -> assert false

let create_type_var loc =
  let tv = Ty.create_tvsymbol (id_user "a" loc) in
  tyvar (create_ty_decl_var ~loc ~user:false tv)

let add_pure_var id ty denv = match view_dty ty with
  | Tyapp (ts, _) when Ty.ts_equal ts ts_arrow -> denv
  | _ -> Typing.add_var id ty denv

let uncurrying ty =
  let rec uncurry acc ty = match ty.ty_node with
    | Ty.Tyapp (ts, [t1; t2]) when ts_equal ts ts_arrow ->
        uncurry (t1 :: acc) t2
    | _ ->
        List.rev acc, ty
  in
  uncurry [] ty

let expected_type e ty =
  if not (Denv.unify e.dexpr_type ty) then
    errorm ~loc:e.dexpr_loc
      "@[this expression has type %a,@ but is expected to have type %a@]"
      print_dty e.dexpr_type print_dty ty

let check_mutable_type loc dty = match view_dty dty with
  | Denv.Tyapp (ts, _) when is_mutable_ts ts ->
      ()
  | _ ->
      errorm ~loc
      "@[this expression has type %a,@ but is expected to have a mutable type@]"
        print_dty dty

let dexception uc qid =
  let sl = Typing.string_list_of_qualid [] qid in
  let loc = Typing.qloc qid in
  let _, _, ty as r = specialize_exception loc sl uc in
  let ty_exn = tyapp ts_exn [] in
  if not (Denv.unify ty ty_exn) then
    errorm ~loc
      "@[this expression has type %a,@ but is expected to be an exception@]"
      print_dty ty;
  r

let dueffect env e =
  { du_reads  = e.Ptree.pe_reads;
    du_writes = e.Ptree.pe_writes;
    du_raises =
      List.map (fun id -> let ls,_,_ = dexception env.uc id in ls)
        e.Ptree.pe_raises; }

let dpost uc (q, ql) =
  let dexn (id, l) = let s, _, _ = dexception uc id in s, l in
  q, List.map dexn ql

let add_local_top env x tyv =
  { env with locals = Mstr.add x tyv env.locals }

let add_local env x ty =
  { env with locals = Mstr.add x ty env.locals; }

let rec dpurify_utype_v = function
  | DUTpure ty ->
      ty
  | DUTarrow (bl, c) ->
      dcurrying (List.map (fun (_,ty,_) -> ty) bl)
        (dpurify_utype_v c.duc_result_type)

(* user indicates whether region type variables can be instantiated *)
let rec dtype ~user env = function
  | PPTtyvar {id=x} ->
      tyvar (Typing.find_user_type_var x env.denv)
  | PPTtyapp (p, x) ->
      let loc = Typing.qloc x in
      let ts, a = Typing.specialize_tysymbol loc x (impure_uc env.uc) in
      let mt = get_mtsymbol ts in
      let np = List.length p in
      if np <> a - mt.mt_regions then
        errorm ~loc
        "@[type %a expects %d argument(s),@ but is applied to %d argument(s)@]"
          print_qualid x (a - mt.mt_regions) np;
      let tyl = List.map (dtype ~user env) p in
      let tyl = create_regions ~user mt.mt_regions @ tyl in
      tyapp ts tyl
  | PPTtuple tyl ->
      let ts = ts_tuple (List.length tyl) in
      tyapp ts (List.map (dtype ~user env) tyl)

let rec dutype_v env = function
  | Ptree.Tpure pt ->
      DUTpure (dtype ~user:true env pt)
  | Ptree.Tarrow (bl, c) ->
      let env, bl = map_fold_left dubinder env bl in
      let c = dutype_c env c in
      DUTarrow (bl, c)

and dutype_c env c =
  let ty = dutype_v env c.Ptree.pc_result_type in
  { duc_result_type = ty;
    duc_effect      = dueffect env c.Ptree.pc_effect;
    duc_pre         = c.Ptree.pc_pre;
    duc_post        = dpost env.uc c.Ptree.pc_post;
  }

and dubinder env ({id=x; id_loc=loc} as id, v) =
  let v = match v with
    | Some v -> dutype_v env v
    | None -> DUTpure (create_type_var loc)
  in
  let ty = dpurify_utype_v v in
  add_local env x ty, (id, ty, v)

let rec add_local_pat env p = match p.dp_node with
  | Denv.Pwild -> env
  | Denv.Pvar x -> add_local env x.id p.dp_ty
  | Denv.Papp (_, pl) -> List.fold_left add_local_pat env pl
  | Denv.Pas (p, x) -> add_local_pat (add_local env x.id p.dp_ty) p
  | Denv.Por (p, q) -> add_local_pat (add_local_pat env p) q

let dvariant env (l, p) =
  let relation p =
    let s, _ = Typing.specialize_psymbol p (pure_uc env.uc) in
    let loc = Typing.qloc p in
    match s.ls_args with
      | [t1; t2] when Ty.ty_equal t1 t2 ->
          s
      | _ ->
          errorm ~loc "predicate %s should be a binary relation"
            s.ls_name.id_string
  in
  l, option_map relation p

let dloop_annotation env a =
  { dloop_invariant = a.Ptree.loop_invariant;
    dloop_variant   = option_map (dvariant env) a.Ptree.loop_variant; }

(***
let is_ps_ghost e = match e.dexpr_desc with
  | DEglobal (ps, _) -> T.p_equal ps ps_ghost
  | _ -> false
***)

let rec extract_labels labs loc e = match e.Ptree.expr_desc with
  | Ptree.Enamed (Ptree.Lstr s, e) -> extract_labels (s :: labs) loc e
  | Ptree.Enamed (Ptree.Lpos p, e) -> extract_labels labs (Some p) e
  | Ptree.Ecast  (e, ty) ->
      let labs, loc, d = extract_labels labs loc e in
      labs, loc, Ptree.Ecast ({ e with Ptree.expr_desc = d }, ty)
  | e -> List.rev labs, loc, e

(* [dexpr] translates ptree into dexpr *)

let rec dexpr ~ghost ~userloc env e =
  let loc = e.Ptree.expr_loc in
  let labs, userloc, d = extract_labels [] userloc e in
  let d, ty = dexpr_desc ~ghost ~userloc env loc d in
  let loc = default_option loc userloc in
  let e = {
    dexpr_desc = d; dexpr_loc = loc; dexpr_lab = labs; dexpr_type = ty; }
  in
  (****
  match view_dty ty with
    (* if below ghost and e has ghost type, then unghost it *)
    | Denv.Tyapp (ts, [ty']) when ghost && ts_equal ts mt_ghost.mt_abstr ->
        let unghost =
          let tv = specialize_type_v ~loc (Htv.create 17) ps_unghost.p_tv in
          match tv with
            | DTarrow ([_,tyx,_], _) ->
                if not (Denv.unify ty tyx) then assert false;
                let dtv = dpurify_type_v tv in
                { dexpr_desc = DEglobal (ps_unghost, tv);
                  dexpr_loc = loc; dexpr_denv = env.denv; dexpr_type = dtv; }
            | _ ->
                assert false
        in
        { dexpr_desc = DEapply (unghost, e); dexpr_loc = e.dexpr_loc;
          dexpr_denv = env.denv; dexpr_type = ty'; }
    | _ ->
  ****)
  e

and dexpr_desc ~ghost ~userloc env loc = function
  | Ptree.Econstant (ConstInt _ as c) ->
      DEconstant c, tyapp Ty.ts_int []
  | Ptree.Econstant (ConstReal _ as c) ->
      DEconstant c, tyapp Ty.ts_real []
  | Ptree.Eident (Qident {id=x}) when Mstr.mem x env.locals ->
      (* local variable *)
      let tyv = Mstr.find x env.locals in
      DElocal (x, tyv), tyv
  | Ptree.Eident p ->
      (* global variable *)
      new_regions_vars ();
      let x = Typing.string_list_of_qualid [] p in
      let ls =
        try
          ns_find_ls (get_namespace (impure_uc env.uc)) (parameter_q x)
        with Not_found -> try
          ns_find_ls (get_namespace (impure_uc env.uc)) x
        with Not_found ->
          errorm ~loc "unbound symbol %a" print_qualid p
      in
      (*if ls_equal ls fs_at then errorm ~loc "at not allowed in programs";*)
      if ls_equal ls fs_old then errorm ~loc "old not allowed in programs";
      let ps = get_psymbol ls in
      begin match ps.ps_kind with
        | PSvar v ->
            let htv = Htv.create 17 in
            let dty = specialize_type_v ~loc ~policy:Region_glob htv v.pv_tv in
            DEglobal (ps, v.pv_tv, htv), dty
        | PSfun tv ->
            let htv = Htv.create 17 in
            let dty = specialize_type_v ~loc htv tv in
            DEglobal (ps, tv, htv), dty
        | PSlogic ->
            let tyl, ty = Denv.specialize_lsymbol ~loc ls in
            let ty = match ty with
              | Some ty -> ty
              | None -> dty_bool env.uc
            in
            DElogic ps.ps_pure, dcurrying tyl ty
      end
  | Ptree.Elazy (op, e1, e2) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      expected_type e1 (dty_bool env.uc);
      let e2 = dexpr ~ghost ~userloc env e2 in
      expected_type e2 (dty_bool env.uc);
      DElazy (op, e1, e2), dty_bool env.uc
  | Ptree.Enot e1 ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      expected_type e1 (dty_bool env.uc);
      DEnot e1, dty_bool env.uc
  | Ptree.Eapply (e1, e2) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      (* let ghost = ghost || is_ps_ghost e1 in *)
      let e2 = dexpr ~ghost ~userloc env e2 in
      let ty2 = create_type_var loc and ty = create_type_var loc in
      if not (Denv.unify e1.dexpr_type (tyapp ts_arrow [ty2; ty])) then
        errorm ~loc:e1.dexpr_loc "this expression is not a function";
      expected_type e2 ty2;
      DEapply (e1, e2), ty
  | Ptree.Efun (bl, t) ->
      let env, bl = map_fold_left dubinder env bl in
      let (_,e,_) as t = dtriple ~ghost ~userloc env t in
      let tyl = List.map (fun (_,ty,_) -> ty) bl in
      let ty = dcurrying tyl e.dexpr_type in
      DEfun (bl, t), ty
  | Ptree.Elet (x, e1, e2) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      let ty1 = e1.dexpr_type in
      let env = add_local env x.id ty1 in
      let e2 = dexpr ~ghost ~userloc env e2 in
      DElet (x, e1, e2), e2.dexpr_type
  | Ptree.Eletrec (dl, e1) ->
      let env, dl = dletrec ~ghost ~userloc env dl in
      let e1 = dexpr ~ghost ~userloc env e1 in
      DEletrec (dl, e1), e1.dexpr_type
  | Ptree.Etuple el ->
      let n = List.length el in
      let s = fs_tuple n in
      let tyl = List.map (fun _ -> create_type_var loc) el in
      let ty = tyapp (ts_tuple n) tyl in
      let uloc = default_option loc userloc in
      let create d ty = { dexpr_desc = d; dexpr_type = ty;
                          dexpr_loc = uloc; dexpr_lab = [] } in
      let apply e1 e2 ty2 =
        let e2 = dexpr ~ghost ~userloc env e2 in
        assert (Denv.unify e2.dexpr_type ty2);
        let ty = create_type_var loc in
        assert (Denv.unify e1.dexpr_type (tyapp ts_arrow [ty2; ty]));
        create (DEapply (e1, e2)) ty
      in
      let e = create (DElogic s) (dcurrying tyl ty) in
      let e = List.fold_left2 apply e el tyl in
      e.dexpr_desc, ty
  | Ptree.Erecord fl ->
      let _, cs, fl = Typing.list_fields (impure_uc env.uc) fl in
      new_regions_vars ();
      let tyl, ty = specialize_lsymbol ~loc (Htv.create 17) cs in
      let ty = of_option ty in
      let uloc = default_option loc userloc in
      let create d ty = { dexpr_desc = d; dexpr_type = ty;
                          dexpr_loc = uloc; dexpr_lab = [] } in
      let constructor d f tyf = match f with
        | Some (_, f) ->
            let f = dexpr ~ghost ~userloc env f in
            expected_type f tyf;
            let ty = create_type_var loc in
            assert (Denv.unify d.dexpr_type (tyapp ts_arrow [tyf; ty]));
            create (DEapply (d, f)) ty
        | None ->
            errorm ~loc "some record fields are missing"
      in
      let d =
        let ps = get_psymbol cs in
        create (DElogic ps.ps_pure) (dcurrying tyl ty)
      in
      let d = List.fold_left2 constructor d fl tyl in
      d.dexpr_desc, ty
  | Ptree.Eupdate (e1, fl) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      let _, cs, fl = Typing.list_fields (impure_uc env.uc) fl in
      let tyl, ty = Denv.specialize_lsymbol ~loc cs in
      let ty = of_option ty in
      expected_type e1 ty;
      let n = ref (-1) in
      let q = Queue.create () in
      (* prepare the pattern *)
      let pl = List.map2 (fun f ty -> match f with
        | Some _ ->
            { dp_node = Denv.Pwild ; dp_ty = ty }
        | None ->
            let x = incr n; "x:" ^ string_of_int !n in
            let i = { id = x ; id_lab = []; id_loc = loc } in
            Queue.add (x,ty) q;
            { dp_node = Denv.Pvar i ; dp_ty = ty }) fl tyl
      in
      let p = { dp_node = Denv.Papp (cs,pl) ; dp_ty = ty } in
      (* prepare the result *)
      new_regions_vars ();
      let tyl, ty = specialize_lsymbol ~loc (Htv.create 17) cs in
      let ty = of_option ty in
      (* unify pattern variable types with expected types *)
      let set_pat_var_ty f tyf = match f with
        | Some _ ->
            ()
        | None ->
            let _, xty as v = Queue.take q in
            assert (Denv.unify xty tyf);
            Queue.push v q
      in
      List.iter2 set_pat_var_ty fl tyl;
      let uloc = default_option loc userloc in
      let create d ty = { dexpr_desc = d; dexpr_type = ty;
                          dexpr_loc = uloc; dexpr_lab = [] } in
      let apply t f tyf = match f with
        | Some (_,e) ->
            let e = dexpr ~ghost ~userloc env e in
            expected_type e tyf;
            let ty = create_type_var loc in
            assert (Denv.unify t.dexpr_type (tyapp ts_arrow [tyf; ty]));
            create (DEapply (t, e)) ty
        | None ->
            let x, _ = Queue.take q in
            let v = create (DElocal (x, tyf)) tyf in
            let ty = create_type_var loc in
            assert (Denv.unify t.dexpr_type (tyapp ts_arrow [tyf; ty]));
            create (DEapply (t, v)) ty
      in
      let t =
        let ps = get_psymbol cs in
        create (DElogic ps.ps_pure) (dcurrying tyl ty)
      in
      let t = List.fold_left2 apply t fl tyl in
      DEmatch (e1, [p, t]), ty
  | Ptree.Eassign (e1, q, e2) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      let e2 = dexpr ~ghost ~userloc env e2 in
      let x = Typing.string_list_of_qualid [] q in
      let ls =
        try ns_find_ls (get_namespace (impure_uc env.uc)) x
        with Not_found -> errorm ~loc "unbound record field %a" print_qualid q
      in
      new_regions_vars ();
      begin match specialize_lsymbol ~loc (Htv.create 17) ls with
        | [ty1], Some ty2 ->
            expected_type e1 ty1;
            expected_type e2 ty2
        | _ ->
            assert false
      end;
      begin match Typing.is_projection (impure_uc env.uc) ls with
        | Some (ts, _, i)  ->
            let mt = get_mtsymbol ts in
            let j =
              try mutable_field mt.mt_effect i
              with Not_found -> errorm ~loc "not a mutable field"
            in
            DEassign (e1, ls, j, e2), dty_unit
        | None ->
            errorm ~loc "unbound record field %a" print_qualid q
      end
  | Ptree.Esequence (e1, e2) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      expected_type e1 dty_unit;
      let e2 = dexpr ~ghost ~userloc env e2 in
      DEsequence (e1, e2), e2.dexpr_type
  | Ptree.Eif (e1, e2, e3) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      expected_type e1 (dty_bool env.uc);
      let e2 = dexpr ~ghost ~userloc env e2 in
      let e3 = dexpr ~ghost ~userloc env e3 in
      expected_type e3 e2.dexpr_type;
      DEif (e1, e2, e3), e2.dexpr_type
  | Ptree.Eloop (a, e1) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      expected_type e1 dty_unit;
      DEloop (dloop_annotation env a, e1), dty_unit
  | Ptree.Ematch (e1, bl) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      let ty1 = e1.dexpr_type in
      let ty = create_type_var loc in (* the type of all branches *)
      let branch (p, e) =
        let denv, p = Typing.dpat_list (impure_uc env.uc) env.denv ty1 p in
        let env = { env with denv = denv } in
        let env = add_local_pat env p in
        let e = dexpr ~ghost ~userloc env e in
        expected_type e ty;
        p, e
      in
      let bl = List.map branch bl in
      DEmatch (e1, bl), ty
  | Ptree.Eabsurd ->
      DEabsurd, create_type_var loc
  | Ptree.Eraise (qid, e) ->
      let ls, tyl, _ = dexception env.uc qid in
      let e = match e, tyl with
        | None, [] ->
            None
        | Some _, [] ->
            errorm ~loc "expection %a has no argument" print_qualid qid
        | None, [ty] ->
            errorm ~loc "exception %a is expecting an argument of type %a"
              print_qualid qid print_dty ty;
        | Some e, [ty] ->
            let e = dexpr ~ghost ~userloc env e in
            expected_type e ty;
            Some e
        | _ ->
            assert false
      in
      DEraise (ls, e), create_type_var loc
  | Ptree.Etry (e1, hl) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      let handler (id, x, h) =
        let ls, tyl, _ = dexception env.uc id in
        let x, env = match x, tyl with
          | Some _, [] ->
              errorm ~loc "expection %a has no argument" print_qualid id
          | None, [] ->
              None, env
          | None, [ty] ->
              errorm ~loc "exception %a is expecting an argument of type %a"
                print_qualid id print_dty ty;
          | Some x, [ty] ->
              Some x.id, add_local env x.id ty
          | _ ->
              assert false
        in
        let h = dexpr ~ghost ~userloc env h in
        expected_type h e1.dexpr_type;
        (ls, x, h)
      in
      DEtry (e1, List.map handler hl), e1.dexpr_type
  | Ptree.Efor (x, e1, d, e2, inv, e3) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      expected_type e1 dty_int;
      let e2 = dexpr ~ghost ~userloc env e2 in
      expected_type e2 dty_int;
      let env = add_local env x.id dty_int in
      let e3 = dexpr ~ghost ~userloc env e3 in
      expected_type e3 dty_unit;
      DEfor (x, e1, d, e2, inv, e3), dty_unit
  | Ptree.Eassert (k, le) ->
      DEassert (k, le), dty_unit
  | Ptree.Emark ({id=s}, e1) ->
      if Typing.mem_var s env.denv then
        errorm ~loc "clash with previous mark %s" s;
      let env = { env with denv = add_pure_var s dty_mark env.denv } in
      let e1 = dexpr ~ghost ~userloc env e1 in
      DEmark (s, e1), e1.dexpr_type
  | Ptree.Ecast (e1, ty) ->
      let e1 = dexpr ~ghost ~userloc env e1 in
      let ty = dtype ~user:false env ty in
      expected_type e1 ty;
      e1.dexpr_desc, ty
  | Ptree.Eany c ->
      let c = dutype_c env c in
      DEany c, dpurify_utype_v c.duc_result_type
  | Ptree.Enamed _ ->
      assert false

and dletrec ~ghost ~userloc env dl =
  (* add all functions into environment *)
  let add_one env (id, bl, var, t) =
    let ty = create_type_var id.id_loc in
    let env = add_local_top env id.id ty in
    env, ((id, ty), bl, var, t)
  in
  let env, dl = map_fold_left add_one env dl in
  (* then type-check all of them and unify *)
  let type_one ((id, tyres), bl, v, t) =
    let env, bl = map_fold_left dubinder env bl in
    let v = option_map (dvariant env) v in
    let (_,e,_) as t = dtriple ~ghost ~userloc env t in
    let tyl = List.map (fun (_,ty,_) -> ty) bl in
    let ty = dcurrying tyl e.dexpr_type in
    if not (Denv.unify ty tyres) then
      errorm ~loc:id.id_loc
        "@[this expression has type %a,@ but is expected to have type %a@]"
        print_dty ty print_dty tyres;
    ((id, tyres), bl, v, t)
  in
  env, List.map type_one dl

and dtriple ~ghost ~userloc env (p, e, q) =
  let e = dexpr ~ghost ~userloc env e in
  let q = dpost env.uc q in
  (p, e, q)

(*** regions tables ********************************************************)

let region_types = Hts.create 17 (* ts -> int -> ty *)

let declare_region_type ts i ty =
  let h =
    try
      Hts.find region_types ts
    with Not_found ->
      let h = Hashtbl.create 17 in Hts.add region_types ts h; h
  in
  Hashtbl.add h i ty

let region_type ts i =
  (* eprintf "region_type: ts=%a i=%d@." Pretty.print_ts ts i; *)
  (* let mt = get_mtsymbol ts in *)
  (* eprintf "%a@." print_mt_symbol mt; *)
  Hashtbl.find (Hts.find region_types ts) i

let regions_tyapp ts nregions tyl =
  let tymatch s tv ty = Ty.ty_match s (ty_var tv) ty in
  let s = List.fold_left2 tymatch Mtv.empty ts.ts_args tyl in
  let mk i ty = match ty.ty_node with
    | Ty.Tyvar r -> R.create r (ty_inst s (region_type ts i))
    | Ty.Tyapp _ -> assert false
  in
  list_mapi mk (Util.prefix nregions tyl)

(* phase 2: remove destructive types and type annotations *****************)

(* check
   1. that variables occurring in 'old' and 'at' are not local variables
   2. that 'old' is used only when old is true
*)
let check_at_fmla ?(old=false) loc f0 =
  let v = ref None in
  let rec check f = match f.t_node with
    | Term.Tapp (ls, _) when ls_equal ls fs_old && not old ->
        errorm ~loc "use of `old' not allowed here"
    | Term.Tapp (ls, _) when ls_equal ls fs_at || ls_equal ls fs_old ->
        let d = Mvs.set_diff f.t_vars f0.t_vars in
        Mvs.is_empty d || (v := Some (fst (Mvs.choose d)); false)
    | _ ->
        t_all check f
  in
  if not (check f0) then
    errorm ~loc "locally bound variable %a under `at'" print_vs (of_option !v)

let dterm env l = Typing.dterm ~localize:(Some None) env l
let dfmla env l = Typing.dfmla ~localize:(Some None) env l

type ienv = {
  i_uc      : uc;
  i_denv    : Typing.denv;
  i_impures : ivsymbol Mstr.t;
  i_effects : vsymbol Mstr.t;
  i_pures   : vsymbol Mstr.t;
}

let create_ivsymbol id ty =
  let vs = create_vsymbol id ty in
  let vse = create_vsymbol id (effectify ty) in
  let vsp =
    let ty' = purify ty in if ty_equal ty ty' then vs else create_vsymbol id ty'
  in
  { i_impure = vs; i_effect = vse; i_pure = vsp }

let rec dty_of_ty denv ty = match ty.ty_node with
  | Ty.Tyvar v ->
      Denv.tyvar (Typing.find_user_type_var v.tv_name.id_string denv)
  | Ty.Tyapp (ts, tyl) ->
      Denv.tyapp ts (List.map (dty_of_ty denv) tyl)

let iadd_local env x ty =
  let v = create_ivsymbol x ty in
  let s = v.i_impure.vs_name.id_string in
  let env = { env with
    i_denv =
      (let dty = dty_of_ty env.i_denv v.i_pure.vs_ty in
       add_pure_var s dty env.i_denv);
    i_impures = Mstr.add s v env.i_impures;
    i_effects = Mstr.add s v.i_effect env.i_effects;
    i_pures = Mstr.add s v.i_pure env.i_pures; }
  in
  env, v

let rec type_effect_term env t =
  let loc = t.pp_loc in
  match t.pp_desc with
  | PPvar (Qident x) when Mstr.mem x.id env.i_effects ->
      let v = Mstr.find x.id env.i_effects in
      v.vs_ty
  | PPvar q ->
      let x = Typing.string_list_of_qualid [] q in
      begin try
        let ls = ns_find_ls (get_namespace (effect_uc env.i_uc)) x in
        of_option ls.ls_value
      with Not_found ->
        errorm ~loc "unbound symbol %a" print_qualid q
      end
(***
  | _ ->
      let uc = effect_uc env.i_uc in
      let t = Typing.type_term uc env.i_denv env.i_effects t in
      begin match t.t_ty with
        | Some ty -> ty
        | None -> errorm ~loc "term expected"
      end
***)
  | _ ->
      errorm ~loc "unsupported effect syntax"

let iuregion env ({ pp_loc = loc; pp_desc = d } as t) = match d with
  | PPapp (f, [t]) ->
      let th = effect_uc env.i_uc in
      let ls, _, _ = Typing.specialize_lsymbol f th in
      begin match Typing.is_projection th ls with
        | Some (ts, _, i) ->
            let j =
              try
                mutable_field ts i
              with Not_found ->
                errorm ~loc "not a mutable record field"
            in
            let tloc = t.pp_loc in
            let ty = type_effect_term env t in
            begin match ty.ty_node with
              | Ty.Tyapp (ts', tyl) when ts_equal ts ts' ->
                  let mt = get_mtsymbol ts in
                  let r = regions_tyapp ts mt.mt_regions tyl in
                  List.nth r j
              | _ ->
                  errorm ~loc:tloc
            "@[this expression has type %a,@ but is expected to have type %a@]"
                    Pretty.print_ty ty Pretty.print_ts ts
            end
        | None ->
            errorm ~loc "not a record field"
      end
  | _ ->
      let ty = type_effect_term env t in
      let not_mutable () = errorm ~loc
      "@[this expression has type %a,@ but is expected to have a mutable type@]"
        Pretty.print_ty ty
      in
      begin match ty.ty_node with
        | Ty.Tyapp (ts, tyl)  ->
            let mt = get_mtsymbol ts in
            let n = mt.mt_regions in
            if n = 0 then not_mutable ();
            if n > 1 then errorm ~loc
              "ambiguous effect term (more than one region)";
            let r = regions_tyapp ts mt.mt_regions tyl in
            List.nth r 0
        | _ ->
            not_mutable ()
      end

let iueffect env e = {
  ie_reads  = List.map (iuregion env) e.du_reads;
  ie_writes = List.map (iuregion env) e.du_writes;
  ie_raises = e.du_raises;
}

let pre env = Denv.fmla env.i_pures

let post env ((ty, f), ql) =
  let env = env.i_pures in
  let exn (ls, (ty, f)) =
    let v, env = match ty with
      | None ->
          None, env
      | Some ty ->
          let ty = Denv.ty_of_dty ty in
          let v_result = create_vsymbol (id_fresh id_result) ty in
          Some v_result, Mstr.add id_result v_result env
    in
    ls, (v, Denv.fmla env f)
  in
  let ty = Denv.ty_of_dty ty in
  let v_result = create_vsymbol (id_fresh id_result) ty in
  let env = Mstr.add id_result v_result env in
  (v_result, Denv.fmla env f), List.map exn ql

let iterm env l =
  let t = dterm (pure_uc env.i_uc) env.i_denv l in
  let t = Denv.term env.i_pures t in
  check_at_fmla l.pp_loc t;
  t

(* FIXME: ensure that symbol comes from theory int.Int *)
let find_int_ls ~loc env s =
  try find_ls ~pure:true env s
  with Not_found -> errorm ~loc "cannot find symbol %s; please import int.Int" s

let variant_rel_int ~loc env =
  Vint (find_int_ls ~loc env "infix <=", find_int_ls ~loc env "infix <")

(* TODO: should we admit an instance of a polymorphic order relation? *)
let ivariant env (t, ps) =
  let loc = t.pp_loc in
  let t = iterm env t in
  match ps with
    | None ->
        if not (Ty.ty_equal ty_int (t_type t)) then
          errorm ~loc "variant should have type int";
        t, variant_rel_int ~loc env.i_uc
    | Some ({ ls_args = [t1; _] } as ps) when Ty.ty_equal t1 (t_type t) ->
        t, Vuser ps
    | Some { ls_args = [t1; _] } ->
        errorm ~loc "@[variant has type %a, but is expected to have type %a@]"
          Pretty.print_ty (t_type t) Pretty.print_ty t1
    | _ ->
        assert false

(* replace every occurrence of [old(t)] with [at(t,'old)] *)
let rec remove_old f = match f.t_node with
  | Term.Tapp (ls, [t]) when ls_equal ls fs_old ->
      t_app fs_at [remove_old t; t_var vs_old] f.t_ty
  | _ ->
      t_map remove_old f

let ifmla ?(old=false) env l =
  let f = dfmla (pure_uc env.i_uc) env.i_denv l in
  let f = Denv.fmla env.i_pures f in
  check_at_fmla ~old l.pp_loc f;
  if (old = true) then remove_old f else f

let id_result loc = id_user id_result loc

let iupost env ty (q, ql) =
  let dexn (s, l) =
    let loc = l.pp_loc in
    let v, env = match s.ls_args with
      | [] ->
              None, env
      | [ty] ->
          let env, v = iadd_local env (id_result loc) ty in
          Some v.i_pure, env
      | _ -> assert false
    in
    let f = ifmla ~old:true env l in
    s, (v, f)
  in
  let loc = q.pp_loc in
  let env, v = iadd_local env (id_result loc) ty in
  let q = ifmla ~old:true env q in
  (v.i_pure, q), List.map dexn ql

let rec purify_itype_v  = function
  | ITpure ty ->
      ty
  | ITarrow (bl, c) ->
      make_arrow_type
        (List.map (fun (v,_) -> v.i_impure.vs_ty) bl)
        (purify_itype_v c.ic_result_type)

let rec iutype_v env = function
  | DUTpure ty ->
      ITpure (Denv.ty_of_dty ty)
  | DUTarrow (bl, c) ->
      let env, bl = map_fold_left iubinder env bl in
      ITarrow (bl, iutype_c env c)

and iutype_c env c =
  let tyv = iutype_v env c.duc_result_type in
  let ty = purify_itype_v tyv in
  { ic_result_type = tyv;
    ic_effect      = iueffect env c.duc_effect;
    ic_pre         = ifmla env c.duc_pre;
    ic_post        = iupost env ty c.duc_post; }

and iubinder env (x, ty, tyv) =
  let tyv = iutype_v env tyv in
  let ty = Denv.ty_of_dty ty in
  let env, v = iadd_local env (id_user x.id x.id_loc) ty in
  env, (v, tyv)

let mk_iexpr loc ty d =
  { iexpr_desc = d; iexpr_loc = loc; iexpr_lab = []; iexpr_type = ty }

(* apply ls to a list of expressions, introducing let's if necessary

  ls [e1; e2; ...; en]
->
  let x1 = e1 in
  let x2 = e2 in
  ...
  let xn = en in
  ls(x1,x2,...,xn)
*)
let make_logic_app loc ty ls el =
  let rec make lvars gvars args = function
    | [] ->
        begin match ls.ls_value with
          | Some _ ->
              IElogic (fs_app ls (List.rev args) (purify ty), lvars, gvars)
          | None ->
              IElogic (ps_app ls (List.rev args), lvars, gvars)
        end
    | ({ iexpr_desc = IElogic (t,lvt,gvt) }, _, _) :: r when t.t_ty <> None ->
        make (Svs.union lvars lvt) (Spv.union gvars gvt) (t :: args) r
    | ({ iexpr_desc = IElocal v }, _, _) :: r ->
        make (Svs.add v.i_impure lvars) gvars (t_var v.i_pure :: args) r
    | ({ iexpr_desc = IEglobal ({ ps_kind = PSvar v }, _) }, _, _) :: r ->
        make lvars (Spv.add v gvars) (t_var v.pv_pure :: args) r
    | (e, _, _) :: r ->
        let v = create_ivsymbol (id_user "x" loc) e.iexpr_type in
        let lvars = Svs.add v.i_impure lvars in
        let d = mk_iexpr loc ty (make lvars gvars (t_var v.i_pure::args) r) in
        IElet (v, e, d)
  in
  make Svs.empty Spv.empty [] el

(* same thing, but for an abritrary expression f (not an application)
   f [e1; e2; ...; en]
-> let x1 = e1 in ... let xn = en in (...((f x1) x2)... xn)
*)
let make_app loc ty f el =
  let mk_iexpr loc lab ty d =
    let ie = mk_iexpr loc ty d in
    { ie with iexpr_lab = lab }
  in
  let rec make k = function
    | [] ->
        k f
    | ({ iexpr_type = ty } as e, tye, lab) :: r when is_mutable_ty ty ->
        begin match e.iexpr_desc with
          | IElocal v ->
              make (fun f -> mk_iexpr loc lab tye (IEapply_var (k f, v))) r
          | IEglobal ({ ps_kind = PSvar v }, _) ->
              make (fun f -> mk_iexpr loc lab tye (IEapply_glob (k f, v))) r
          | IEglobal ({ ps_kind = PSfun _ }, _) ->
              errorm ~loc "higher-order programs not yet implemented"
          | _ ->
              let v = create_ivsymbol (id_user "x" loc) e.iexpr_type in
              let d =
                make (fun f -> mk_iexpr loc lab tye (IEapply_var (k f, v))) r
              in
              mk_iexpr loc [] ty (IElet (v, e, d))
        end
    | ({ iexpr_desc = IElocal v }, tye, lab) :: r ->
        make (fun f -> mk_iexpr loc lab tye (IEapply (k f, v))) r
    | (e, tye, lab) :: r ->
        let v = create_ivsymbol (id_user "x" loc) e.iexpr_type in
        let d = make (fun f -> mk_iexpr loc lab tye (IEapply (k f, v))) r in
        mk_iexpr loc [] ty (IElet (v, e, d))
  in
  make (fun f -> f) el

let ipattern env p =
  let memo = Hvs.create 17 in
  let add1 env vs =
    try
      env, Hvs.find memo vs
    with Not_found ->
      (* TODO: incorrect when vs is not pure ? *)
      let _, v as r = iadd_local env (id_clone vs.vs_name) vs.vs_ty in
      Hvs.add memo vs v;
      r
  in
  let rec ipattern env p =
    let env, n = ipattern_node env p.pat_node in
    env, { ipat_pat = p; ipat_node = n }
  and ipattern_node env = function
    | Term.Pwild ->
        env, IPwild
    | Term.Papp (ls, pl) ->
        let env, pl = map_fold_left ipattern env pl in
        env, IPapp (ls, pl)
    | Term.Por (p1, p2) ->
        let env, p1 = ipattern env p1 in
        let _  , p2 = ipattern env p2 in
        env, IPor (p1, p2)
    | Term.Pvar vs ->
        let env, v = add1 env vs in
        env, IPvar v
    | Term.Pas (p, vs) ->
        let env, v = add1 env vs in
        let env, p = ipattern env p in
        env, IPas (p, v)
  in
  ipattern env p

(* pretty-printing (for debugging) *)

open Pp
open Pretty

let print_iregion = R.print

let rec print_iexpr fmt e = match e.iexpr_desc with
  | IElogic (t, _, _) ->
      print_term fmt t
  | IElocal v ->
      fprintf fmt "<local %a>" print_vs v.i_impure
  | IEglobal ({ ps_kind = PSvar v }, _) ->
      fprintf fmt "<global var %a>" print_vs v.pv_effect
  | IEglobal ({ ps_kind = PSfun v } as ps, _) ->
      fprintf fmt "<global %a : %a>" print_ls ps.ps_effect T.print_type_v v
  | IEapply (e, v) ->
      fprintf fmt "@[((%a) %a)@]" print_iexpr e print_vs v.i_impure
  | IEapply_var (e, v) ->
      fprintf fmt "@[((%a) <var %a>)@]" print_iexpr e print_vs v.i_impure
  | IEapply_glob (e, v) ->
      fprintf fmt "@[((%a) <glob %a>)@]" print_iexpr e print_vs v.pv_effect
  | IEfun (_, (_,e,_)) ->
      fprintf fmt "@[fun _ ->@ %a@]" print_iexpr e
  | IElet (v, e1, e2) ->
      fprintf fmt "@[let %a = %a in@ %a@]" print_vs v.i_impure
        print_iexpr e1 print_iexpr e2
  | IEif (e1, e2, e3) ->
      fprintf fmt "@[if %a then %a else %a@]"
        print_iexpr e1 print_iexpr e2 print_iexpr e3
  | _ ->
      fprintf fmt "<other>"

let mtv_of_htv htv =
  Htv.fold
    (fun tv tvar m ->
       let ty = ty_of_dty (tyvar tvar) in
       Mtv.add tv ty m)
    htv Mtv.empty

(* push the labels under the IElet's introduced by iexpr, make_app,
   and make_logic_app (except for DElet and DEsequence which are
   real, user-written let's) *)

let drown_lab d e =
  let rec drown e = match e.iexpr_desc with
    | IElet (v,e1,e2) ->
        { e with iexpr_desc = IElet (v, e1, drown e2) }
    | _ ->
        { e with iexpr_lab  = d.dexpr_lab } in
  match d.dexpr_desc with
    | DElet _ | DEsequence _ ->
        { e with iexpr_lab  = d.dexpr_lab }
    | _ ->
        drown e

(* [iexpr] translates dexpr into iexpr
   [env : vsymbol Mstr.t] maps strings to vsymbols for local variables *)

let rec iexpr env e =
  let ty = Denv.ty_of_dty e.dexpr_type in
  let d = iexpr_desc env e.dexpr_loc ty e.dexpr_desc in
  drown_lab e { iexpr_desc = d; iexpr_type = ty;
                iexpr_loc = e.dexpr_loc; iexpr_lab = [] }

and iexpr_desc env loc ty = function
  | DEconstant c ->
      IElogic (t_const c, Svs.empty, Spv.empty)
  | DElocal (x, _) ->
      IElocal (Mstr.find x env.i_impures)
  | DEglobal (s, tv, htv) ->
      let ts = mtv_of_htv htv in
      let tv = subst_type_v ts Mvs.empty tv in
      IEglobal (s, tv)
  | DElogic ls ->
      begin match ls.ls_args, ls.ls_value with
        | [], Some _ ->
            IElogic (fs_app ls [] (purify ty), Svs.empty, Spv.empty)
        | [], None ->
            IElogic (ps_app ls [], Svs.empty, Spv.empty)
        | al, _ ->
            errorm ~loc "function symbol %s is expecting %d arguments"
              ls.ls_name.id_string (List.length al)
      end
  | DEapply (e1, e2) ->
      let f, args = decompose_app env e1 [iexpr env e2, ty, []] in
      begin match f.dexpr_desc with
        | DElogic ls ->
            let n = List.length ls.ls_args in
            if List.length args <> n then
              errorm ~loc "function symbol %s is expecting %d arguments"
                ls.ls_name.id_string n;
            make_logic_app loc ty ls args
        | _ ->
            let f = iexpr env f in
            let e = make_app loc ty f args in
            e.iexpr_desc
      end
  | DEfun (bl, e1) ->
      let env, bl = map_fold_left iubinder env bl in
      IEfun (bl, itriple env e1)
  | DElet (x, e1, e2) ->
      let e1 = iexpr env e1 in
      let env, v = iadd_local env (id_user x.id x.id_loc) e1.iexpr_type in
      IElet (v, e1, iexpr env e2)
  | DEletrec (dl, e1) ->
      let env, dl = iletrec env dl in
      let e1 = iexpr env e1 in
      IEletrec (dl, e1)
  | DEassign (e1, ls, j, e2) ->
      (* e1.f <- e2 is syntactic sugar for
         let x1 = e1 in let x2 = e2 in any {} writes f { x1.f = x2 } *)
      let e1 = iexpr env e1 in
      let e2 = iexpr env e2 in
      let x1 = create_ivsymbol (id_fresh "x") e1.iexpr_type in
      let x2 = create_ivsymbol (id_fresh "x") e2.iexpr_type in
      let r = match e1.iexpr_type.ty_node with
        | Ty.Tyapp (ts, tyl) ->
            let mt = get_mtsymbol ts in
            let r = regions_tyapp mt.mt_effect mt.mt_regions tyl in
            List.nth r j
        | Ty.Tyvar _ ->
            assert false
      in
      let ef = { ie_reads = []; ie_writes = [r]; ie_raises = [] } in
      let q =
        let ls = (get_psymbol ls).ps_pure in
        t_equ (fs_app ls [t_var x1.i_pure] x2.i_pure.vs_ty) (t_var x2.i_pure)
      in
      let q = (create_vsymbol (id_fresh "result") ty, q), [] in
      let c = {
        ic_result_type = ITpure ty; ic_effect = ef;
        ic_pre = t_true; ic_post = q }
      in
      IElet (x1, e1, mk_iexpr loc ty (
      IElet (x2, e2, mk_iexpr loc ty (
      IEany c))))
  | DEsequence (e1, e2) ->
      let vs = create_ivsymbol (id_fresh "_") (ty_app (ts_tuple 0) []) in
      IElet (vs, iexpr env e1, iexpr env e2)
  | DEif (e1, e2, e3) ->
      IEif (iexpr env e1, iexpr env e2, iexpr env e3)
  | DEloop (la, e1) ->
      let la =
        { loop_invariant =
            option_map (ifmla env) la.dloop_invariant;
          loop_variant   =
            option_map (ivariant env) la.dloop_variant; }
      in
      IEloop (la, iexpr env e1)
  | DElazy (op, e1, e2) ->
      IElazy (op, iexpr env e1, iexpr env e2)
  | DEnot e1 ->
      IEnot (iexpr env e1)
  | DEmatch (e1, bl) ->
      let e1 = iexpr env e1 in
      let branch (p, e) =
        let envi = Mstr.map (fun v -> v.i_impure) env.i_impures in
        let _, p = Denv.pattern envi p in
        let env, p = ipattern env p in
        (p, iexpr env e)
      in
      let bl = List.map branch bl in
      let v = create_ivsymbol (id_user "x" loc) e1.iexpr_type in
      IElet (v, e1, mk_iexpr loc ty (IEmatch (v, bl)))
  | DEabsurd ->
      IEabsurd
  | DEraise (ls, e) ->
      IEraise (ls, option_map (iexpr env) e)
  | DEtry (e, hl) ->
      let handler (ls, x, h) =
        let x, env = match x with
          | Some x ->
              let ty = match ls.ls_args with [ty] -> ty | _ -> assert false in
              let env, v = iadd_local env (id_user x loc) ty in
              Some v, env
          | None ->
              None, env
        in
        (ls, x, iexpr env h)
      in
      IEtry (iexpr env e, List.map handler hl)
  | DEfor (x, e1, d, e2, inv, e3) ->
      List.iter
        (fun s -> ignore (find_int_ls ~loc env.i_uc s)) ["infix <"; "infix +"];
      let e1 = iexpr env e1 in
      let e2 = iexpr env e2 in
      let env, vx = iadd_local env (id_user x.id x.id_loc) e1.iexpr_type in
      let inv = option_map (ifmla env) inv in
      let e3 = iexpr env e3 in
      let v1 = create_ivsymbol (id_user "for_start" loc) e1.iexpr_type in
      let v2 = create_ivsymbol (id_user "for_end" loc)   e2.iexpr_type in
      IElet (v1, e1, mk_iexpr loc ty (
      IElet (v2, e2, mk_iexpr loc ty (
      IEfor (vx, v1, d, v2, inv, e3)))))
  | DEassert (k, f) ->
      let f = ifmla env f in
      IEassert (k, f)
  | DEmark (s, e1) ->
      let env, v = iadd_local env (id_fresh s) ty_mark in
      IEmark (v.i_impure, iexpr env e1)
  | DEany c ->
      let c = iutype_c env c in
      IEany c

and decompose_app env e args = match e.dexpr_desc with
  | DEapply (e1, e2) ->
      let lab = e.dexpr_lab in
      let ty = Denv.ty_of_dty e.dexpr_type in
      decompose_app env e1 ((iexpr env e2, ty, lab) :: args)
  | _ ->
      e, args

and iletrec env dl =
  (* add all functions into env, and compute local env *)
  let step1 env ((x, dty), bl, var, t) =
    let ty = Denv.ty_of_dty dty in
    let env, v = iadd_local env (id_user x.id x.id_loc) ty in
    env, (v, bl, var, t)
  in
  let env, dl = map_fold_left step1 env dl in
  (* then translate variants and bodies *)
  let step2 (v, bl, var, (_,_,_ as t)) =
    let env, bl = map_fold_left iubinder env bl in
    let var = option_map (ivariant env) var in
    let t = itriple env t in
    let var, t = match var with
      | None ->
          None, t
      | Some (phi, r) ->
          let p, e, q = t in
          let phi0 = create_ivsymbol (id_fresh "variant") (t_type phi) in
          let e_phi = {
            iexpr_desc = IElogic (phi, Svs.empty, Spv.empty);
                     (* FIXME: vars(phi) *)
            iexpr_type = t_type phi;
            iexpr_lab = [];
            iexpr_loc = e.iexpr_loc }
          in
          let e = { e with iexpr_desc = IElet (phi0, e_phi, e) } in
          Some (phi0, phi, r), (p, e, q)
    in
    (v, bl, var, t)
  in
  let dl = List.map step2 dl in
  (* finally, check variants are all absent or all present and consistent *)
  let error e =
    errorm ~loc:e.iexpr_loc "variants must be all present or all absent"
  in
  begin match dl with
    | [] ->
        assert false
    | (_, _, None, _) :: r ->
        let check_no_variant (_,_,var,(_,e,_)) = if var <> None then error e in
        List.iter check_no_variant r
    | (_, _, Some (_, _, ps), _) :: r ->
        let r_equal r1 r2 = match r1, r2 with
          | Vint _, Vint _ -> true
          | Vuser ls1, Vuser ls2 -> ls_equal ls1 ls2
          | _ -> false
        in
        let check_variant (_,_,var,(_,e,_)) = match var with
          | None -> error e
          | Some (_, _, ps') -> if not (r_equal ps ps') then
              errorm ~loc:e.iexpr_loc
                "variants must share the same order relation"
        in
        List.iter check_variant r
  end;
  env, dl

and itriple env (p, e, q) =
  let p = ifmla env p in
  let e = iexpr env e in
  let ty = e.iexpr_type in
  let q = iupost env ty q in
  (p, e, q)

(* phase 3: effect inference **********)

let rec ty_effect ef ty = match ty.ty_node with
  | Ty.Tyvar _ ->
      ef
  | Ty.Tyapp (ts, _) when ts_equal ts ts_arrow ->
      ef
  | Ty.Tyapp (ts, tyl) ->
      let mt = get_mtsymbol ts in
      let rl = regions_tyapp ts mt.mt_regions tyl in
      let ef = List.fold_right Sreg.add rl ef in
      List.fold_left ty_effect ef (Util.chop mt.mt_regions tyl)

let globals = Hls.create 17

let declare_global ls pv =
  Pgm_wp.declare_global_regions pv;
  Hls.add globals ls pv

let rec term_effect ef t = match t.t_node with
  | Term.Tapp (ls, []) when Hls.mem globals ls ->
      let pv = Hls.find globals ls in
      E.add_var pv ef, t_var pv.pv_pure
  | _ ->
      t_map_fold term_effect ef t

let post_effect ef ((v, q), ql) =
  let exn_effect ef (e, (x, q)) =
    let ef, q = term_effect ef q in ef, (e, (x, q))
  in
  let ef, q = term_effect ef q in
  let ef, ql = map_fold_left exn_effect ef ql in
  ef, ((v, q), ql)

let effect e =
  let reads ef r = E.add_read r ef in
  let writes ef r = E.add_write r ef in
  let raises ef l = E.add_raise l ef in
  let ef = List.fold_left reads E.empty e.ie_reads in
  let ef = List.fold_left writes ef e.ie_writes in
  List.fold_left raises ef e.ie_raises

let create_pvsymbol id v ~effect ~pure =
  let regions = ty_effect Sreg.empty effect.vs_ty in
  create_pvsymbol id v ~effect ~pure ~regions

let create_pvsymbol_i i v =
  create_pvsymbol (id_clone i.i_impure.vs_name)
    ~effect:i.i_effect ~pure:i.i_pure v

let create_pvsymbol_v id v =
  create_pvsymbol id v
    ~effect:(create_vsymbol id (trans_type_v ~effect:true v))
    ~pure:  (create_vsymbol id (trans_type_v ~pure:  true v))

let add_local env i v =
  let vs = create_pvsymbol_i i v in
  Mvs.add i.i_impure vs env, vs

let rec type_v env = function
  | ITpure ty ->
      tpure ty
  | ITarrow (bl, c) ->
      let env, bl = add_binders env bl in
      tarrow bl (type_c env c)

and type_c env c =
  let ef = effect c.ic_effect in
  let ef, p = term_effect ef c.ic_pre in
  let ef, q = post_effect ef c.ic_post in
  (* saturate effect with exceptions appearing in q *)
  let ef = List.fold_left (fun ef (e, _) -> E.add_raise e ef) ef (snd q) in
  { c_result_type = type_v env c.ic_result_type;
    c_effect      = ef;
    c_pre         = p;
    c_post        = q; }

and add_binders env bl =
  map_fold_left add_binder env bl

and add_binder env (i, v) =
  let v = type_v env v in
  let env, vs = add_local env i v in
  env, vs

let rec pattern env p =
  let ty = purify p.ipat_pat.pat_ty in
  let env, (lp, n) = pattern_node env ty p.ipat_node in
  env, { ppat_pat = lp; ppat_node = n }

and pattern_node env ty p =
  let add1 env i = add_local env i (tpure i.i_impure.vs_ty) in
  match p with
  | IPwild ->
      env, (pat_wild ty, Pwild)
  | IPapp (ls, pl) ->
      let ls = (get_psymbol ls).ps_pure in (* impure -> pure *)
      let env, pl = map_fold_left pattern env pl in
      let lpl = List.map (fun p -> p.ppat_pat) pl in
      env, (pat_app ls lpl ty, Papp (ls, pl))
  | IPor (p1, p2) ->
      let env, p1 = pattern env p1 in
      let _  , p2 = pattern env p2 in
      env, (pat_or p1.ppat_pat p2.ppat_pat, Por (p1, p2))
  | IPvar vs ->
      let env, v = add1 env vs in
      env, (pat_var v.pv_pure, Pvar v)
  | IPas (p, vs) ->
      let env, v = add1 env vs in
      let env, p = pattern env p in
      env, (pat_as p.ppat_pat v.pv_pure, Pas (p, v))

let make_apply loc e1 ty c =
  let x = create_pvsymbol_v (id_fresh "f") (tpure e1.expr_type) in
  let v = c.c_result_type and ef = c.c_effect in
  let any_c = { expr_desc = Eany c; expr_type = ty; expr_lab = [];
                expr_type_v = v; expr_effect = ef; expr_loc = loc } in
  Elet (x, e1, any_c), v, ef

let exn_check = ref true
let without_exn_check f x =
  if !exn_check then begin
    exn_check := false;
    try let y = f x in exn_check := true; y
    with e -> exn_check := true; raise e
  end else
    f x

(*s Pure expressions. Used in [Slazy_and] and [Slazy_or] to decide
    whether to use [strict_bool_and_] and [strict_bool_or_] or not. *)

let rec is_pure_expr e =
  E.no_side_effect e.expr_effect &&
  match e.expr_desc with
  | Elocal _ | Elogic _ -> true
  | Eif (e1, e2, e3) -> is_pure_expr e1 && is_pure_expr e2 && is_pure_expr e3
  | Elet (_, e1, e2) -> is_pure_expr e1 && is_pure_expr e2
  | Emark (_, e1) -> is_pure_expr e1
  | Eany c -> E.no_side_effect c.c_effect
  | Eassert _ | Etry _ | Efor _ | Eraise _ | Ematch _
  | Eloop _ | Eletrec _ | Efun _
  | Eglobal _ | Eabsurd -> false (* TODO: improve *)

let mk_expr ?(lab=[]) loc ty ef d =
  { expr_desc = d; expr_type = ty; expr_type_v = tpure ty;
    expr_effect = ef; expr_lab = lab; expr_loc = loc }

let mk_simple_expr loc ty d = mk_expr loc ty E.empty d

let mk_bool_constant loc gl ls =
  let ty = ty_app (find_ts ~pure:true gl "bool") [] in
  { expr_desc = Elogic (fs_app ls [] ty);
    expr_type = ty; expr_type_v = tpure ty;
    expr_effect = E.empty; expr_lab = []; expr_loc = loc }

let mk_false loc gl =
  mk_bool_constant loc gl (find_ls ~pure:true gl "False")
let mk_true  loc gl =
  mk_bool_constant loc gl (find_ls ~pure:true gl "True")

(* Saturation of postconditions: a postcondition must be set for
   any possibly raised exception *)

(* let warning_no_post loc x =  *)
(*   wprintf loc "no postcondition for exception %a; false inserted@\n"  *)
(*     Ident.print x; *)
(*   if werror then exit 1 *)

let saturation loc ef (a,al) =
  let xs = ef.E.raises in
  let check (x,_) =
    if not (Sexn.mem x xs) then
      errorm ~loc "exception %a cannot be raised" print_ls x
  in
  List.iter check al;
  let set_post x =
    try
      x, List.assoc x al
    with Not_found ->
      (* warning_no_post loc x; *)
      x, (exn_v_result x, t_false)
  in
  (a, List.map set_post (Sexn.elements xs))

let type_v_unit _env = tpure (ty_app (ts_tuple 0) [])

let remove_bl_effects bl ef =
  let remove ef pv = E.remove pv.pv_regions ef in
  List.fold_left remove ef bl

(* push the labels under the Elet's introduced by make_apply *)

let drown_lab ie e =
  let rec drown e = match e.expr_desc with
    | Elet (v,e1,e2) ->
        { e with expr_desc = Elet (v, e1, drown e2) }
    | _ ->
        { e with expr_lab  = ie.iexpr_lab } in
  match ie.iexpr_desc with
    | IEapply _ | IEapply_var _ | IEapply_glob _ ->
        drown e
    | _ ->
        { e with expr_lab  = ie.iexpr_lab }

(* [expr] translates iexpr into expr
   [env : type_v Mvs.t] maps local variables to their types *)

let rec expr gl env e =
  let ty = e.iexpr_type in
  let loc = e.iexpr_loc in
  let d, v, ef = expr_desc gl env loc ty e.iexpr_desc in
  drown_lab e { expr_desc = d; expr_type = ty; expr_lab = [];
                expr_type_v = v; expr_effect = ef; expr_loc = loc }

and expr_desc gl env loc ty = function
  | IElogic (t, lvars, gvars) ->
      let ef, t = term_effect E.empty t in
      let add_lvar v ef = let v = Mvs.find v env in E.add_var v ef in
      let ef = Svs.fold add_lvar lvars ef in
      let ef = Spv.fold E.add_var gvars ef in
      Elogic t, tpure ty, ef
  | IElocal vs ->
      let vs = Mvs.find vs.i_impure env in
      Elocal vs, vs.pv_tv, E.add_var vs E.empty
  | IEglobal ({ ps_kind = PSvar pv } as s, tv) ->
      Eglobal s, tv, E.add_var pv E.empty
  | IEglobal (s, tv) ->
      Eglobal s, tv, E.empty
  | IEapply (e1, vs) ->
      let e1 = expr gl env e1 in
      (* printf "e1 : %a@." print_type_v e1.expr_type_v; *)
      let vs = Mvs.find vs.i_impure env in
      let c = apply_type_v_var e1.expr_type_v vs in
      (* printf "c : %a / ty = %a@." print_type_c c print_ty ty; *)
      make_apply loc e1 ty c
  | IEapply_var (e1, v) ->
      let e1 = expr gl env e1 in
      let vs = Mvs.find v.i_impure env in
      let c = apply_type_v_var e1.expr_type_v vs in
      (*  printf "c = %a@." print_type_c c; *)
      make_apply loc e1 ty c
  | IEapply_glob (e1, v) ->
      let e1 = expr gl env e1 in
      let c = apply_type_v_var e1.expr_type_v v in
      make_apply loc e1 ty c
  | IEfun (bl, t) ->
      let env, bl = add_binders env bl in
      let (_,e,_) as t, c = triple gl env t in
      let ef = remove_bl_effects bl e.expr_effect in
      Efun (bl, t), tarrow bl c, ef
  | IElet (v, e1, e2) ->
      let e1 = expr gl env e1 in
      let env, v = add_local env v e1.expr_type_v in
      let e2 = expr gl env e2 in
      let ef = E.union e1.expr_effect e2.expr_effect in
      let s = Sreg.filter is_fresh_region v.pv_regions in
      if Sreg.exists (fun r -> occur_type_v r e2.expr_type_v) s then
        errorm ~loc "local reference would escape its scope";
      let ef = E.remove s ef in
      Elet (v, e1, e2), e2.expr_type_v, ef
  | IEletrec (dl, e1) ->
      let env, dl = letrec gl env dl in
      let e1 = expr gl env e1 in
      let add_effect ef (_,_,_,ef') = E.union ef ef' in
      let ef = List.fold_left add_effect e1.expr_effect dl in
      Eletrec (dl, e1), e1.expr_type_v, ef
  | IEif (e1, e2, e3) ->
      let e1 = expr gl env e1 in
      let e2 = expr gl env e2 in
      let e3 = expr gl env e3 in
      let ef = E.union e1.expr_effect e2.expr_effect in
      let ef = E.union ef             e3.expr_effect in
      if not (eq_type_v e2.expr_type_v e3.expr_type_v) then
        errorm ~loc "cannot branch on functions";
      Eif (e1, e2, e3), e2.expr_type_v, ef
  | IEloop (a, e1) ->
      let e1 = expr gl env e1 in
      let ef = e1.expr_effect in
      let ef, inv = option_map_fold term_effect ef a.loop_invariant in
      let ef, var = match a.loop_variant with
        | Some (t, ls) ->
            let ef, t = term_effect ef t in ef, Some (t, ls)
        | None ->
            ef, None
      in
      let a = { loop_invariant = inv; loop_variant = var } in
      Eloop (a, e1), type_v_unit gl, ef
  | IElazy (op, e1, e2) ->
      let e1 = expr gl env e1 in
      let e2 = expr gl env e2 in
      let ef = E.union e1.expr_effect e2.expr_effect in
      let d =
        if is_pure_expr e2 then
          let ls = match op with
            | Ptree.LazyAnd -> find_ls ~pure:true gl "andb"
            | Ptree.LazyOr  -> find_ls ~pure:true gl "orb"
          in
          let v1 = create_pvsymbol_v (id_fresh "lazy") (tpure ty) in
          let v2 = create_pvsymbol_v (id_fresh "lazy") (tpure ty) in
          let t = fs_app ls [t_var v1.pv_pure; t_var v2.pv_pure] ty in
          Elet (v1, e1,
                mk_expr loc ty ef
                  (Elet (v2, e2, mk_simple_expr loc ty (Elogic t))))
        else match op with
          | Ptree.LazyAnd ->
              Eif (e1, e2, mk_false loc gl)
          | Ptree.LazyOr ->
              Eif (e1, mk_true loc gl, e2)
      in
      d, tpure ty, ef
  | IEnot e1 ->
      let e1 = expr gl env e1 in
      let ls = find_ls ~pure:true gl "notb" in
      let v1 = create_pvsymbol_v (id_fresh "lazy") (tpure ty) in
      let t = fs_app ls [t_var v1.pv_pure] ty in
      let d = Elet (v1, e1, mk_simple_expr loc ty (Elogic t)) in
      d, tpure ty, e1.expr_effect
  | IEmatch (i, bl) ->
      let v = Mvs.find i.i_impure env in
      let branch ef (p, e) =
        let env, p = pattern env p in
        let e = expr gl env e in
        let ef = E.union ef e.expr_effect in
        ef, (p, e)
      in
      let ef, bl = map_fold_left branch E.empty bl in
      Ematch (v, bl), tpure ty, ef
  | IEabsurd ->
      Eabsurd, tpure ty, E.empty
  | IEraise (x, e1) ->
      let e1 = option_map (expr gl env) e1 in
      let ef = match e1 with Some e1 -> e1.expr_effect | None -> E.empty in
      let ef = E.add_raise x ef in
      Eraise (x, e1), tpure ty, ef
  | IEtry (e1, hl) ->
      let e1 = expr gl env e1 in
      let ef = e1.expr_effect in
      let handler (x, v, h) =
        if not (Sexn.mem x ef.E.raises) && !exn_check then
          errorm ~loc "exception %a cannot be raised" print_ls x;
        let env, v = match x.ls_args, v with
          | [ty], Some v ->
              let env, v = add_local env v (tpure ty) in env, Some v
          | [], None ->
              env, None
          | _ -> assert false
        in
        x, v, expr gl env h
      in
      let ef = List.fold_left (fun e (x,_,_) -> E.remove_raise x e) ef hl in
      let hl = List.map handler hl in
      let ef =
        List.fold_left (fun e (_,_,h) -> E.union e h.expr_effect) ef hl
      in
      Etry (e1, hl), tpure ty, ef
  | IEfor (x, v1, d, v2, inv, e3) ->
      let v1 = Mvs.find v1.i_impure env in
      let v2 = Mvs.find v2.i_impure env in
      let env, x = add_local env x (tpure v1.pv_pure.vs_ty) in
      let e3 = expr gl env e3 in
      let ef = e3.expr_effect in
      let ef, inv = option_map_fold term_effect ef inv in
      Efor (x, v1, d, v2, inv, e3), type_v_unit gl, ef
  | IEassert (k, f) ->
      let ef, f = term_effect E.empty f in
      Eassert (k, f), tpure ty, ef
  | IEmark (m, e1) ->
      let e1 = expr gl env e1 in
      Emark (m, e1), e1.expr_type_v, e1.expr_effect
  | IEany c ->
      let c = type_c env c in
      Eany c, c.c_result_type, c.c_effect

and triple gl env (p, e, q) =
  let e = expr gl env e in
  let q = saturation e.expr_loc e.expr_effect q in
  let ef = e.expr_effect in
  let ef, p = term_effect ef p in
  let ef, q = post_effect ef q in
  (* eprintf "triple: p = %a ef = %a@." Pretty.print_fmla p E.print ef; *)
  let e = { e with expr_effect = ef } in
  let c =
    { c_result_type = e.expr_type_v;
      c_effect      = ef;
      c_pre         = p;
      c_post        = q }
  in
  (p, e, q), c

and letrec gl env dl = (* : env * recfun list *)
  let binders (i, bl, var, t) =
    let env, bl = add_binders env bl in
    let variant (i, t, ls) =
      (create_pvsymbol (id_clone i.i_impure.vs_name)
         ~effect:i.i_effect ~pure:i.i_pure
         (tpure i.i_impure.vs_ty), t, ls)
    in
    (i, bl, env, option_map variant var, t)
  in
  let dl = List.map binders dl in
  (* effects are computed as a least fixpoint
     [m] maps each function to its current effect *)
  let make_env env ?decvar m =
    let add1 env (i, bl, _, var, _) =
      let c = Mvs.find i.i_impure m in
      let c = match decvar, var with
        | Some phi0, Some (_, phi, r) ->
            let _, phi = term_effect E.empty phi in
            let decphi = match r with
              | Vint (le, lt) -> Pgm_wp.default_variant le lt phi (t_var phi0)
              | Vuser r -> ps_app r [phi; t_var phi0]
            in
            { c with c_pre = t_and decphi c.c_pre }
        | _ ->
            c
      in
      let env, _ = add_local env i (tarrow bl c) in
      env
    in
    List.fold_left add1 env dl
  in
  let one_step m0 =
    let type1 m (i, bl, env, var, t) =
      let decvar = option_map (fun (v,_,_) -> v.pv_pure) var in
      let env = make_env env ?decvar m0 in
      let t, c = triple gl env t in
      let v = create_pvsymbol (id_clone i.i_impure.vs_name) (tarrow bl c)
        ~effect:i.i_effect ~pure:i.i_pure
      in
      Mvs.add i.i_impure c m, (v, bl, var, t)
    in
    map_fold_left type1 Mvs.empty dl
  in
  let rec fixpoint m =
    (* printf "fixpoint...@\n"; *)
    let m', dl' = one_step m in
    let same_effect (i,bl,_,_,_) =
      let c = Mvs.find i.i_impure m and c' = Mvs.find i.i_impure m' in
      let v = tarrow bl c and v' = tarrow bl c' in
      (* printf "  v = %a@." print_type_v v; *)
      (* printf "  v'= %a@." print_type_v v'; *)
      eq_type_v v v'
      (* E.equal c.c_effect c'.c_effect *)
    in
    if List.for_all same_effect dl then m, dl' else fixpoint m'
  in
  let add_empty_effect m (i, bl, _, _, (p, _, q)) =
    let tyl, ty = uncurrying i.i_impure.vs_ty in
    assert (List.length bl = List.length tyl);
    let c = { c_result_type = tpure ty;
              c_pre = p; c_effect = E.empty; c_post = q; }
    in
    Mvs.add i.i_impure c m
  in
  let m0 = List.fold_left add_empty_effect Mvs.empty dl in
  let m, dl = fixpoint m0 in
  let add_effect (pv, bl, _, (_,e,_ as t)) =
    pv, bl, t, remove_bl_effects bl e.expr_effect
  in
  make_env env m, List.map add_effect dl

(* freshness analysis

   checks that values of type 'a ref are only freshly allocated
   term:bool indicates if we are in terminal position in the expression
   (to allow functions to return fresh references) *)

let rec fresh_expr gl ~term locals e = match e.expr_desc with
  | Elocal vs when is_mutable_ty vs.pv_effect.vs_ty
    && term && not (Spv.mem vs locals) ->
      errorm ~loc:e.expr_loc "not a fresh value (could create an alias)"
  | Elogic _ | Elocal _ | Eglobal _ ->
      ()
  | Efun (_, t) ->
      fresh_triple gl t
  | Elet (vs, e1, e2) ->
      fresh_expr gl ~term:false locals              e1;
      fresh_expr gl ~term       (Spv.add vs locals) e2
  | Eletrec (fl, e1) ->
      List.iter (fun (_, _, t, _) -> fresh_triple gl t) fl;
      fresh_expr gl ~term locals e1

  | Eif (e1, e2, e3) ->
      fresh_expr gl ~term:false locals e1;
      fresh_expr gl ~term       locals e2;
      fresh_expr gl ~term       locals e3
  | Eloop (_, e1) ->
      fresh_expr gl ~term:false locals e1
  | Ematch (_, bl) ->
      let branch (_, e1) = fresh_expr gl ~term locals e1 in
      List.iter branch bl
  | Eabsurd | Eraise (_, None) ->
      ()
  | Eraise (_, Some e1) ->
      fresh_expr gl ~term:false locals e1
  | Etry (e1, hl) ->
      fresh_expr gl ~term:false locals e1;
      List.iter (fun (_, _, e2) -> fresh_expr gl ~term locals e2) hl
  | Efor (_, _, _, _, _, e1) ->
      fresh_expr gl ~term:false locals e1

  | Emark (_, e) ->
      fresh_expr gl ~term locals e
  | Eassert _ | Eany _ ->
      ()

and fresh_triple gl (_, e, _) =
  fresh_expr gl ~term:true Spv.empty e

(* typing declarations (combines the three phases together) *)

let create_ienv denv = {
  i_uc = denv.uc;
  i_denv = denv.denv;
  i_impures = Mstr.empty;
  i_effects = Mstr.empty;
  i_pures = Hls.fold (fun _ pv m -> Mstr.add pv.pv_name.id_string pv.pv_pure m)
    globals Mstr.empty;
}

let type_type uc ty =
  let denv = create_denv uc in
  let dty = Typing.dty (impure_uc uc) denv.denv ty in
  Denv.ty_of_dty dty

let add_pure_decl uc ?loc ls =
  try
    Pgm_module.add_pure_decl (Decl.create_logic_decl [ls, None]) uc
  with Theory.ClashSymbol _ ->
    errorm ?loc "clash with previous symbol %s" ls.ls_name.id_string

let add_effect_decl uc ls =
  Pgm_module.add_effect_decl (Decl.create_logic_decl [ls, None]) uc

let add_impure_decl uc ls =
  Pgm_module.add_impure_decl (Decl.create_logic_decl [ls, None]) uc

let add_global_fun loc ~labels x tyv uc =
  let x = parameter x in
  try
    let label,loc =
      List.fold_left
        (fun (labels,loc) lab ->
           match lab with
             | Lstr s -> (s::labels,loc)
             | Lpos l -> (labels,l))
        ([],loc)
        labels
    in
    let ls, ps = create_psymbol_fun (id_user ~label x loc) tyv in
    let d = Decl.create_logic_decl [ls, None] in
    ps, Pgm_module.add_impure_decl d uc
  with Pgm_module.ClashSymbol _ ->
    errorm ~loc "clash with previous symbol %s" x

let add_exception loc x ty uc =
  try
    let tyl = match ty with None -> [] | Some ty -> [ty] in
    let id = id_user x loc in
    let ls = create_lsymbol id tyl (Some (ty_app ts_exn [])) in
    add_esymbol ls uc
  with ClashSymbol _ ->
    errorm ~loc "clash with previous exception %s" x

(* [cannot_be_generalized_ty ty] returns a pair (t, m) where
   [t = true] iff [ty] contains a type variable
   [m = true] iff [ty] contains a polymorphic mutable type *)
let rec cannot_be_generalized_ty ty = match ty.ty_node with
  | Ty.Tyapp (ts, tyl) ->
      let n = (get_mtsymbol ts).mt_regions in
      let t, m = List.fold_left
        (fun (acct, accm) ty ->
           let t, m = cannot_be_generalized_ty ty in acct || t, accm || m)
        (false, false)
        (Util.chop n tyl)
      in
      t, m || n > 0 && t
  | Ty.Tyvar _ ->
      true, false

let cannot_be_generalized = function
  | Tpure ty -> let _, m = cannot_be_generalized_ty ty in m
  | Tarrow _ -> false

let check_type_vars ~loc vars ty =
  let h = Htv.create 17 in
  List.iter (fun v -> Htv.add h v ()) vars;
  let rec check ty = match ty.ty_node with
    | Ty.Tyvar v when not (Htv.mem h v) ->
        errorm ~loc "unbound type variable '%s" v.tv_name.id_string
    | Ty.Tyvar _ ->
        ()
    | Ty.Tyapp (_, tyl) ->
        List.iter check tyl
  in
  check ty

let make_immutable_type td =
  let td = { td with td_model = false } in
  let make_immutable_field (loc, _, id, ty) = (loc, false, id, ty) in
  match td.td_def with
(*     | TDrecord [_, _, _, ty] -> (\* singleton record *\) *)
(*         { td with td_def = TDalias ty } *)
    | TDrecord fl ->
        { td with td_def = TDrecord (List.map make_immutable_field fl) }
    | TDabstract | TDalias _ | TDalgebraic _ ->
        td

let add_logic_ps ?(nofail=false) uc x =
  try
    let get th = ns_find_ls (get_namespace th) [x] in
    let pure   = get (pure_uc   uc) in
    let effect = get (effect_uc uc) in
    let impure = try Some (get (impure_uc uc)) with Not_found -> None in
    ignore (create_psymbol ?impure ~effect ~pure ~kind:PSlogic)
  with Not_found ->
    (* can fail if x is a constructor of a model type (record or algebraic) *)
    assert nofail

let add_types env ltm uc dl =
  (* 1. type check the pure def, to have all sanity checks performed *)
  let dlp = List.map make_immutable_type dl in
  let uc = Pgm_module.add_pure_pdecl env ltm (TypeDecl dlp) uc in
  (* 2. compute number of regions for each type *)
  let def = List.fold_left
    (fun def d -> Mstr.add d.td_ident.id d def) Mstr.empty dl
  in
  let nregions = Hashtbl.create 17 in (* name -> int *)
  let mutable_field = Hashtbl.create 17 in (* name, field -> region *)
  let singletons = Hashtbl.create 17 in
  let projections = ref [] in
  let add_projection x = projections := x.id :: !projections in
  let rec visit x =
    try
      match Hashtbl.find nregions x with
        | None -> 0 (* for recursive data types *)
        | Some n -> n
    with Not_found ->
      Hashtbl.add nregions x None;
      let d = Mstr.find x def in
      let n = match d.td_def with
        | TDabstract ->
            0
        | TDalias ty ->
            nregions_of_type ty
        | TDalgebraic cl ->
            let param n (_, ty) = n + nregions_of_type ty in
            let constructor n (_, _, pl) = List.fold_left param n pl in
            List.fold_left constructor 0 cl
        | TDrecord fl ->
            let nf = List.length fl in
            List.fold_left
              (fun n (loc, mut, _, ty) ->
                 if mut && nf = 1 then Hashtbl.add singletons x ();
                 let nty = nregions_of_type ty in
                 if mut then begin
                   if nty > 0 then
                     errorm ~loc "inner mutable types not yet implemented";
                   n + 1
                 end else
                   n + nty)
              0 fl
      in
      Hashtbl.add nregions x (Some n);
      n
  and nregions_of_type = function
    | PPTtyvar _ ->
        0
    | PPTtyapp (tyl, q) ->
        let n = nregions_of_qualid q in
        n + nregions_of_types tyl
    | PPTtuple tyl ->
        nregions_of_types tyl
  and nregions_of_types tyl =
    List.fold_left (fun n ty -> n + nregions_of_type ty) 0 tyl
  and nregions_of_qualid q = match q with
    | Qident x when Mstr.mem x.id def ->
        visit x.id
    | Qident _ | Qdot _ ->
        try
          let p = Typing.string_list_of_qualid [] q in
          let ts = ns_find_ts (get_namespace (impure_uc uc)) p in
          (get_mtsymbol ts).mt_regions
        with Not_found ->
          0 (* TODO: should have a mt already? *)
  in
  List.iter (fun d -> ignore (visit d.td_ident.id)) dl;
  (* 3. build new type declarations with regions for program/effect types *)
  let add_regions ~effect d =
    let x = d.td_ident.id in
    let n = of_option (Hashtbl.find nregions x) in
    let loc = d.td_loc in
    let regions =
      Array.init n
        (fun i -> { id = "r" ^ string_of_int i; id_lab = []; id_loc = loc })
    in
    let params = Array.to_list regions @ d.td_params in
    let region =
      let c = ref (-1) in fun () -> incr c; assert (!c < n); !c, regions.(!c)
    in
    let rec add_regions_to_type = function
      | PPTtyvar _ as ty ->
          ty
      | PPTtyapp (tyl, q) ->
          let n = nregions_of_qualid q in
          let reg = ref [] in
          for i = 1 to n do reg := PPTtyvar (snd (region ())) :: !reg done;
          PPTtyapp (List.rev !reg @ List.map add_regions_to_type tyl, q)
      | PPTtuple tyl ->
          PPTtuple (List.map add_regions_to_type tyl)
    in
    let def = match d.td_def with
      | _ when d.td_model && not effect ->
          TDabstract
      | TDabstract ->
          TDabstract
      | TDalias ty ->
          TDalias (add_regions_to_type ty)
      | TDalgebraic cl ->
          let add (x, ty) =
            option_iter add_projection x;
            x, add_regions_to_type ty
          in
          let constructor (loc, id, pl) = (loc, id, List.map add pl) in
          TDalgebraic (List.map constructor cl)
      | TDrecord fl ->
          let add i (loc, mut, id, ty) =
            add_projection id;
            if mut then begin
              let j, _ = region () in
              if effect then Hashtbl.add mutable_field (x, i) j
            end;
            (loc, false, id, add_regions_to_type ty)
          in
          TDrecord (list_mapi add fl)
    in
    { d with td_params = params; td_model = false; td_def = def }
  in
  let dli = List.map (add_regions ~effect:false) dl in
  let uc = Pgm_module.add_impure_pdecl env ltm (Ptree.TypeDecl dli) uc in
  let dle = List.map (add_regions ~effect:true) dl in
  let uc = Pgm_module.add_effect_pdecl env ltm (Ptree.TypeDecl dle) uc in
  (* 4. add mtsymbols in module *)
  let add_mt d =
    let x = d.td_ident.id in
    let get th = ns_find_ts (get_namespace th) [x] in
    let impure = get (impure_uc uc) in
    let effect = get (effect_uc uc) in
    let pure   = get (pure_uc   uc) in
    let singleton = Hashtbl.mem singletons x in
    ignore (create_mtsymbol ~impure ~effect ~pure ~singleton)
  in
  List.iter add_mt dl;
  (* 5. declare region types *)
  let visited = Hashtbl.create 17 in
  let th = effect_uc uc in
  let km = get_known th in
  let rec visit x =
    if not (Hashtbl.mem visited x) then begin
      Hashtbl.add visited x ();
      if is_debug () then
        eprintf "@[type %s: %d regions@\n" x
          (of_option (Hashtbl.find nregions x));
      let ts = ns_find_ts (get_namespace th) [x] in
      Hashtbl.iter
        (fun (y, i) j -> if y = x then begin
           if is_debug () then eprintf "  field %d = region %d@\n" i j;
           declare_mutable_field ts i j
         end)
        mutable_field;
      let region = ref (-1) in
      let declare_region_type ty =
        incr region; declare_region_type ts !region ty
      in
      let rec visit_type ty = match ty.ty_node with
        | Ty.Tyvar _ ->
            ()
        | Ty.Tyapp (ts, tyl) ->
            let y = ts.ts_name.id_string in
            let n =
              if Mstr.mem y def then begin
                visit y; of_option (Hashtbl.find nregions y)
              end else
                (get_mtsymbol ts).mt_regions
            in
            let rl = regions_tyapp ts n tyl in
            List.iter (fun r -> declare_region_type r.R.r_ty) rl;
            List.iter visit_type tyl
      in
      begin match ts.ts_def with
        | None -> (* abstract or algebraic *)
            begin match Decl.find_constructors km ts with
              | [] -> (* abstract *)
                  ()
              | [ls] -> (* record *)
                  add_logic_ps ~nofail:true uc ls.ls_name.id_string;
                  let field i ty =
                    if Hashtbl.mem mutable_field (x, i) then
                      declare_region_type ty;
                    visit_type ty
                  in
                  list_iteri field ls.ls_args
              | cl -> (* algebraic *)
                  let constructor ls =
                    add_logic_ps ~nofail:true uc ls.ls_name.id_string;
                    List.iter visit_type ls.ls_args
                  in
                  List.iter constructor cl
            end
        | Some ty -> (* alias *)
            visit_type ty
      end;
      if is_debug () then eprintf "@]"
    end
  in
  List.iter (add_logic_ps ~nofail:true uc) !projections;
  List.iter (fun d -> visit d.td_ident.id) dl;
  uc

let add_logics env ltm uc d =
  let uc = Pgm_module.add_pure_pdecl env ltm d uc in
  let region =
    let c = ref (-1) in
    fun loc ->
      incr c; { id = "r" ^ string_of_int !c; id_lab = []; id_loc = loc }
  in
  let rec add_regions_to_type = function
    | PPTtyvar _ as ty ->
        ty
    | PPTtyapp (tyl, q) ->
        let loc = Typing.qloc q in
        let p = Typing.string_list_of_qualid [] q in
        let ts = ns_find_ts (get_namespace (impure_uc uc)) p in
        let n = (get_mtsymbol ts).mt_regions in
        let reg = ref [] in
        for i = 1 to n do reg := PPTtyvar (region loc) :: !reg done;
        PPTtyapp (List.rev !reg @ List.map add_regions_to_type tyl, q)
    | PPTtuple tyl ->
        PPTtuple (List.map add_regions_to_type tyl)
  in
  let add_param (x, ty) = (x, add_regions_to_type ty) in
  let add_regions d =
    { d with
        ld_params = List.map add_param d.ld_params;
        ld_type   = option_map add_regions_to_type d.ld_type;
        ld_def    = None; }
  in
  let add uc d0 =
    let d = LogicDecl [add_regions d0] in
    let uc = Pgm_module.add_impure_pdecl env ltm d uc in
    let uc = Pgm_module.add_effect_pdecl env ltm d uc in
    add_logic_ps uc d0.ld_ident.id;
    uc
  in
  let addi uc d =
    add uc { ld_loc = d.in_loc; ld_ident = d.in_ident;
             ld_params = d.in_params; ld_type = None; ld_def = None; }
  in
  match d with
    | LogicDecl dl -> List.fold_left add uc dl
    | IndDecl dl -> List.fold_left addi uc dl
    | Meta _ | UseClone _ | PropDecl _ | TypeDecl _ -> assert false

let find_module penv lmod q id = match q with
  | [] ->
      (* local module *)
      Mstr.find id lmod
  | _ :: _ ->
      (* theory in file f *)
      Pgm_env.find_module penv q id

(* env  = to retrieve theories from the loadpath
   penv = to retrieve modules from the loadpath
   lmod = local modules *)
let rec decl ~wp env penv ltm lmod uc = function
  | Ptree.Dlet (id, e) ->
      let denv = create_denv uc in
      let e = dexpr ~ghost:false ~userloc:None denv e in
      let e = iexpr (create_ienv denv) e in
      let e = expr uc Mvs.empty e in
      check_region_vars ();
      ignore (fresh_expr uc ~term:false Spv.empty e);
      if Debug.test_flag debug then
        eprintf "@[--typing %s-----@\n  @[<hov 2>%a@]@\n@[<hov 2>: %a@]@]@."
          id.id Pgm_pretty.print_expr e print_type_v e.expr_type_v;
      let ls, uc =
        add_global_fun id.id_loc ~labels:id.id_lab id.id e.expr_type_v uc
      in
      let d = Dlet (ls, e) in
      let uc = add_decl d uc in
      if wp then Pgm_wp.decl uc d else uc
  | Ptree.Dletrec dl ->
      let denv = create_denv uc in
      let _, dl = dletrec ~ghost:false ~userloc:None denv dl in
      let _, dl = iletrec (create_ienv denv) dl in
      let _, dl = letrec uc Mvs.empty dl in
      List.iter (fun (_, _, t, _) -> fresh_triple uc t) dl;
      check_region_vars ();
      let one uc (v, _, _, _ as d) =
        let tyv = v.pv_tv in
        let loc = loc_of_id v.pv_name in
        let id = v.pv_name.id_string in
        if Debug.test_flag debug then
          eprintf "@[--typing %s-----@\n  %a@.%a@]@."
            id Pgm_pretty.print_recfun d print_type_v tyv;
        let ps, uc =
          add_global_fun loc ~labels:[] (* FIXME *) id tyv uc
        in
        uc, (ps, d)
      in
      let uc, dl = map_fold_left one uc dl in
      let d = Dletrec dl in
      let uc = add_decl d uc in
      if wp then Pgm_wp.decl uc d else uc
  | Ptree.Dparam (id, tyv) ->
      let loc = id.id_loc in
      let denv = create_denv uc in
      let tyv = dutype_v denv tyv in
      let tyv = iutype_v (create_ienv denv) tyv in
      let tyv = type_v Mvs.empty tyv in
      if cannot_be_generalized tyv then errorm ~loc "cannot be generalized";
      if Debug.test_flag debug then
        eprintf "@[--parameter %s-----@\n  %a@]@."
          id.id print_type_v tyv;
      let ps, uc = match tyv with
        | Tarrow _ ->
            let ps, uc =
              add_global_fun loc ~labels:[] (* FIXME *) id.id tyv uc
            in
            ps, uc
        | Tpure _ ->
            let id = id_user id.id loc in
            let pv = create_pvsymbol_v id tyv in
            let ls, ps = create_psymbol_var pv in
            let uc = add_pure_decl   uc ~loc ps.ps_pure in
            let uc = add_effect_decl uc ps.ps_effect in
            let uc = add_impure_decl uc ls in
            declare_global ps.ps_pure pv;
            ps, uc
      in
      add_decl (Dparam ps) uc (* TODO: is it really needed? *)
  | Ptree.Dexn (id, ty) ->
      let ty = option_map (type_type uc) ty in
      add_exception id.id_loc id.id ty uc
  (* modules *)
  | Ptree.Duse (qid, imp_exp, use_as) ->
      let loc = Typing.qloc qid in
      let q, id = Typing.split_qualid qid in
      let m =
        try
          find_module penv lmod q id
        with Not_found | Pgm_env.ModuleNotFound _ ->
          errorm ~loc "@[unbound module %a@]" print_qualid qid
      in
      let n = match use_as with
        | None -> Some (m.m_name.id_string)
        | Some x -> Some x.id
      in
      begin try match imp_exp with
        | Nothing ->
            (* use T = namespace T use_export T end *)
            let uc = open_namespace uc in
            let uc = use_export uc m in
            close_namespace uc false n
        | Import ->
            (* use import T = namespace T use_export T end import T *)
            let uc = open_namespace uc in
            let uc = use_export uc m in
            close_namespace uc true n
        | Export ->
            use_export uc m
      with ClashSymbol s ->
        errorm ~loc "clash with previous symbol %s" s
      end
  | Ptree.Dnamespace (loc, id, import, dl) ->
      let uc = open_namespace uc in
      let uc = List.fold_left (decl ~wp env penv ltm lmod) uc dl in
      let id = option_map (fun id -> id.id) id in
      begin try close_namespace uc import id
      with ClashSymbol s -> errorm ~loc "clash with previous symbol %s" s end
  | Ptree.Dlogic (TypeDecl d) ->
      add_types env ltm uc d
  | Ptree.Dlogic (LogicDecl _ | IndDecl _ as d) ->
      add_logics env ltm uc d
  | Ptree.Dlogic (PropDecl _ | Meta _ as d) ->
      Pgm_module.add_pure_pdecl env ltm d uc
  | Ptree.Dlogic (UseClone _ as d) ->
      Pgm_module.add_pdecl env ltm d uc

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)

(*
TODO:

- mutually recursive functions: allow order relation to be specified only once

- exhaustivity of pattern-matching (in WP?)

- do not add global references into the pure theory

- polymorphic let?

- ghost
*)
