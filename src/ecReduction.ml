(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcPath
open EcTypes
open EcModules
open EcFol
open EcEnv

module BI = EcBigInt

module Debug =
  struct

    let rec pp_list sep pp fmt xs =
      let pp_list = pp_list sep pp in
      match xs with
      | []      -> ()
      | [x]     -> Format.fprintf fmt "%a" pp x
      | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs

    let pp_binding fmt (x,_) = EcIdent.pp_ident fmt x

    let pp_bindings fmt xs =
      Format.fprintf fmt "@[%a@]" (pp_list "@ " pp_binding) xs

    let pp_q = function
      | Lforall -> "forall", ","
      | Lexists -> "exists", ","
      | Llambda  -> "fun", "=>"

    let rec pp_form fmt f =
      match f.f_node with
      | Fquant (q, bd, f) ->
        let sq, sv = pp_q q in
        Format.fprintf fmt "@[(%s %a%s@ %a)@]"
          sq pp_bindings bd sv pp_form f

      | Fif(a,b,c) ->
        Format.fprintf fmt "@[(if %a then@ %a@ else@ %a)@]"
          pp_form a pp_form b pp_form c

      | Fint i -> EcBigInt.pp_print fmt i

      | Flocal x -> EcIdent.pp_ident fmt x

      | Fpvar(x,m) ->
        Format.fprintf fmt "%s{%a}"
        (EcPath.x_tostring x.pv_name) EcIdent.pp_ident m
      | Fglob(p,m) ->
        Format.fprintf fmt "(glob %s){%a}"
        (EcPath.m_tostring p) EcIdent.pp_ident m
      | Fop(p,_) -> Format.fprintf fmt "%s" (EcPath.tostring p)

      | Fapp(f, args) ->
        Format.fprintf fmt "@[(%a)@]"
          (pp_list "@ " pp_form) (f::args)

      | Ftuple args ->
        Format.fprintf fmt "@[(%a)@]"
          (pp_list ",@ " pp_form) args

      | Fproj(f,i) ->
        Format.fprintf fmt "@[%a.%i@]" pp_form f i

      | _ -> Format.fprintf fmt "?"
  end

(* -------------------------------------------------------------------- *)
exception IncompatibleType of env * (ty * ty)
exception IncompatibleForm of env * (form * form)

(* -------------------------------------------------------------------- *)
type 'a eqtest  = env -> 'a -> 'a -> bool
type 'a eqntest = env -> ?norm:bool -> 'a -> 'a -> bool

module EqTest = struct
  let rec for_type env t1 t2 =
    ty_equal t1 t2 || for_type_r env t1 t2

  and for_type_r env t1 t2 =
    match t1.ty_node, t2.ty_node with
    | Tunivar uid1, Tunivar uid2 -> EcUid.uid_equal uid1 uid2

    | Tvar i1, Tvar i2 -> i1 = i2

    | Ttuple lt1, Ttuple lt2 ->
          List.length lt1 = List.length lt2
       && List.all2 (for_type env) lt1 lt2

    | Tfun (t1, t2), Tfun (t1', t2') ->
        for_type env t1 t1' && for_type env t2 t2'

    | Tglob mp, _ when EcEnv.NormMp.tglob_reducible env mp ->
        for_type env (EcEnv.NormMp.norm_tglob env mp) t2

    | _, Tglob mp when EcEnv.NormMp.tglob_reducible env mp ->
        for_type env t1 (EcEnv.NormMp.norm_tglob env mp)

    | Tconstr (p1, lt1), Tconstr (p2, lt2) when EcPath.p_equal p1 p2 ->
        if
             List.length lt1 = List.length lt2
          && List.all2 (for_type env) lt1 lt2
        then true
        else
          if   Ty.defined p1 env
          then for_type env (Ty.unfold p1 lt1 env) (Ty.unfold p2 lt2 env)
          else false

    | Tconstr(p1,lt1), _ when Ty.defined p1 env ->
        for_type env (Ty.unfold p1 lt1 env) t2

    | _, Tconstr(p2,lt2) when Ty.defined p2 env ->
        for_type env t1 (Ty.unfold p2 lt2 env)

    | _, _ -> false

  (* ------------------------------------------------------------------ *)
  let is_unit env ty = for_type env tunit ty
  let is_bool env ty = for_type env tbool ty
  let is_int  env ty = for_type env tint  ty

  (* ------------------------------------------------------------------ *)
  let for_type_exn env t1 t2 =
    if not (for_type env t1 t2) then
      raise (IncompatibleType (env, (t1, t2)))

  (* ------------------------------------------------------------------ *)
  let for_pv env ~norm p1 p2 =
    pv_equal p1 p2 || (norm && (p1.pv_kind = p2.pv_kind) &&
      let p1 = NormMp.norm_pvar env p1 in
      let p2 = NormMp.norm_pvar env p2 in
      EcPath.x_equal p1.pv_name p2.pv_name)

  (* ------------------------------------------------------------------ *)
  let for_xp env ~norm p1 p2 =
     EcPath.x_equal p1 p2 || (norm &&
       let p1 = NormMp.norm_xfun env p1 in
       let p2 = NormMp.norm_xfun env p2 in
       EcPath.x_equal p1 p2)

  (* ------------------------------------------------------------------ *)
  let for_mp env ~norm p1 p2 =
     EcPath.m_equal p1 p2 || (norm &&
       let p1 = NormMp.norm_mpath env p1 in
       let p2 = NormMp.norm_mpath env p2 in
       EcPath.m_equal p1 p2)

  (* ------------------------------------------------------------------ *)
  let for_expr env ~norm =
    let module E = struct exception NotConv end in

    let find alpha id = odfl id (Mid.find_opt id alpha) in

    let noconv (f : expr -> expr -> bool) e1 e2 =
      try f e1 e2 with E.NotConv -> false in

    let check_lpattern alpha lp1 lp2 =
      match lp1, lp2 with
      | LSymbol (id1,_), LSymbol (id2,_) ->
          Mid.add id1 id2 alpha

      | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
          List.fold_left2
            (fun alpha (id1,_) (id2,_) -> Mid.add id1 id2 alpha)
            alpha lid1 lid2

      | _, _ -> raise E.NotConv in

    let check_binding env alpha (id1, ty1) (id2, ty2) =
      if not (for_type env ty1 ty2) then
        raise E.NotConv;
      Mid.add id1 id2 alpha in

    let check_bindings env alpha b1 b2 =
      if List.length b1 <> List.length b2 then
        raise E.NotConv;
      List.fold_left2 (check_binding env) alpha b1 b2 in

    let rec aux alpha e1 e2 =
      e_equal e1 e2 || aux_r alpha e1 e2

    and aux_r alpha e1 e2 =
      match e1.e_node, e2.e_node with
      | Eint i1, Eint i2 ->
          BI.equal i1 i2

      | Elocal id1, Elocal id2 ->
          EcIdent.id_equal (find alpha id1) id2

      | Evar p1, Evar p2 ->
          for_pv env ~norm p1 p2

      | Eop(o1,ty1), Eop(o2,ty2) ->
          p_equal o1 o2 && List.all2 (for_type env) ty1 ty2

      | Equant(q1,b1,e1), Equant(q2,b2,e2) when qt_equal q1 q2 ->
          let alpha = check_bindings env alpha b1 b2 in
          noconv (aux alpha) e1 e2

      | Eapp (f1, args1), Eapp (f2, args2) ->
          aux alpha f1 f2 && List.all2 (aux alpha) args1 args2

      | Elet (p1, f1', g1), Elet (p2, f2', g2) ->
          aux alpha f1' f2'
            && noconv (aux (check_lpattern alpha p1 p2)) g1 g2

      | Etuple args1, Etuple args2 -> List.all2 (aux alpha) args1 args2

      | Eif (a1,b1,c1), Eif(a2,b2,c2) ->
          aux alpha a1 a2 && aux alpha b1 b2 && aux alpha c1 c2

      | Ematch (e1,es1,ty1), Ematch(e2,es2,ty2) ->
          for_type env ty1 ty2
            && List.all2 (aux alpha) (e1::es1) (e2::es2)

      | _, _ -> false

    in fun e1 e2 -> aux Mid.empty e1 e2

  (* ------------------------------------------------------------------ *)
  let for_lv env ~norm lv1 lv2 =
    match lv1, lv2 with
    | LvVar(p1, _), LvVar(p2, _) ->
        for_pv env ~norm p1 p2

    | LvTuple p1, LvTuple p2 ->
        List.all2
          (fun (p1, _) (p2, _) -> for_pv env ~norm p1 p2)
          p1 p2

    | LvMap ((m1, ty1), p1, e1, _), LvMap ((m2, ty2), p2, e2, _) ->
        p_equal m1 m2
          && List.all2 (for_type env) ty1 ty2
          && for_pv env ~norm p1 p2
          && for_expr env ~norm e1 e2

    | _, _ -> false

  (* ------------------------------------------------------------------ *)
  let rec for_stmt env ~norm s1 s2 =
       s_equal s1 s2
    || List.all2 (for_instr env ~norm) s1.s_node s2.s_node

  (* ------------------------------------------------------------------ *)
  and for_instr env ~norm i1 i2 =
    i_equal i1 i2 || for_instr_r env ~norm i1 i2

  and for_instr_r env ~norm i1 i2 =
    match i1.i_node, i2.i_node with
    | Sasgn (lv1, e1), Sasgn (lv2, e2) ->
        for_lv env ~norm lv1 lv2 && for_expr env ~norm e1 e2

    | Srnd (lv1, e1), Srnd (lv2, e2) ->
        for_lv env ~norm lv1 lv2 && for_expr env ~norm e1 e2

    | Scall (lv1, f1, e1), Scall (lv2, f2, e2) ->
        oall2 (for_lv env ~norm) lv1 lv2
          && for_xp env ~norm f1 f2
          && List.all2 (for_expr env ~norm) e1 e2

    | Sif (a1, b1, c1), Sif(a2, b2, c2) ->
        for_expr env ~norm a1 a2
          && for_stmt env ~norm b1 b2
          && for_stmt env ~norm c1 c2

    | Swhile(a1,b1), Swhile(a2,b2) ->
        for_expr env ~norm a1 a2 && for_stmt env ~norm b1 b2

    | Sassert a1, Sassert a2 ->
        for_expr env ~norm a1 a2

    | Sabstract id1, Sabstract id2 ->
        EcIdent.id_equal id1 id2

    | _, _ -> false

  (* ------------------------------------------------------------------ *)
  let for_pv    = fun env ?(norm = true) -> for_pv    env ~norm
  let for_xp    = fun env ?(norm = true) -> for_xp    env ~norm
  let for_mp    = fun env ?(norm = true) -> for_mp    env ~norm
  let for_instr = fun env ?(norm = true) -> for_instr env ~norm
  let for_stmt  = fun env ?(norm = true) -> for_stmt  env ~norm
  let for_expr  = fun env ?(norm = true) -> for_expr  env ~norm
end

(* -------------------------------------------------------------------- *)
type reduction_info = {
  beta    : bool;
  delta_p : (path  -> bool);
  delta_h : (ident -> bool);
  zeta    : bool;
  iota    : bool;
  eta     : bool;
  logic   : rlogic_info;
  modpath : bool;
  user    : bool;
}

and rlogic_info = [`Full | `ProductCompat] option

(* -------------------------------------------------------------------- *)
let full_red = {
  beta    = true;
  delta_p = EcUtils.predT;
  delta_h = EcUtils.predT;
  zeta    = true;
  iota    = true;
  eta     = true;
  logic   = Some `Full;
  modpath = true;
  user    = true;
}

let no_red = {
  beta    = false;
  delta_p = EcUtils.pred0;
  delta_h = EcUtils.pred0;
  zeta    = false;
  iota    = false;
  eta     = false;
  logic   = None;
  modpath = false;
  user    = false;
}

let beta_red     = { no_red with beta = true; }
let betaiota_red = { no_red with beta = true; iota = true; }

let nodelta =
  { full_red with
      delta_h = EcUtils.pred0;
      delta_p = EcUtils.pred0; }

let delta = { no_red with delta_p = EcUtils.predT; }

let reduce_local ri hyps x  =
  if   ri.delta_h x
  then LDecl.unfold x hyps
  else raise NotReducible

let reduce_op ri env p tys =
  if   ri.delta_p p
  then Op.reduce env p tys
  else raise NotReducible

let is_record env f =
  match EcFol.destr_app f with
  | { f_node = Fop (p, _) }, _ -> EcEnv.Op.is_record_ctor env p
  | _ -> false

(* -------------------------------------------------------------------- *)
type convertible = bool
exception ConvError


type zlet_kind = ZLK_x | ZLK_in

type zapp_kind =
  | ZAF_app
  | ZAF_tuple
  | ZAF_if
  | ZAF_proj     of int
  | ZAF_hoareF   of hoareF * hoareF
  | ZAF_hoareS   of hoareS * hoareS
  | ZAF_bdhoareF of bdHoareF * bdHoareF
  | ZAF_bdhoareS of bdHoareS * bdHoareS
  | ZAF_equivF   of equivF * equivF
  | ZAF_equivS   of equivS * equivS
  | ZAF_eagerF   of eagerF * eagerF
  | ZAF_pr       of pr * pr

type zhoare_kind =
  | ZHK_pre
  | ZHK_post

type zbdhoare_kind =
  | ZBHK_pre
  | ZBHK_post
  | ZBHK_bound

type zpr_kind =
  | ZPK_arg
  | ZPK_event

type zipper =
  | Zempty
  | Zbind of quantif * bindings * bindings * env * f_subst * zipper
  | Zlet  of zlet_kind * lpattern * form *
                         lpattern * form * env * f_subst * zipper
  | Zapp of zapp_kind * form list * form list * ty *
                        form list * form list * ty * zipper

let rec pp_zip pp_hole1 pp_hole2 fmt = function
  | Zempty -> Format.fprintf fmt "%a, %a" pp_hole1 () pp_hole2 ()
  | Zbind (q,bd1, bd2, _env, _s, z) ->
    let sq, sv = Debug.pp_q q in
    let pp_hole pp_h bd fmt () =
      Format.fprintf fmt "@[(%s %a%s@ %a)@]" sq Debug.pp_bindings bd sv pp_h () in
    pp_zip (pp_hole pp_hole1 bd1) (pp_hole pp_hole2 bd2) fmt z
  | Zlet (k, _lp1, f1, _lp2, f2, _env, _s, z) ->
    let pp_hole pp_h f fmt () =
      if k = ZLK_x then
        Format.fprintf fmt "@[let _ = %a in@ %a@]" pp_h () Debug.pp_form f
      else
        Format.fprintf fmt "@[let _ = %a in@ %a@]" Debug.pp_form f pp_h ()
    in
    pp_zip (pp_hole pp_hole1 f1) (pp_hole pp_hole2 f2) fmt z

  | Zapp(k, ra1, a1, _, ra2, a2, _, z) ->

    let pp_k = function
      | ZAF_app -> "@"
      | ZAF_tuple -> "()"
      | ZAF_if    -> "if"
      | ZAF_proj i -> Format.sprintf ".%i" i
      | ZAF_hoareF _ -> "hoareF"
      | ZAF_hoareS _ -> "hoareS"
      | ZAF_bdhoareF _ -> "bdHoareF"
      | ZAF_bdhoareS _ -> "bdHoareS"
      | ZAF_equivF   _ -> "equivF"
      | ZAF_equivS   _ -> "equivS"
      | ZAF_eagerF   _ -> "eagerF"
      | ZAF_pr       _ -> "Pr" in

    let pp_hole pp_h ra a fmt () =
      let pp_ra fmt ra =
        if ra = [] then ()
        else Format.fprintf fmt "%a@ " (Debug.pp_list "@ " Debug.pp_form) (List.rev ra) in
      let pp_a fmt a =
        if a = [] then ()
        else Format.fprintf fmt "@ %a" (Debug.pp_list "@ " Debug.pp_form) a in
      Format.fprintf fmt "@[%s(%a%a%a)@]" (pp_k k) pp_ra ra pp_h () pp_a a in
    pp_zip (pp_hole pp_hole1 ra1 a1) (pp_hole pp_hole2 ra2 a2) fmt z




let pp_zip =
  let pp_h fmt () = Format.fprintf fmt "[]" in
  pp_zip pp_h pp_h

let zip_empty = Zempty

let zip_bind q bd1 bd2 env subst zip =
  Zbind (q, bd1, bd2, env, subst, zip)

let zip_let p1 g1 p2 g2 env subst zip =
  Zlet (ZLK_x, p1, g1, p2, g2, env, subst, zip)

let zip_args args1 ty1 args2 ty2 zip =
  Zapp(ZAF_app, [], args1, ty1, [], args2, ty2, zip)

let zip_tuple args1 ty1 args2 ty2 zip =
  Zapp(ZAF_tuple, [], args1, ty1, [], args2, ty2, zip)

let zip_if b1 b2 c1 c2 zip =
  Zapp(ZAF_if, [], [b1; b2], tbool, [], [c1;c2], tbool, zip)

let zip_proj i ty1 ty2 zip =
  Zapp(ZAF_proj i, [], [], ty1, [], [], ty2, zip)

let zip_hoareF hf1 hf2 zip =
  Zapp(ZAF_hoareF(hf1, hf2),
       [], [hf1.hf_po], tbool,
       [], [hf2.hf_po], tbool, zip)

let zip_hoareS hs1 hs2 zip =
  Zapp(ZAF_hoareS(hs1, hs2),
       [], [hs1.hs_po], tbool,
       [], [hs2.hs_po], tbool, zip)

let zip_bdhoareF hf1 hf2 zip =
  Zapp(ZAF_bdhoareF(hf1, hf2),
       [], [hf1.bhf_po; hf1.bhf_bd], tbool,
       [], [hf2.bhf_po; hf1.bhf_bd], tbool, zip)

let zip_bdhoareS hs1 hs2 zip =
  Zapp(ZAF_bdhoareS(hs1, hs2),
       [], [hs1.bhs_po; hs1.bhs_bd], tbool,
       [], [hs2.bhs_po; hs1.bhs_bd], tbool, zip)

let zip_equivF hf1 hf2 zip =
  Zapp(ZAF_equivF(hf1, hf2),
       [], [hf1.ef_po], tbool,
       [], [hf2.ef_po], tbool, zip)

let zip_equivS hs1 hs2 zip =
  Zapp(ZAF_equivS(hs1, hs2),
       [], [hs1.es_po], tbool,
       [], [hs2.es_po], tbool, zip)

let zip_eagerF hf1 hf2 zip =
  Zapp(ZAF_eagerF(hf1, hf2),
       [], [hf1.eg_po], tbool,
       [], [hf2.eg_po], tbool, zip)

let zip_pr pr1 pr2 zip =
  Zapp(ZAF_pr(pr1, pr2),
       [], [pr1.pr_event], treal,
       [], [pr2.pr_event], treal, zip)

let is_zapp_fun zip =
  match zip with
  | Zapp (ZAF_app, [], _, _, [], _, _, _) -> true
  | _ -> false

let mk_app k ra1 a1 as1 ty1 ra2 a2 as2 ty2 =
  let args1 = List.rev_append ra1 (a1::as1) in
  let args2 = List.rev_append ra2 (a2::as2) in
  match k with
  | ZAF_app ->
    let f1, args1 =
      match args1 with
      | [] -> assert false
      | f :: args -> f, args in
    let f2, args2 =
      match args2 with
      | [] -> assert false
      | f :: args -> f, args in
    f_app f1 args1 ty1, f_app f2 args2 ty2

  | ZAF_tuple   -> f_tuple args1, f_tuple args2

  | ZAF_if      ->
    let a1, b1, c1 = as_seq3 args1 in
    let a2, b2, c2 = as_seq3 args2 in
    f_if a1 b1 c1, f_if a2 b2 c2

  | ZAF_proj i ->
    let f1 = as_seq1 args1 in
    let f2 = as_seq1 args2 in
    f_proj f1 i ty1, f_proj f2 i ty2

  | ZAF_hoareF(hf1, hf2) ->
    let pr1, po1 = as_seq2 args1 in
    let pr2, po2 = as_seq2 args2 in
    f_hoareF_r {hf1 with hf_pr = pr1; hf_po = po1 },
    f_hoareF_r {hf2 with hf_pr = pr2; hf_po = po2 }

  | ZAF_hoareS(hs1, hs2) ->
    let pr1, po1 = as_seq2 args1 in
    let pr2, po2 = as_seq2 args2 in
    f_hoareS_r {hs1 with hs_pr = pr1; hs_po = po1 },
    f_hoareS_r {hs2 with hs_pr = pr2; hs_po = po2 }


  | ZAF_bdhoareF(hf1, hf2) ->
    let pr1, po1, bd1 = as_seq3 args1 in
    let pr2, po2, bd2 = as_seq3 args2 in
    f_bdHoareF_r {hf1 with bhf_pr = pr1; bhf_po = po1; bhf_bd = bd1 },
    f_bdHoareF_r {hf2 with bhf_pr = pr2; bhf_po = po2; bhf_bd = bd2 }

  | ZAF_bdhoareS(hs1, hs2) ->
    let pr1, po1, bd1 = as_seq3 args1 in
    let pr2, po2, bd2 = as_seq3 args2 in
    f_bdHoareS_r {hs1 with bhs_pr = pr1; bhs_po = po1; bhs_bd = bd1 },
    f_bdHoareS_r {hs2 with bhs_pr = pr2; bhs_po = po2; bhs_bd = bd2 }

  | ZAF_equivF(hf1, hf2) ->
    let pr1, po1 = as_seq2 args1 in
    let pr2, po2 = as_seq2 args2 in
    f_equivF_r {hf1 with ef_pr = pr1; ef_po = po1 },
    f_equivF_r {hf2 with ef_pr = pr2; ef_po = po2 }

  | ZAF_equivS(hs1, hs2) ->
    let pr1, po1 = as_seq2 args1 in
    let pr2, po2 = as_seq2 args2 in
    f_equivS_r {hs1 with es_pr = pr1; es_po = po1 },
    f_equivS_r {hs2 with es_pr = pr2; es_po = po2 }

  | ZAF_eagerF(hf1, hf2) ->
    let pr1, po1 = as_seq2 args1 in
    let pr2, po2 = as_seq2 args2 in
    f_eagerF_r {hf1 with eg_pr = pr1; eg_po = po1 },
    f_eagerF_r {hf2 with eg_pr = pr2; eg_po = po2 }

  | ZAF_pr(pr1, pr2) ->
    let a1, e1 = as_seq2 args1 in
    let a2, e2 = as_seq2 args2 in
    f_pr_r { pr1 with pr_args = a1; pr_event = e1 },
    f_pr_r { pr2 with pr_args = a2; pr_event = e2 }

(* -------------------------------------------------------------------- *)
let need_reduce_args = ref false

let rec h_red_x ri env hyps f =
  match f.f_node with
   (* bindings reduction *)
  | Fquant (Lforall as t, b, f1)
  | Fquant (Lexists as t, b, f1) -> begin
      let ctor =
        match t, ri.logic with
        | Lforall, Some `Full -> f_forall_simpl
        | Lforall, _          -> f_forall
        | Lexists, Some `Full -> f_exists_simpl
        | Lexists, _          -> f_exists
        | Llambda, _          -> assert false in

      (* FIXME: this is not head reduction *)
      try
        let env = Mod.add_mod_binding b env in
          ctor b (h_red_x ri env hyps f1)
      with NotReducible ->
      let f' = ctor b f1 in
      if f_equal f f' then raise NotReducible else f'
    end

    (* β-reduction *)
  | Fapp ({ f_node = Fquant (Llambda, _, _)}, _) when ri.beta ->
      f_betared f

    (* ζ-reduction *)
  | Flocal x -> reduce_local ri hyps x

    (* ζ-reduction *)
  | Fapp ({ f_node = Flocal x }, args) ->
      f_app_simpl (reduce_local ri hyps x) args f.f_ty

    (* ζ-reduction *)
  | Flet (LSymbol(x,_), e1, e2) when ri.zeta ->
      let s = Fsubst.f_bind_local Fsubst.f_subst_id x e1 in
        Fsubst.f_subst s e2

    (* ι-reduction (let-tuple) *)
  | Flet (LTuple ids, { f_node = Ftuple es }, e2) when ri.iota ->
      let s =
        List.fold_left2
          (fun s (x,_) e1 -> Fsubst.f_bind_local s x e1)
          Fsubst.f_subst_id ids es
      in
        Fsubst.f_subst s e2

    (* ι-reduction (let-records) *)
  | Flet (LRecord (_, ids), f1, f2) when ri.iota && is_record env f1 ->
      let args  = snd (EcFol.destr_app f1) in
      let subst =
        List.fold_left2 (fun subst (x, _) e ->
          match x with
          | None   -> subst
          | Some x -> Fsubst.f_bind_local subst x e)
          Fsubst.f_subst_id ids args
      in
        Fsubst.f_subst subst f2

    (* ι-reduction (records projection) *)
  | Fapp ({ f_node = Fop (p, _); } as f1, args)
      when ri.iota && EcEnv.Op.is_projection env p -> begin
        try
          match args with
          | mk :: args -> begin
              match (odfl mk (h_red_opt ri env hyps mk)).f_node with
              | Fapp ({ f_node = Fop (mkp, _) }, mkargs) ->
                  if not (EcEnv.Op.is_record_ctor env mkp) then
                    raise NotReducible;
                  let v = oget (EcEnv.Op.by_path_opt p env) in
                  let v = proj3_2 (EcDecl.operator_as_proj v) in
                  let v = List.nth mkargs v in
                  f_app (odfl v (h_red_opt ri env hyps v)) args f.f_ty

              | _ -> raise NotReducible
            end
          | _ -> raise NotReducible

        with NotReducible ->
          f_app (h_red_x ri env hyps f1) args f.f_ty
      end

    (* ι-reduction (tuples projection) *)
  | Fproj(f1, i) when ri.iota ->
      let f' = f_proj_simpl f1 i f.f_ty in
      if f_equal f f' then f_proj (h_red_x ri env hyps f1) i f.f_ty else f'

    (* ι-reduction (if-then-else) *)
  | Fif (f1, f2, f3) when ri.iota ->
      let f' = f_if_simpl f1 f2 f3 in
      if f_equal f f' then f_if (h_red_x ri env hyps f1) f2 f3 else f'

    (* μ-reduction *)
  | Fglob (mp, m) when ri.modpath ->
      let f' = EcEnv.NormMp.norm_glob env m mp in
        if f_equal f f' then raise NotReducible else f'

    (* μ-reduction *)
  | Fpvar (pv, m) when ri.modpath ->
      let pv' = EcEnv.NormMp.norm_pvar env pv in
        if pv_equal pv pv' then raise NotReducible else f_pvar pv' f.f_ty m

    (* η-reduction *)
  | Fquant (Llambda, [x, GTty _], { f_node = Fapp (fn, args) })
      when ri.eta && can_eta x (fn, args)
    -> f_app fn (List.take (List.length args - 1) args) f.f_ty

  | Fapp ({f_node = Fop _} , _) ->
    reduce_op_app ri env hyps f

  | Fop _ ->
    reduce_op_app ri env hyps f

  | _ -> raise NotReducible

and reduce_op_app ri env hyps f =
  need_reduce_args := false;

  let strategies =
    [ reduce_logic;
      reduce_user ~mode:`BeforeFix;
      reduce_fix;
      reduce_user ~mode:`AfterFix ;
      reduce_delta;
    ] in
  let r =
    List.Exceptionless.find_map
      (fun strategy ->
        try Some (strategy ri env hyps f) with NotReducible -> None)
      strategies in
  match r with
  | Some f' -> f'
  | None ->
    if not !need_reduce_args then raise NotReducible;
    let f1, args = destr_app f in
    let args' =
      List.Smart.map
        (fun f -> try h_red_x ri env hyps f with NotReducible -> f) args in
    if args == args' then raise NotReducible;
    f_app f1 args' f.f_ty

(* ι-reduction (match-fix) *)
and reduce_fix ri env _hyps f =
  let ((p, tys), fargs) = destr_op_app f in
  if not (ri.iota && EcEnv.Op.is_fix_def env p) then raise NotReducible;
  let op  = oget (EcEnv.Op.by_path_opt p env) in
  let fix = EcDecl.operator_as_fix op in

  if List.length fargs < snd (fix.EcDecl.opf_struct) then
    raise NotReducible;

  let fargs, eargs = List.split_at (snd (fix.EcDecl.opf_struct)) fargs in

  let args  = Array.of_list fargs in

  let pargs = List.fold_left (fun (opb, acc) v ->
    let v = args.(v) in
    match fst_map (fun x -> x.f_node) (EcFol.destr_app v) with
    | (Fop (p, _), cargs) when EcEnv.Op.is_dtype_ctor env p -> begin
        let idx = EcEnv.Op.by_path p env in
        let idx = snd (EcDecl.operator_as_ctor idx) in
        match opb with
        | EcDecl.OPB_Leaf   _  -> assert false
        | EcDecl.OPB_Branch bs ->
          ((Parray.get bs idx).EcDecl.opb_sub, cargs :: acc)
      end
    | _ -> need_reduce_args := true;raise NotReducible)
       (fix.EcDecl.opf_branches, []) (fst fix.EcDecl.opf_struct)
  in

  let pargs, (bds, body) =
    match pargs with
    | EcDecl.OPB_Leaf (bds, body), cargs -> (List.rev cargs, (bds, body))
    | _ -> assert false
  in

  let subst =
    List.fold_left2
      (fun subst (x, _) fa -> Fsubst.f_bind_local subst x fa)
      Fsubst.f_subst_id fix.EcDecl.opf_args fargs in

  let subst =
    List.fold_left2
      (fun subst bds cargs ->
        List.fold_left2
          (fun subst (x, _) fa -> Fsubst.f_bind_local subst x fa)
          subst bds cargs)
      subst bds pargs in

  let body = EcFol.form_of_expr EcFol.mhr body in
  let body =
    EcFol.Fsubst.subst_tvar
      (EcTypes.Tvar.init (List.map fst op.EcDecl.op_tparams) tys) body in

  f_app (Fsubst.f_subst subst body) eargs f.f_ty

and reduce_logic ri env hyps f =
  let ((p, _tys), args) = destr_op_app f in
  if not (is_some ri.logic && is_logical_op p) then raise NotReducible;
  let pcompat =
    match oget ri.logic with `Full -> true | `ProductCompat -> false
  in

  let f' =
    match op_kind p, args with
    | Some (`Not), [f1]    when pcompat -> f_not_simpl f1
    | Some (`Imp), [f1;f2] when pcompat -> f_imp_simpl f1 f2
    | Some (`Iff), [f1;f2] when pcompat -> f_iff_simpl f1 f2

    | Some (`And `Asym), [f1;f2] -> f_anda_simpl f1 f2
    | Some (`Or  `Asym), [f1;f2] -> f_ora_simpl f1 f2
    | Some (`And `Sym ), [f1;f2] -> f_and_simpl f1 f2
    | Some (`Or  `Sym ), [f1;f2] -> f_or_simpl f1 f2
    | Some (`Int_le   ), [f1;f2] -> f_int_le_simpl f1 f2
    | Some (`Int_lt   ), [f1;f2] -> f_int_lt_simpl f1 f2
    | Some (`Real_le  ), [f1;f2] -> f_real_le_simpl f1 f2
    | Some (`Real_lt  ), [f1;f2] -> f_real_lt_simpl f1 f2
    | Some (`Int_add  ), [f1;f2] -> f_int_add_simpl f1 f2
    | Some (`Int_opp  ), [f]     -> f_int_opp_simpl f
    | Some (`Int_mul  ), [f1;f2] -> f_int_mul_simpl f1 f2
    | Some (`Int_edivz), [f1;f2] -> f_int_edivz_simpl f1 f2
    | Some (`Real_add ), [f1;f2] -> f_real_add_simpl f1 f2
    | Some (`Real_opp ), [f]     -> f_real_opp_simpl f
    | Some (`Real_mul ), [f1;f2] -> f_real_mul_simpl f1 f2
    | Some (`Real_inv ), [f]     -> f_real_inv_simpl f
    | Some (`Eq       ), [f1;f2] -> begin
        match fst_map f_node (destr_app f1), fst_map f_node (destr_app f2) with
        | (Fop (p1, _), args1), (Fop (p2, _), args2)
            when EcEnv.Op.is_dtype_ctor env p1
                 && EcEnv.Op.is_dtype_ctor env p2 ->

          let idx p =
            let idx = EcEnv.Op.by_path p env in
            snd (EcDecl.operator_as_ctor idx)
          in
          if   idx p1 <> idx p2
          then f_false
          else f_ands (List.map2 f_eq args1 args2)

        | (_, []), (_, [])
            when EqTest.for_type env f1.f_ty EcTypes.tunit
                 && EqTest.for_type env f2.f_ty EcTypes.tunit ->

          f_true

        | _ ->
          if   f_equal f1 f2 || is_alpha_eq hyps f1 f2
          then f_true
          else f_eq_simpl f1 f2
      end

    | _ -> raise NotReducible
  in
  if f_equal f f' then (need_reduce_args := true; raise NotReducible);
  f'

and reduce_delta ri env _hyps f =
  let ((p, tys), args) = destr_op_app f in
  if not (ri.delta_p p) then raise NotReducible;
  let op = reduce_op ri env p tys in
  f_app_simpl op args f.f_ty

and reduce_user_gen mode simplify ri env hyps f =
  if not ri.user then raise NotReducible;

  let p =
    match f_node (fst (destr_app f)) with
    | Fop (p, _) -> `Path p
    | Ftuple _   -> `Tuple
    | _ -> raise NotReducible in

  let module R = EcTheory in

  let try_rule rule =
    need_reduce_args := true;
    try
      let ue  = EcUnify.UniEnv.create None in
      let tvi = EcUnify.UniEnv.opentvi ue rule.R.rl_tyd None in
      let pv  = ref Mid.empty in
      let rec doit f ptn =
        match destr_app f, ptn with
        | ({ f_node = Fop (p, tys) }, args), R.Rule (`Op (p', tys'), args')
            when EcPath.p_equal p p' && List.length args = List.length args' ->

          let tys' = List.map (EcTypes.Tvar.subst tvi) tys' in

          begin
            try  List.iter2 (EcUnify.unify env ue) tys tys'
            with EcUnify.UnificationFailure _ -> raise NotReducible end;

          List.iter2 doit args args'

        | ({ f_node = Ftuple args} , []), R.Rule (`Tuple, args')
            when List.length args = List.length args' ->

          List.iter2 doit args args'

        | ({ f_node = Fint i }, []), R.Int j when EcBigInt.equal i j ->
          ()

        | _, R.Var x -> begin
          match Mid.find_opt x !pv with
          | None    -> pv := Mid.add x f !pv
          | Some f' -> check_alpha_equal ri hyps f f'
          end

        | _ -> raise NotReducible in

      doit f rule.R.rl_ptn;

      if not (EcUnify.UniEnv.closed ue) then
        raise NotReducible;

      let subst f =
        let tysubst = { ty_subst_id with ts_u = EcUnify.UniEnv.assubst ue } in
        let subst   = Fsubst.f_subst_init ~sty:tysubst () in
        let subst   = Mid.fold (fun x f s -> Fsubst.f_bind_local s x f) !pv subst in
        Fsubst.f_subst subst (Fsubst.subst_tvar tvi f)
      in

      List.iter (fun cond ->
        if not (f_equal (simplify (subst cond)) f_true) then
          raise NotReducible)
        rule.R.rl_cond;

      Some (subst rule.R.rl_tg)

    with NotReducible -> None in

  let get_rules _p rules = List.Exceptionless.find_map try_rule rules in

  let rules =
    let ri = EcEnv.Reduction.get p env in
    match mode with
    | `BeforeFix -> ri.ri_before_fix
    | `AfterFix  -> ri.ri_after_fix in

  oget ~exn:NotReducible (EcMaps.Mint.find_map get_rules rules)

and reduce_user ~mode ri env hyps f =
  reduce_user_gen mode (simplify ri env hyps) ri env hyps f

and can_eta x (f, args) =
  match List.rev args with
  | { f_node = Flocal y } :: args ->
      let check v = not (Mid.mem x v.f_fv) in
      id_equal x y && List.for_all check (f :: args)
  | _ -> false

and h_red_opt ri env hyps f =
  try Some (h_red_x ri env hyps f)
  with NotReducible -> None

and check_alpha_equal ri hyps f1 f2 =
  let env = LDecl.toenv hyps in
  let exn = IncompatibleForm (env, (f1, f2)) in
  (* eta is performed by the conversion directly *)
  let ri = { ri with eta = false} in


  let error () = raise ConvError in
  let ensure t = if not t then error () in

  let check_ty env subst ty1 ty2 =
    EqTest.for_type env ty1 (subst.fs_ty ty2) in

  let e_check_ty env subst ty1 ty2 =
    ensure (check_ty env subst ty1 ty2) in

  let add_local (env, subst) (x1,ty1) (x2,ty2) =
    e_check_ty env subst ty1 ty2;
    env,
    if id_equal x1 x2 then subst
    else Fsubst.f_bind_rename subst x2 x1 ty1 in

  let check_lpattern env subst lp1 lp2 =
    match lp1, lp2 with
    | LSymbol xt1, LSymbol xt2 -> add_local (env, subst) xt1 xt2
    | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
      List.fold_left2 add_local (env,subst) lid1 lid2
    | _, _ -> error() in

  let check_memtype env mt1 mt2 =
    match mt1, mt2 with
    | None, None -> ()
    | Some lmt1, Some lmt2 ->
      let xp1, xp2 = EcMemory.lmt_xpath lmt1, EcMemory.lmt_xpath lmt2 in
      ensure (EqTest.for_xp env xp1 xp2);
      let m1, m2 = EcMemory.lmt_bindings lmt1, EcMemory.lmt_bindings lmt2 in
      ensure (EcSymbols.Msym.equal
                (fun (p1,ty1) (p2,ty2) ->
                  p1 = p2 && EqTest.for_type env ty1 ty2) m1 m2)
    | _, _ -> error () in

  (* TODO all declaration in env, do it also in add local *)
  let check_binding (env, subst) (x1,gty1) (x2,gty2) =
    let gty2 = Fsubst.gty_subst subst gty2 in
    match gty1, gty2 with
    | GTty ty1, GTty ty2 ->
      ensure (EqTest.for_type env ty1 ty2);
      env,
      if id_equal x1 x2 then subst else
        Fsubst.f_bind_rename subst x2 x1 ty1
    | GTmodty (p1, r1) , GTmodty(p2, r2) ->
      ensure (ModTy.mod_type_equiv env p1 p2 &&
                NormMp.equal_restr env r1 r2);
      Mod.bind_local x1 p1 r1 env,
      if id_equal x1 x2 then subst
      else Fsubst.f_bind_mod subst x2 (EcPath.mident x1)
    | GTmem   me1, GTmem me2  ->
      check_memtype env me1 me2;
      env,
      if id_equal x1 x2 then subst
      else Fsubst.f_bind_mem subst x2 x1
    | _, _ -> error () in

  let rec check_bindings env subst bd1 bd2 =
    List.fold_left2 check_binding (env, subst) bd1 bd2 in

  let check_local subst id1 f2 id2 =
    match (Mid.find_def f2 id2 subst.fs_loc).f_node with
    | Flocal id2 -> EcIdent.id_equal id1 id2
    | _ -> assert false in

  let check_mem subst m1 m2 =
    let m2 = Mid.find_def m2 m2 subst.fs_mem in
    EcIdent.id_equal m1 m2 in

  let check_pv env subst pv1 pv2 =
    let pv2 = pv_subst (EcPath.x_substm subst.fs_sty.ts_p subst.fs_mp) pv2 in
    EqTest.for_pv env pv1 pv2 in

  let check_mp env subst mp1 mp2 =
    let mp2 = EcPath.m_subst subst.fs_sty.ts_p subst.fs_mp mp2 in
    EqTest.for_mp env mp1 mp2 in

  let check_xp env subst xp1 xp2 =
    let xp2 = EcPath.x_substm subst.fs_sty.ts_p subst.fs_mp xp2 in
    EqTest.for_xp env xp1 xp2 in

  let check_s env s s1 s2 =
    let es = e_subst_init s.fs_freshen s.fs_sty.ts_p
                          s.fs_ty Mp.empty s.fs_mp s.fs_esloc in
    let s2 = EcModules.s_subst es s2 in
    EqTest.for_stmt env s1 s2 in

  let rec check_head env subst f1 f2 zip =
    if Fsubst.is_subst_id subst && f_equal f1 f2 then
      unzip env subst true f1 f2 zip
    else

    match f1.f_node, f2.f_node with
    | Fquant(q1,bd1,f1'), Fquant(q2,bd2,f2') when
        q1 = q2 && List.length bd1 = List.length bd2 ->
      begin match check_bindings env subst bd1 bd2 with
      | (env', subst') ->
        check_head env' subst' f1' f2' (zip_bind q1 bd1 bd2 env subst zip)
      | exception ConvError ->
        unzip_red env subst false f1 f2 zip
      end

    | Fif(a1,b1,c1), Fif(a2,b2,c2) ->
      check_head env subst a1 a2 (zip_if b1 c1 b2 c2 zip)

    | Flet(p1,f1',g1), Flet(p2,f2',g2) ->
      begin match check_lpattern env subst p1 p2 with
      | (env', subst') ->
        check_head env subst f1' f2' (zip_let p1 g1 p2 g2 env' subst' zip)
      | exception ConvError ->
        unzip_red env subst false f1 f2 zip
      end

    | Fint i1, Fint i2 ->
      unzip env subst (EcBigInt.equal i1 i2) f1 f2 zip

    | Flocal id1, Flocal id2 ->
      unzip_red env subst (check_local subst id1 f2 id2) f1 f2 zip

    | Fpvar(p1,m1), Fpvar(p2,m2) ->
      unzip_red env subst
        (check_mem subst m1 m2 && check_pv env subst p1 p2) f1 f2 zip

    | Fglob(p1,m1), Fglob(p2,m2) ->
      unzip_red env subst
        (check_mem subst m1 m2 && check_mp env subst p1 p2) f1 f2 zip

    | Fop(p1, ty1), Fop(p2, ty2) ->
      unzip_red env subst
        (EcPath.p_equal p1 p2 && List.for_all2 (check_ty env subst) ty1 ty2)
        f1 f2 zip

    | Fapp(f1',args1), Fapp(f2',args2) ->
      if List.length args1 = List.length args2 then
        check_head env subst f1' f2' (zip_args args1 f1.f_ty args2 f2.f_ty zip)
      else
        unzip_red env subst false f1 f2 zip

    | Ftuple [], Ftuple [] ->
      unzip env subst true f1 f2 zip

    | Ftuple (f1'::args1), Ftuple (f2'::args2) ->
      if List.length args1 = List.length args2 then
        check_head env subst f1' f2' (zip_tuple args1 f1.f_ty args2 f2.f_ty zip)
      else
        unzip env subst false f1 f2 zip

    | Fproj(f1',i1), Fproj(f2',i2) ->
      if i1 = i2 then
        check_head env subst f1' f2' (zip_proj i1 f1.f_ty f2.f_ty zip)
      else
        unzip_red env subst false f1 f2 zip

    | FhoareF hf1, FhoareF hf2 ->
      if check_xp env subst hf1.hf_f hf2.hf_f then
        check_head env subst hf1.hf_pr hf2.hf_pr (zip_hoareF hf1 hf2 zip)
      else unzip env subst false f1 f2 zip

    | FhoareS hs1, FhoareS hs2 ->
      if check_s env subst hs1.hs_s hs2.hs_s then
        (* FIXME should check the memenv *)
        check_head env subst hs1.hs_pr hs2.hs_pr (zip_hoareS hs1 hs2 zip)
      else unzip env subst false f1 f2 zip

    | FbdHoareF hf1, FbdHoareF hf2 ->
      if hf1.bhf_cmp = hf2.bhf_cmp &&
         check_xp env subst hf1.bhf_f hf2.bhf_f then
        check_head env subst hf1.bhf_pr hf2.bhf_pr (zip_bdhoareF hf1 hf2 zip)
      else unzip env subst false f1 f2 zip

    | FbdHoareS hs1, FbdHoareS hs2 ->
      if hs1.bhs_cmp = hs2.bhs_cmp &&
         check_s env subst hs1.bhs_s hs2.bhs_s then
        (* FIXME should check the memenv *)
        check_head env subst hs1.bhs_pr hs2.bhs_pr (zip_bdhoareS hs1 hs2 zip)
      else unzip env subst false f1 f2 zip

    | FequivF ef1, FequivF ef2 ->
      if check_xp env subst ef1.ef_fl ef2.ef_fl &&
         check_xp env subst ef1.ef_fr ef2.ef_fr then
        check_head env subst ef1.ef_pr ef2.ef_pr (zip_equivF ef1 ef2 zip)
      else unzip env subst false f1 f2 zip

    | FequivS es1, FequivS es2 ->
      if check_s env subst es1.es_sl es2.es_sl &&
         check_s env subst es1.es_sr es2.es_sr then
        (* FIXME should check the memenv *)
        check_head env subst es1.es_pr es2.es_pr (zip_equivS es1 es2 zip)
      else unzip env subst false f1 f2 zip

    | FeagerF eg1, FeagerF eg2 ->
      if check_xp env subst eg1.eg_fl eg2.eg_fl &&
         check_xp env subst eg1.eg_fr eg2.eg_fr &&
         check_s env subst eg1.eg_sl eg2.eg_sl &&
         check_s env subst eg1.eg_sr eg2.eg_sr then
        check_head env subst eg1.eg_pr eg2.eg_pr (zip_eagerF eg1 eg2 zip)
      else unzip env subst false f1 f2 zip

    | Fpr pr1, Fpr pr2 ->
      if check_mem subst pr1.pr_mem pr2.pr_mem &&
         check_xp env subst pr1.pr_fun pr2.pr_fun then
        check_head env subst pr1.pr_args pr2.pr_args (zip_pr pr1 pr2 zip)
      else unzip env subst false f1 f2 zip

    | _, _ ->
      unzip_red env subst false f1 f2 zip

  and unzip env subst conv f1 f2 zip =
    match zip with
    | Zempty ->
      if conv then ()
      else raise exn

    | Zbind(q,bd1,bd2,env,subst, zip) ->
      let f1 = f_quant q bd1 f1 in
      let f2 = f_quant q bd2 f2 in
      unzip_red env subst conv f1 f2 zip

    | Zlet(ZLK_x, p1, in1, p2, in2, env', subst', zip) ->
      if conv then
        check_head env' subst' in1 in2
          (Zlet(ZLK_in, p1, f1, p2, f2, env, subst, zip))
      else
        let f1 = f_let p1 f1 in1 in
        let f2 = f_let p2 f2 in2 in
        unzip_red env subst conv f1 f2 zip

    | Zlet(ZLK_in, p1, x1, p2, x2, env', subst', zip) ->
      let f1 = f_let p1 x1 f1 in
      let f2 = f_let p2 x2 f2 in
      unzip_red env' subst' conv f1 f2 zip

    | Zapp(k, ra1, as1, ty1, ra2, as2, ty2, zip) ->
      if conv then
        match as1, as2 with
        | [], [] ->
          let f1, f2 = mk_app k ra1 f1 as1 ty1 ra2 f2 as2 ty2 in
          unzip env subst conv f1 f2 zip
        | a1::as1, a2::as2 ->
          let zip =
            Zapp(k, f1::ra1, as1, ty1, f2::ra2, as2, ty2, zip) in
          check_head env subst a1 a2 zip
        | _, _ -> assert false
      else
        let f1, f2 = mk_app k ra1 f1 as1 ty1 ra2 f2 as2 ty2 in
        unzip_red env subst conv f1 f2 zip

  and unzip_red env subst conv f1 f2 zip =
    if conv || is_zapp_fun zip then unzip env subst conv f1 f2 zip
    else begin
    match h_red_opt ri env hyps f1 with
    | Some f1 ->
      check_head env subst f1 f2 zip
    | None ->
      match h_red_opt ri env hyps f2 with
      | Some f2 ->
        check_head env subst f1 f2 zip
      | None ->
        let nb_lambda f =
          match f.f_node with
          | Fquant(Llambda, bd, _) -> List.length bd
          | _ -> 0 in
        if not (nb_lambda f1 = nb_lambda f2) &&
             check_ty env subst f1.f_ty f2.f_ty then
          (* At least one is greater than 0 *)
          let dom1, codom1 = EcEnv.Ty.decompose_fun f1.f_ty env in
          let dom2, codom2 = EcEnv.Ty.decompose_fun f2.f_ty env in
          assert (List.length dom1 = List.length dom2);
          let mk_b ty = EcIdent.create "_", ty in
          let bd1 = List.map mk_b dom1 in
          let bd2 = List.map mk_b dom2 in
          let mk_a (x,ty) = f_local x ty in
          let args1 = List.map mk_a bd1 in
          let args2 = List.map mk_a bd2 in
          let mk_bd (x,ty) = x, GTty ty in
          let bd1 = List.map mk_bd bd1 in
          let bd2 = List.map mk_bd bd2 in
          let f1 = f_lambda bd1 (f_app_simpl f1 args1 codom1) in
          let f2 = f_lambda bd2 (f_app_simpl f2 args2 codom2) in
          check_head env subst f1 f2 zip
        else
          unzip env subst conv f1 f2 zip
         end in

  check_head env Fsubst.f_subst_id f1 f2 Zempty

and check_alpha_eq f1 f2 = check_alpha_equal no_red   f1 f2

and check_conv ?redinfo f1 f2 =
  let ri = odfl full_red redinfo in
  check_alpha_equal ri f1 f2

and is_alpha_eq hyps f1 f2 =
  try check_alpha_eq hyps f1 f2; true
  with _ -> false

and simplify ri env hyps f =
  let f' = try h_red_x ri env hyps f with NotReducible -> f in
  if   f == f'
  then simplify_rec ri env hyps f
  else simplify ri env hyps f'

and simplify_rec ri env hyps f =
  match f.f_node with

  | FhoareF hf when ri.modpath ->
      let hf_f = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) hf.hf_f in
      f_map (fun ty -> ty) (simplify ri env hyps) (f_hoareF_r { hf with hf_f })

  | FbdHoareF hf when ri.modpath ->
      let bhf_f = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) hf.bhf_f in
      f_map (fun ty -> ty) (simplify ri env hyps) (f_bdHoareF_r { hf with bhf_f })

  | FequivF ef when ri.modpath ->
      let ef_fl = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) ef.ef_fl in
      let ef_fr = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) ef.ef_fr in
      f_map (fun ty -> ty) (simplify ri env hyps) (f_equivF_r { ef with ef_fl; ef_fr; })

  | FeagerF eg when ri.modpath ->
      let eg_fl = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) eg.eg_fl in
      let eg_fr = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) eg.eg_fr in
      f_map (fun ty -> ty) (simplify ri env hyps) (f_eagerF_r { eg with eg_fl ; eg_fr; })

  | Fpr pr  when ri.modpath ->
      let pr_fun = EcEnv.NormMp.norm_xfun (LDecl.toenv hyps) pr.pr_fun in
      f_map (fun ty -> ty) (simplify ri env hyps) (f_pr_r { pr with pr_fun })

  | _ ->
    let f' = f_map (fun ty -> ty) (simplify ri env hyps) f in
    if f == f' then f
    else
      let f'' = try h_red_x ri env hyps f' with NotReducible -> f' in
      if f' == f'' then f'
      else simplify ri env hyps f''

(* -------------------------------------------------------------------- *)
let is_conv ?redinfo hyps f1 f2 =
  try check_conv ?redinfo hyps f1 f2; true with _ -> false

let h_red ri hyps f =
   h_red_x ri (LDecl.toenv hyps) hyps f

let h_red_opt ri hyps f =
  h_red_opt ri (LDecl.toenv hyps) hyps f

let simplify ri hyps f =
  simplify ri (LDecl.toenv hyps) hyps f

(* -------------------------------------------------------------------- *)
type xconv = [`Eq | `AlphaEq | `Conv]

let xconv (mode : xconv) hyps =
  match mode with
  | `Eq      -> f_equal
  | `AlphaEq -> is_alpha_eq hyps
  | `Conv    -> is_conv hyps

(* -------------------------------------------------------------------- *)
module User = struct
  type options = EcTheory.rule_option

  type error =
    | MissingVarInLhs   of EcIdent.t
    | MissingTyVarInLhs of EcIdent.t
    | NotAnEq
    | NotFirstOrder
    | RuleDependsOnMemOrModule
    | HeadedByVar

  exception InvalidUserRule of error

  module R = EcTheory

  type rule = EcEnv.Reduction.rule

  let compile ~opts ~prio (env : EcEnv.env) (p : EcPath.path) =
    let simp =
      if opts.EcTheory.ur_delta then
        let hyps = EcEnv.LDecl.init env [] in
        fun f -> odfl f (h_red_opt delta hyps f)
      else fun f -> f in

    let ax = EcEnv.Ax.by_path p env in
    let bds, rl = EcFol.decompose_forall (simp ax.EcDecl.ax_spec) in

    let bds =
      let filter = function
        | (x, GTty ty) -> (x, ty)
        | _ -> raise (InvalidUserRule RuleDependsOnMemOrModule)
      in List.map filter bds in

    let lhs, rhs, conds =
      try
        let rec doit conds f =
          match sform_of_form (simp f) with
          | SFimp (f1, f2) -> doit (f1 :: conds) f2
          | SFeq  (f1, f2) -> (f1, f2, List.rev conds)
          | _ -> raise (InvalidUserRule NotAnEq)
        in doit [] rl

      with InvalidUserRule NotAnEq
             when opts.EcTheory.ur_eqtrue &&
                  ty_equal tbool (EcEnv.ty_hnorm rl.f_ty env)
           -> (rl, f_true, List.rev [])

    in

    let rule =
      let rec rule (f : form) : EcTheory.rule_pattern =
        match EcFol.destr_app f with
        | { f_node = Fop (p, tys) }, args ->
            R.Rule (`Op (p, tys), List.map rule args)
        | { f_node = Ftuple args }, [] ->
            R.Rule (`Tuple, List.map rule args)
        | { f_node = Fint i }, [] ->
            R.Int i
        | { f_node = Flocal x }, [] ->
            R.Var x
        | _ -> raise (InvalidUserRule NotFirstOrder)
      in rule lhs in

    let lvars, ltyvars =
      let rec doit (lvars, ltyvars) = function
        | R.Var x ->
            (Sid.add x lvars, ltyvars)

        | R.Int _ ->
            (lvars, ltyvars)

        | R.Rule (op, args) ->
            let ltyvars =
              match op with
              | `Op (_, tys) ->
                List.fold_left (
                    let rec doit ltyvars = function
                      | { ty_node = Tvar a } -> Sid.add a ltyvars
                      | _ as ty -> ty_fold doit ltyvars ty in doit)
                  ltyvars tys
              | `Tuple -> ltyvars in
            List.fold_left doit (lvars, ltyvars) args

      in doit (Sid.empty, Sid.empty) rule in

    let mvars   =
      Sid.diff (Sid.of_list (List.map fst bds)) lvars in
    let mtyvars =
      Sid.diff (Sid.of_list (List.map fst ax.EcDecl.ax_tparams)) ltyvars in

    if not (Sid.is_empty mvars) then
      raise (InvalidUserRule (MissingVarInLhs (Sid.choose mvars)));
    if not (Sid.is_empty mtyvars) then
      raise (InvalidUserRule (MissingTyVarInLhs (Sid.choose mtyvars)));

    begin match rule with
    | R.Var _ -> raise (InvalidUserRule (HeadedByVar));
    | _       -> () end;

    R.{ rl_tyd  = ax.EcDecl.ax_tparams;
        rl_vars = bds;
        rl_cond = conds;
        rl_ptn  = rule;
        rl_tg   = rhs;
        rl_prio = prio; }

end
