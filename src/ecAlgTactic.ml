(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcDecl
open EcCoreGoal
open EcAlgebra

(* -------------------------------------------------------------------- *)
module Axioms = struct
  open EcDecl

  let tmod  = EcPath.fromqsymbol ([EcCoreLib.i_top; "AlgTactic"], "Requires")
  let tname = "domain"


  let tmod_and_deps =
    tmod :: [
      EcPath.fromqsymbol ([EcCoreLib.i_top; "Ring"], "Field")
    ]

  let zero  = "rzero"
  let one   = "rone"
  let add   = "add"
  let opp   = "opp"
  let sub   = "sub"
  let mul   = "mul"
  let inv   = "inv"
  let div   = "div"
  let expr  = "expr"
  let embed = "ofint"
  let cN    = "Cn"
  let cP    = "Cp"

  let core_add  = ["oner_neq0"; "addr0"; "addrA"; "addrC";]
  let core_mul  = [ "mulr1"; "mulrA"; "mulrC"; "mulrDl"]
  let core      = core_add @ "addrN" :: core_mul
  let core_bool = core_add @ "addrK" :: "mulrK" :: core_mul

  let ofoppbool = ["oppr_id"]
  let intpow    = ["expr0"; "exprS"]
  let ofint     = ["ofint0"; "ofint1"; "ofintS"; "ofintN"]
  let ofsub     = ["subrE"]
  let field     = ["mulrV"; "exprN"]
  let ofdiv     = ["divrE"]
  let cNax      = ["Cn_eq0"]
  let cPax      = ["Cp_idp"]

  let ty0 ty = ty
  let ty1 ty = tfun ty (ty0 ty)
  let ty2 ty = tfun ty (ty1 ty)

  let ring_symbols env kind ty =
    let reqopp = not (kind = `Boolean) in

    let symbols =
      [(zero, (true  , ty0 ty));
       (one , (true  , ty0 ty));
       (add , (true  , ty2 ty));
       (opp , (reqopp, ty1 ty));
       (sub , (false , ty2 ty));
       (mul , (true  , ty2 ty));
       (expr, (false , toarrow [ty; tint] ty))]
    in
      if   EcReduction.EqTest.for_type env ty tint
      then symbols
      else symbols @ [(embed, (false, tfun tint ty))]

  let field_symbols env ty =
    (ring_symbols env `Integer ty)
      @ [(inv, (true , ty1 ty));
         (div, (false, ty2 ty))]

  let subst_of_ring (cr : ring) =
    let crcore = [(zero, cr.r_zero);
                  (one , cr.r_one );
                  (add , cr.r_add );
                  (mul , cr.r_mul ); ] in

    let xpath  = fun x -> EcPath.pqname tmod x in
    let add    = fun subst x p -> EcSubst.add_path subst ~src:(xpath x) ~dst:p in
    let addctt = fun subst x f -> EcSubst.add_opdef subst (xpath x) ([], f) in

    let subst  =
      EcSubst.add_tydef (EcSubst.empty ()) (xpath tname) ([], cr.r_type) in
    let subst  =
      List.fold_left (fun subst (x, p) -> add subst x p) subst crcore in
    let subst  = odfl subst (cr.r_opp |> omap (fun p -> add subst opp p)) in
    let subst  = odfl subst (cr.r_sub |> omap (fun p -> add subst sub p)) in
    let subst  = odfl subst (cr.r_exp |> omap (fun p -> add subst expr p)) in

    let subst  =
      match cr.r_kind with
      | `Boolean | `Integer -> subst
      | `Modulus (c, p) ->
          let subst = odfl subst (c |> omap (fun c -> addctt subst cN (e_int c))) in
          let subst = odfl subst (p |> omap (fun p -> addctt subst cP (e_int p))) in
          subst
    in

    let subst  =
      match cr.r_embed with
      | `Direct | `Default -> subst
      | `Embed p -> add subst embed p
    in

    subst

  let subst_of_field (cr : field) =
    let xpath  = fun x -> EcPath.pqname tmod x in
    let add    = fun subst x p -> EcSubst.add_path subst ~src:(xpath x) ~dst:p in

    let subst = subst_of_ring cr.f_ring in
    let subst = add subst inv cr.f_inv in
    let subst = odfl subst (cr.f_div |> omap (fun p -> add subst div p)) in
      subst

  (* FIXME: should use operators inlining when available *)
  let get cr env axs =
    let subst  =
      match cr with
      | `Ring  cr -> subst_of_ring  cr
      | `Field cr -> subst_of_field cr
    in

    let for1 axname =
      let ax = EcEnv.Ax.by_path (EcPath.pqname tmod axname) env in
        assert (ax.ax_tparams = [] && is_axiom ax.ax_kind);
        (axname, EcSubst.subst_form subst ax.ax_spec)
    in
      List.map for1 axs

  let getr env cr axs = get (`Ring  cr) env axs
  let getf env cr axs = get (`Field cr) env axs

  let ring_axioms env (cr : ring) =
    let axcore =
      match cr.r_kind with
      | `Boolean   -> getr env cr core_bool
      | `Integer   -> getr env cr core
      | `Modulus _ -> getr env cr core in
    let axint =
      match cr.r_embed with
      | `Direct | `Default -> [] | `Embed _ -> getr env cr ofint in
    let axopp =
      match cr.r_opp with
      | Some _ when cr.r_kind = `Boolean -> getr env cr ofoppbool
      | _ -> [] in
    let axsub =
      match cr.r_sub with None -> [] | Some _ -> getr env cr ofsub in
    let axexp =
      match cr.r_exp with None -> [] | Some _ -> getr env cr intpow in
    let axCnp =
      match cr.r_kind with
      | `Boolean | `Integer -> []

      | `Modulus (c, p) ->
            (odfl [] (c |> omap (fun _ -> getr env cr cNax)))
          @ (odfl [] (p |> omap (fun _ -> getr env cr cPax)))
    in

    List.flatten [axcore; axopp; axexp; axint; axsub; axCnp]

  let field_axioms env (cr : field) =
    let axring = ring_axioms env cr.f_ring in
    let axcore = getf env cr field in
    let axdiv  = match cr.f_div with None -> [] | Some _ -> getf env cr ofdiv in
    List.flatten [axring; axcore; axdiv]

end

let ring_symbols  = Axioms.ring_symbols
let field_symbols = Axioms.field_symbols

let ring_axioms  = Axioms.ring_axioms
let field_axioms = Axioms.field_axioms

(* -------------------------------------------------------------------- *)
let is_module_loaded env =
  List.for_all
    (fun x -> EcEnv.Theory.by_path_opt x env <> None)
    Axioms.tmod_and_deps

(* -------------------------------------------------------------------- *)
let t_ring_simplify cr eqs (f1, f2) tc =
  let hyps = FApi.tc1_hyps tc in
  let cr = cring_of_ring cr in
  let f1 = ring_simplify hyps cr eqs f1 in
  let f2 = ring_simplify hyps cr eqs f2 in
  FApi.xmutate1 tc `Ring [f_eq f1 f2]

let t_ring r eqs (f1, f2) tc =
  let hyps = FApi.tc1_hyps tc in
  let cr = cring_of_ring r in
  let f  = ring_eq hyps cr eqs f1 f2 in
  if   EcReduction.is_conv hyps f (emb_rzero r)
  then FApi.xmutate1 tc `Ring []
  else FApi.xmutate1 tc `Ring [f_eq f (emb_rzero r)]

let t_ring_congr (cr:cring) (rm:RState.rstate) li lv tc =
  let r  = ring_of_cring cr in
  let concl = FApi.tc1_goal tc in
  let f1,f2 = try destr_eq concl with DestrError _ -> raise InvalidGoalShape in
  let pe, rm = toring (FApi.tc1_hyps tc) cr rm f1 in
  let rm' = RState.update rm li lv in
  let f2' = ofring r rm' pe in
  if not (f_equal f2 f2') then raise InvalidGoalShape;

  let env = FApi.tc1_env tc in
  let mk_goal i =
    let r1 = oget (RState.get i rm) in
    let r2 = oget (RState.get i rm') in
    EcReduction.EqTest.for_type_exn env r1.f_ty r2.f_ty;
    f_eq r1 r2 in
  FApi.xmutate1 tc `Ring_congr (List.map mk_goal li)

(* -------------------------------------------------------------------- *)
let t_field_simplify r eqs (f1, f2) tc =
  let hyps = FApi.tc1_hyps tc in
  let cr = cfield_of_field r in
  let (c1, (n1, d1)) = field_simplify hyps cr eqs f1 in
  let (c2, (n2, d2)) = field_simplify hyps cr eqs f2 in

  let c = List.map (fun f -> f_not (f_eq f (emb_fzero r))) (c1 @ c2) in
  let f = f_eq (fdiv r n1 d1) (fdiv r n2 d2) in

  FApi.xmutate1 tc `Field (c @ [f])

let t_field r eqs (f1, f2) tc =
  let hyps = FApi.tc1_hyps tc in
  let cr = cfield_of_field r in
  let (c, ((n1, n2), (d1, d2))) = field_eq hyps cr eqs f1 f2 in
  let c  = Sf.undup (List.map (fun f -> f_not (f_eq f (emb_fzero r))) c) in
  let r1 = fmul r n1 d2
  and r2 = fmul r n2 d1 in
  let f  = ring_eq hyps (cring_of_ring r.f_ring) eqs r1 r2 in

  if   EcReduction.is_conv hyps f (emb_fzero r)
  then FApi.xmutate1 tc `Field c
  else FApi.xmutate1 tc `Field (c @ [f_eq f (emb_fzero r)])

let t_field_congr (cr:cfield) (rm:RState.rstate) li lv tc =
  let r  = field_of_cfield cr in
  let concl = FApi.tc1_goal tc in
  let f1,f2 = try destr_eq concl with DestrError _ -> raise InvalidGoalShape in
  let pe, rm = tofield (FApi.tc1_hyps tc) cr rm f1 in
  let rm' = RState.update rm li lv in
  let f2' = offield r rm' pe in
  if not (f_equal f2 f2') then raise InvalidGoalShape;

  let env = FApi.tc1_env tc in
  let mk_goal i =
    let r1 = oget (RState.get i rm) in
    let r2 = oget (RState.get i rm') in
    EcReduction.EqTest.for_type_exn env r1.f_ty r2.f_ty;
    f_eq r1 r2 in
  FApi.xmutate1 tc `Field_congr (List.map mk_goal li)
