(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcPath
open EcTypes
open EcFol
open EcAlgebra

(* -------------------------------------------------------------------- *)
module Axioms = struct
  open EcDecl

  let tmod  = EcPath.fromqsymbol ([EcCoreLib.id_top; "AlgTactic"], "Requires")
  let tname = "domain"

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

  let core   = ["oner_neq0"; "addr0"; "addrA"; "addrC"; "addrN";
                "mulr1"; "mulrA"; "mulrC"; "mulrDl"]
  let intpow = ["expr0"; "exprS"]
  let ofint  = ["ofint0"; "ofint1"; "ofintS"; "ofintN"]
  let ofsub  = ["subrE"]
  let field  = ["mulrV"; "exprN"]
  let ofdiv  = ["divrE"]

  let ty0 ty = ty
  let ty1 ty = tfun ty (ty0 ty)
  let ty2 ty = tfun ty (ty1 ty)

  let ring_symbols env ty =
    let symbols =
      [(zero, (true , ty0 ty));
       (one , (true , ty0 ty));
       (add , (true , ty2 ty));
       (opp , (true , ty1 ty));
       (sub , (false, ty2 ty));
       (mul , (true , ty2 ty));
       (expr, (true , toarrow [ty; tint] ty))]
    in
      if   EcReduction.equal_type env ty tint
      then symbols
      else symbols @ [(embed, (true, tfun tint ty))]

  let field_symbols env ty =
    (ring_symbols env ty)
      @ [(inv, (true , ty1 ty));
         (div, (false, ty2 ty))]

  let subst_of_ring (cr : ring) =
    let crcore = [(zero, cr.r_zero);
                  (one , cr.r_one );
                  (add , cr.r_add );
                  (opp , cr.r_opp );
                  (mul , cr.r_mul );
                  (expr, cr.r_exp )] in

    let xpath  = fun x -> EcPath.pqname tmod x in
    let add    = fun subst x p -> EcSubst.add_path subst (xpath x) p in

    let subst  = EcSubst.add_tydef EcSubst.empty (xpath tname) ([], cr.r_type) in
    let subst  = List.fold_left (fun subst (x, p) -> add subst x p) subst crcore in
    let subst  = odfl subst (cr.r_sub |> omap (fun p -> add subst sub p)) in
    let subst  = cr.r_embed |> (function `Direct -> subst | `Embed p -> add subst embed p) in
      subst

  let subst_of_field (cr : field) =
    let xpath  = fun x -> EcPath.pqname tmod x in
    let add    = fun subst x p -> EcSubst.add_path subst (xpath x) p in

    let subst = subst_of_ring cr.f_ring in
    let subst = add subst inv cr.f_inv in
    let subst = odfl subst (cr.f_div |> omap (fun p -> add subst div p)) in
      subst

  (* FIXME: should use operators inlining when available *)
  let get axs env cr =
    let subst  =
      match cr with
      | `Ring  cr -> subst_of_ring  cr
      | `Field cr -> subst_of_field cr
    in

    let for1 axname =
      let ax = EcEnv.Ax.by_path (EcPath.pqname tmod axname) env in
        assert (ax.ax_tparams = [] && ax.ax_kind = `Axiom && ax.ax_spec <> None);
        (axname, EcSubst.subst_form subst (oget ax.ax_spec))
    in
      List.map for1 axs

  let get_core   = fun env cr -> get core   env (`Ring  cr)
  let get_expr   = fun env cr -> get intpow env (`Ring  cr)
  let get_ofint  = fun env cr -> get ofint  env (`Ring  cr)
  let get_ofsub  = fun env cr -> get ofsub  env (`Ring  cr)
  let get_field  = fun env cr -> get field  env (`Field cr)
  let get_ofdiv  = fun env cr -> get ofdiv  env (`Field cr)

  let ring_axioms env (cr : ring) =
    let axcore = (get_core env cr) @ (get_expr env cr) in
    let axint  = match cr.r_embed with `Direct -> [] | `Embed _ -> get_ofint env cr in
    let axsub  = match cr.r_sub with None -> [] | Some _ -> get_ofsub env cr in
      List.flatten [axcore; axint; axsub]

  let field_axioms env (cr : field) =
    let axring = ring_axioms env cr.f_ring in
    let axcore = get_field env cr in
    let axdiv  = match cr.f_div with None -> [] | Some _ -> get_ofdiv env cr in
      List.flatten [axring; axcore; axdiv]
end

let ring_symbols  = Axioms.ring_symbols
let field_symbols = Axioms.field_symbols

let ring_axioms  = Axioms.ring_axioms
let field_axioms = Axioms.field_axioms

(* -------------------------------------------------------------------- *)
open EcBaseLogic
open EcLogic

class rn_ring  = object inherit xrule "ring"  end
class rn_field = object inherit xrule "field" end

let rn_ring  = RN_xtd (new rn_ring)
let rn_field = RN_xtd (new rn_field)

let t_ring_simplify cr eqs (f1, f2) g =
  let cr = cring_of_ring cr in
  let f1 = ring_simplify cr eqs f1 in
  let f2 = ring_simplify cr eqs f2 in
	prove_goal_by [f_eq f1 f2] rn_ring g

let t_ring r eqs (f1, f2) g =
  let cr = cring_of_ring r in
  let f  = ring_eq cr eqs f1 f2 in

    if   EcReduction.is_conv (get_hyps g) f (emb_rzero r)
    then prove_goal_by [] rn_ring g
    else prove_goal_by [f_eq f (emb_rzero r)] rn_ring g

let t_field_simplify r eqs (f1, f2) g =
  let cr = cfield_of_field r in
  let (c1, n1, d1) = field_simplify cr eqs f1 in
  let (c2, n2, d2) = field_simplify cr eqs f2 in

  let c = List.map (fun f -> f_not (f_eq f (emb_fzero r))) (c1 @ c2) in
  let f = f_eq (fdiv r n1 d1) (fdiv r n2 d2) in

    prove_goal_by (c @ [f]) rn_field g

let t_field r eqs (f1, f2) g =
  let cr = cfield_of_field r in
  let (c, (n1, n2), (d1, d2)) = field_eq cr eqs f1 f2 in
  let c  = List.map (fun f -> f_not (f_eq f (emb_fzero r))) c in
  let r1 = fmul r n1 d2
  and r2 = fmul r n2 d1 in
  let f  = ring_eq (cring_of_ring r.f_ring) eqs r1 r2 in

    if   EcReduction.is_conv (get_hyps g) f (emb_fzero r)
    then prove_goal_by c rn_field g
    else prove_goal_by (c @ [f_eq f (emb_fzero r)]) rn_field g

(* -------------------------------------------------------------------- *)
let is_module_loaded env =
  EcEnv.Theory.by_path_opt Axioms.tmod env <> None
