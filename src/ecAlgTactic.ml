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

  let tmod  = "AlgTactic"
  let tname = "domain"

  let zero = "rzero"
  let one  = "rone"
  let add  = "add"
  let opp  = "opp"
  let sub  = "sub"
  let mul  = "mul"
  let inv  = "inv"
  let div  = "div"
  let expr = "expr"

  let core   = ("RingCore"    , ["oner_eq0"; "addr0"; "addrA"; "addrC"; "addrN";
                                 "mulr1"; "mulrA"; "mulrC"; "mulrDl"])
  let natmul = ("RingNatMul"  , ["expr0"; "exprS"])
  let ofint  = ("RingOfInt"   , ["ofint0"; "ofint1"; "ofintS"; "ofintN"])
  let ofsub  = ("RingWithSub" , ["subrE"])
  let field  = ("FieldCore"   , ["mulrV"; "exprN"])
  let ofdiv  = ("FieldWithDiv", ["divrE"])

  let subst_of_ring thname (cr : ring) =
    let crcore = [(zero, cr.r_zero);
                  (one , cr.r_one );
                  (add , cr.r_add );
                  (opp , cr.r_opp );
                  (mul , cr.r_mul );
                  (expr, cr.r_exp )] in

    let thpath = EcPath.fromqsymbol ([tmod], thname) in
    let xpath  = fun x -> EcPath.pqname thpath x in
    let add    = fun subst x p -> EcSubst.add_path subst (xpath x) p in

    let subst  = EcSubst.add_tydef EcSubst.empty (xpath tname) ([], cr.r_type) in
    let subst  = List.fold_left (fun subst (x, p) -> add subst x p) subst crcore in
    let subst  = odfl subst (cr.r_sub |> omap (fun p -> add subst sub p)) in
    let subst  = cr.r_intmul |> (function `Embed -> subst | `IntMul p -> add subst expr p) in
      subst

  let subst_of_field thname (cr : field) =
    let thpath = EcPath.fromqsymbol ([tmod], thname) in
    let xpath  = fun x -> EcPath.pqname thpath x in
    let add    = fun subst x p -> EcSubst.add_path subst (xpath x) p in

    let subst = subst_of_ring thname cr.f_ring in
    let subst = add subst inv cr.f_inv in
    let subst = odfl subst (cr.f_div |> omap (fun p -> add subst div p)) in
      subst

  (* FIXME: should use operators inlining when available *)
  let get (thname, axs) env cr =
    let thpath = EcPath.fromqsymbol ([tmod], thname) in
    let subst  =
      match cr with
      | `Ring  cr -> subst_of_ring  thname cr
      | `Field cr -> subst_of_field thname cr
    in

    let for1 axname =
      let ax = EcEnv.Ax.by_path (EcPath.pqname thpath axname) env in
        assert (ax.ax_tparams = [] && ax.ax_kind = `Axiom && ax.ax_spec <> None);
        (axname, EcSubst.subst_form subst (oget ax.ax_spec))
    in
      List.map for1 axs

  let get_core   = fun env cr -> get core   env (`Ring  cr)
  let get_natmul = fun env cr -> get natmul env (`Ring  cr)
  let get_ofint  = fun env cr -> get ofint  env (`Ring  cr)
  let get_ofsub  = fun env cr -> get ofsub  env (`Ring  cr)
  let get_field  = fun env cr -> get field  env (`Field cr)
  let get_ofdiv  = fun env cr -> get ofdiv  env (`Field cr)

  let ring_axioms env (cr : ring) =
    let axcore = (get_core env cr) @ (get_natmul env cr) in
    let axint  = match cr.r_intmul with `Embed -> [] | `IntMul _ -> get_ofint env cr in
    let axsub  = match cr.r_sub with None -> [] | Some _ -> get_ofsub env cr in
      List.flatten [axcore; axint; axsub]

  let field_axioms env (cr : field) =
    let axring = ring_axioms env cr.f_ring in
    let axcore = get_field env cr in
    let axdiv  = match cr.f_div with None -> [] | Some _ -> get_ofdiv env cr in
      List.flatten [axring; axcore; axdiv]
end

let ring_axioms  = Axioms.ring_axioms
let field_axioms = Axioms.field_axioms

(* -------------------------------------------------------------------- *)
open EcBaseLogic
open EcLogic

let t_ring_simplify cr eqs (f1, f2) g =
  let cr = cring_of_ring cr in
  let f1 = ring_simplify cr eqs f1 in
  let f2 = ring_simplify cr eqs f2 in
	prove_goal_by [f_eq f1 f2] RN_ring g

let t_ring r eqs (f1, f2) g =
  let cr = cring_of_ring r in
  let f  = ring_eq cr eqs f1 f2 in

    if   EcReduction.is_conv (get_hyps g) f (rzero r)
    then prove_goal_by [] RN_ring g
    else prove_goal_by [f_eq f (rzero r)] RN_ring g

let t_field_simplify r eqs (f1, f2) g =
  let cr = cfield_of_field r in
  let (c1, n1, d1) = field_simplify cr eqs f1 in
  let (c2, n2, d2) = field_simplify cr eqs f2 in

  let c = List.map (fun f -> f_not (f_eq f (fzero r))) (c1 @ c2) in
  let f = f_eq (fdiv r n1 d1) (fdiv r n2 d2) in

    prove_goal_by (c @ [f]) RN_field g

let t_field r eqs (f1, f2) g =
  let cr = cfield_of_field r in
  let (c, (n1, n2), (d1, d2)) = field_eq cr eqs f1 f2 in
  let c  = List.map (fun f -> f_not (f_eq f (fzero r))) c in
  let r1 = fmul r n1 d2
  and r2 = fmul r n2 d1 in
  let f  = ring_eq (cring_of_ring r.f_ring) eqs r1 r2 in

    if   EcReduction.is_conv (get_hyps g) f (fzero r)
    then prove_goal_by c RN_field g
    else prove_goal_by (c @ [f_eq f (fzero r)]) RN_field g
