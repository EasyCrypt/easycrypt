(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 About Inv} *)
type inv = (Fol.pred, Fol.pred * Fol.pred * Fol.pred) AstLogic.g_inv

let build_inv_spec inv f1 f2 =
  let eq_params = Fol.mkeq_params f1 f2 in
  let eq_res = Fol.mkeq_result f1 f2 in
  match inv with
    | AstLogic.Inv_global inv -> Fol.pand eq_params inv, Fol.pand eq_res inv
    | AstLogic.Inv_upto (bad1, bad2, inv) ->
      let bad1_bad2 = Fol.piff bad1 bad2 in
      let nbad1 = Fol.pnot bad1 in
      let pre = Fol.pand bad1_bad2
        (Fol.pimplies nbad1 (Fol.pand eq_params inv)) in
      let post = Fol.pand bad1_bad2
        (Fol.pimplies nbad1 (Fol.pand eq_res inv)) in
      pre, post

let build_inv_oracle_spec inv f1 f2 =
  let eq_params = Fol.mkeq_params f1 f2 in
  let eq_res = Fol.mkeq_result f1 f2 in
  match inv with
    | AstLogic.Inv_global inv -> Fol.pand eq_params inv, Fol.pand eq_res inv
    | AstLogic.Inv_upto (bad1, bad2, inv) ->
      let bad1_bad2 = Fol.piff bad1 bad2 in
      let nbad1 = Fol.pnot bad1 in
      let nbad2 = Fol.pnot bad2 in
      let pre = Fol.pand nbad1 (Fol.pand nbad2 (Fol.pand eq_params inv)) in
      let post =
        Fol.pand bad1_bad2
          (Fol.pimplies nbad1 (Fol.pand eq_res inv)) in
      pre, post



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 About Random} *)

let rec bound_random side vx r =
  match r with
    | Ast.Rinter(e1,e2) ->
      let mk_le e1 e2 = Ast.Eapp (Global.op_int_le, [e1;e2]) in
      let le1 = Fol.pred_of_term (mk_le (Fol.term_of_exp side e1) vx) in
      let le2 = Fol.pred_of_term (mk_le vx (Fol.term_of_exp side e2)) in
      Fol.pand le1 le2
    | Ast.Rexcepted(r,e) ->
      let p = bound_random side vx r in
      let mk_notin v e =
        Ast.Eapp (Global.bool_not,
                  [Ast.Eapp (Global.op_in_list (EcTerm.type_of_random r),
                             [v;e])]) in
      let notin = Fol.pred_of_term (mk_notin vx (Fol.term_of_exp side e)) in
      Fol.pand p notin
    | Ast.Rbool | Ast.Rbitstr _ | Ast.Rapp _ -> Fol.Ptrue

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

