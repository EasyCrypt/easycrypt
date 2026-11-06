(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcModules
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the expression change, resolved: the range is an integer
   gap range of the (possibly nested) block at a normalized path, the
   replacements typed expressions over local identifiers recorded with
   them. *)
type tr_expr_change = {
  trec_range : EcMatching.Position.nm_codegap_range option;
  trec_exprs : (EcIdent.t list * expr) option list;
}

type EcPlTransform.transform += TrExprChange of tr_expr_change

(* -------------------------------------------------------------------- *)
let invalid () = raise (InvalidTransform "invalid expression change")

(* -------------------------------------------------------------------- *)
let exprs ?(locals = []) f acc (is : instr list) =
  List.fold_left_map (i_fold_map_expr ~locals f) acc is

let rec locals_of_path (path : Zpr.ipath) =
  match path with
  | ZTop -> []
  | ZWhile  (_, (_, path))
  | ZIfThen (_, (_, path), _)
  | ZIfElse (_, _, (_, path)) -> locals_of_path path
  | ZMatch  (_, (_, path), ctxt) -> locals_of_path path @ ctxt.locals

(* -------------------------------------------------------------------- *)
(* [rename xs ys e]: [e] with the locals [xs] simultaneously renamed to
   [ys] (taken with the types of [xs]). *)
let rename (xs : (EcIdent.t * ty) list) (ys : EcIdent.t list) (e : expr) =
  let subst =
    List.fold_left2
      (fun subst (x, ty) y ->
        EcCoreSubst.bind_elocal subst x (EcTypes.e_local y ty))
      EcCoreSubst.Fsubst.f_subst_id xs ys
  in EcCoreSubst.e_subst subst e

(* Replace [e] (with the match-arm locals [xs] in scope) as told by the
   next element of the replacements, accumulating its obligation. The
   side conditions ensure that [forall ys, e[xs := ys] = e'] implies that
   [e] and [e'[ys := xs]] agree for every value of [xs]: the renamings
   capture nothing. *)
let change xs (obls, cs) (e : expr) =
  match cs with
  | [] -> invalid ()

  | None :: cs ->
      (obls, cs), e

  | Some (ys, e') :: cs ->
      if not (EcTypes.ty_equal e.e_ty e'.e_ty) then invalid ();
      if List.length ys <> List.length xs then invalid ();

      let sxs = EcIdent.Sid.of_list (List.fst xs) in
      let sys = EcIdent.Sid.of_list ys in

      if EcIdent.Sid.cardinal sys <> List.length ys then invalid ();

      if EcIdent.Mid.exists
           (fun x _ -> EcIdent.Sid.mem x sys && not (EcIdent.Sid.mem x sxs))
           (EcTypes.e_fv e) then invalid ();

      if EcIdent.Mid.exists
           (fun x _ -> EcIdent.Sid.mem x sxs && not (EcIdent.Sid.mem x sys))
           (EcTypes.e_fv e') then invalid ();

      let lhs = rename xs ys e in
      let lcs = List.map2 (fun y (_, ty) -> (y, ty)) ys xs in
      let obl = OExprEq { oee_locals = lcs; oee_lhs = lhs; oee_rhs = e'; } in

      (obl :: obls, cs), rename lcs (List.fst xs) e'

(* -------------------------------------------------------------------- *)
(* Replace the expressions of the range (of the whole statement), in
   program order, one obligation per replaced expression. *)
let expr_change (p : tr_expr_change) (ctxt : tr_ctxt) (s : stmt) =
  let (obls, cs), s =
    match p.trec_range with
    | None ->
        let acc, is = exprs change ([], p.trec_exprs) s.s_node in
        acc, stmt is

    | Some (path, (start, fin)) ->
        let invalid_cpos () =
          raise (InvalidTransform "invalid code position") in
        let zpr =
          try  Zpr.zipper_of_nm_cpos (path, start) s
          with EcMatching.Position.InvalidCPos -> invalid_cpos () in
        if not (start <= fin && fin - start <= List.length zpr.z_tail) then
          invalid_cpos ();
        let body, epilog = List.takedrop (fin - start) zpr.z_tail in
        let locals = locals_of_path zpr.z_path in
        let acc, body = exprs ~locals change ([], p.trec_exprs) body in
        acc, Zpr.zip { zpr with z_tail = body @ epilog }
  in

  if not (List.is_empty cs) then invalid ();

  { trr_me  = ctxt.trc_me;
    trr_s   = s;
    trr_obl = List.rev obls; }

let () =
  register (function
    | TrExprChange p -> Some (expr_change p)
    | _ -> None)
