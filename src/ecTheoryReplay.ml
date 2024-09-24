(* ------------------------------------------------------------------ *)
open EcSymbols
open EcUtils
open EcLocation
open EcParsetree
open EcAst
open EcTypes
open EcDecl
open EcModules
open EcTheory
open EcThCloning

module Sp = EcPath.Sp
module Mp = EcPath.Mp
module CS = EcCoreSubst

(* ------------------------------------------------------------------ *)
type ovoptions = {
  clo_abstract : bool;
}

type 'a ovrenv = {
  ovre_ovrd     : EcThCloning.evclone;
  ovre_rnms     : EcThCloning.renaming list;
  ovre_ntclr    : EcPath.Sp.t;
  ovre_opath    : EcPath.path;
  ovre_npath    : EcPath.path;
  ovre_prefix   : (symbol list) pair;
  ovre_glproof  : (ptactic_core option * evtags option) list;
  ovre_abstract : bool;
  ovre_local    : EcTypes.is_local;
  ovre_hooks    : 'a ovrhooks;
}

and 'a ovrhooks = {
  henv      : 'a -> EcSection.scenv;
  hadd_item : 'a -> EcTheory.import -> EcTheory.theory_item_r -> 'a;
  hthenter  : 'a -> thmode -> symbol -> is_local -> 'a;
  hthexit   : 'a -> [`Full | `ClearOnly | `No] -> 'a;
  herr      : 'b . ?loc:EcLocation.t -> string -> 'b;
}

(* -------------------------------------------------------------------- *)
let is_inline_mode (mode : clmode) =
  match mode with `Inline _ -> true | `Alias -> false

let keep_of_mode (mode : clmode) =
  match mode with `Inline `Keep | `Alias -> true | `Inline `Clear -> false

(* -------------------------------------------------------------------- *)
exception Incompatible of incompatible

let tparams_compatible rtyvars ntyvars =
  let rlen = List.length rtyvars and nlen = List.length ntyvars in
  if rlen <> nlen then
    raise (Incompatible (NotSameNumberOfTyParam(rlen,nlen)))

let ty_compatible env ue (rtyvars, rty) (ntyvars, nty) =
  tparams_compatible rtyvars ntyvars;
  let subst = CS.Tvar.init rtyvars (List.map tvar ntyvars) in
  let rty   = CS.Tvar.subst subst rty in
  try  EcUnify.unify env ue rty nty
  with EcUnify.UnificationFailure _ ->
    raise (Incompatible (DifferentType (rty, nty)))

(* -------------------------------------------------------------------- *)
let error_body exn b = if not b then raise exn

(* -------------------------------------------------------------------- *)
let constr_compatible exn env cs1 cs2 =
  error_body exn (List.length cs1 = List.length cs2);
  let doit (s1,tys1) (s2,tys2) =
    error_body exn (EcSymbols.sym_equal s1 s2);
    error_body exn (List.length tys1 = List.length tys2);
    List.iter2 (fun ty1 ty2 -> error_body exn (EcReduction.EqTest.for_type env ty1 ty2)) tys1 tys2 in
  List.iter2 doit cs1 cs2

let datatype_compatible exn hyps ty1 ty2 =
  let env = EcEnv.LDecl.toenv hyps in
  constr_compatible exn env ty1.tydt_ctors ty2.tydt_ctors

let record_compatible exn hyps f1 pr1 f2 pr2 =
  error_body exn (EcReduction.is_conv hyps f1 f2);
  error_body exn (List.length pr1 = List.length pr2);
  let env = EcEnv.LDecl.toenv hyps in
  let doit (s1,ty1) (s2,ty2) =
    error_body exn (EcSymbols.sym_equal s1 s2);
    error_body exn (EcReduction.EqTest.for_type env ty1 ty2) in
  List.iter2 doit pr1 pr2

let get_open_tydecl hyps p tys =
  let tydecl = EcEnv.Ty.by_path p (EcEnv.LDecl.toenv hyps) in
  EcSubst.open_tydecl tydecl tys

let rec tybody_compatible exn hyps ty_body1 ty_body2 =
  match ty_body1, ty_body2 with
  | `Abstract _, `Abstract _ -> () (* FIXME Sp.t *)
  | `Concrete ty1   , `Concrete ty2 -> error_body exn (EcReduction.EqTest.for_type (EcEnv.LDecl.toenv hyps) ty1 ty2)
  | `Datatype ty1   , `Datatype ty2 -> datatype_compatible exn hyps ty1 ty2
  | `Record (f1,pr1), `Record(f2,pr2) -> record_compatible exn hyps f1 pr1 f2 pr2
  | _, `Concrete {ty_node = Tconstr(p, tys) } ->
    let ty_body2 = get_open_tydecl hyps p tys in
    tybody_compatible exn hyps ty_body1 ty_body2
  | `Concrete{ty_node = Tconstr(p, tys) }, _ ->
    let ty_body1 = get_open_tydecl hyps p tys in
    tybody_compatible exn hyps ty_body1 ty_body2
  | _, _ -> raise exn (* FIXME should we do more for concrete version other *)

let tydecl_compatible env tyd1 tyd2 =
  let params = tyd1.tyd_params in
  tparams_compatible params tyd2.tyd_params;
  let tparams = List.map (fun (id,_) -> tvar id) params in
  let ty_body1 = tyd1.tyd_type in
  let ty_body2 = EcSubst.open_tydecl tyd2 tparams in
  let exn  = Incompatible (TyBody(*tyd1,tyd2*)) in
  let hyps = EcEnv.LDecl.init env params in
  match ty_body1, ty_body2 with
  | `Abstract _, _ -> () (* FIXME Sp.t *)
  | _, _ -> tybody_compatible exn hyps ty_body1 ty_body2

(* -------------------------------------------------------------------- *)
let expr_compatible exn env s e1 e2 =
  let f1 = EcFol.form_of_expr EcFol.mhr e1 in
  let f2 = EcSubst.subst_form s (EcFol.form_of_expr EcFol.mhr e2) in
  let ri = { EcReduction.full_red with delta_p = fun _-> `Force; } in
  error_body exn (EcReduction.is_conv ~ri:ri (EcEnv.LDecl.init env []) f1 f2)

let get_open_oper exn env p tys =
  let oper = EcEnv.Op.by_path p env in
  let _, okind = EcSubst.open_oper oper tys in
  match okind with
  | OB_oper (Some ob) -> ob
  | _ -> raise exn

let rec oper_compatible exn env ob1 ob2 =
  match ob1, ob2 with
  | OP_Plain f1, OP_Plain f2 ->
    let ri = { EcReduction.full_red with delta_p = fun _-> `Force; } in
    error_body exn (EcReduction.is_conv ~ri:ri (EcEnv.LDecl.init env []) f1 f2)
  | OP_Plain {f_node = Fop(p,tys)}, _ ->
    let ob1 = get_open_oper exn env p tys  in
    oper_compatible exn env ob1 ob2
  | _, OP_Plain {f_node = Fop(p,tys)} ->
    let ob2 = get_open_oper exn env p tys in
    oper_compatible exn env ob1 ob2
  | OP_Constr(p1,i1), OP_Constr(p2,i2) ->
    error_body exn (EcPath.p_equal p1 p2 && i1 = i2)
  | OP_Record p1, OP_Record p2 ->
    error_body exn (EcPath.p_equal p1 p2)
  | OP_Proj(p1,i11,i12), OP_Proj(p2,i21,i22) ->
    error_body exn (EcPath.p_equal p1 p2 && i11 = i21 && i12 = i22)
  | OP_Fix f1, OP_Fix f2 ->
    opfix_compatible exn env f1 f2
  | OP_TC, OP_TC -> ()
  | _, _ -> raise exn

and opfix_compatible exn env f1 f2 =
  let s = params_compatible exn env EcSubst.empty f1.opf_args f2.opf_args in
  error_body exn (EcReduction.EqTest.for_type env f1.opf_resty f2.opf_resty);
  error_body exn (f1.opf_struct = f2.opf_struct);
  opbranches_compatible exn env s f1.opf_branches f2.opf_branches

and params_compatible exn env s p1 p2 =
  error_body exn (List.length p1 = List.length p2);
  let doit s (id1,ty1) (id2,ty2) =
    error_body exn (EcReduction.EqTest.for_type env ty1 ty2);
    EcSubst.add_flocal s id2 (EcFol.f_local id1 ty1) in
  List.fold_left2 doit s p1 p2

and opbranches_compatible exn env s ob1 ob2 =
  match ob1, ob2 with
  | OPB_Leaf(d1,e1), OPB_Leaf(d2,e2) ->
    error_body exn (List.length d1 = List.length d2);
    let s =
      List.fold_left2 (params_compatible exn env) s d1 d2 in
    expr_compatible exn env s e1 e2

  | OPB_Branch obs1, OPB_Branch obs2 ->
    error_body exn (Parray.length obs1 = Parray.length obs2);
    Parray.iter2 (opbranch_compatible exn env s) obs1 obs2
  | _, _ -> raise exn

and opbranch_compatible exn env s ob1 ob2 =
  error_body exn (EcPath.p_equal (fst ob1.opb_ctor) (fst ob2.opb_ctor));
  error_body exn (snd ob1.opb_ctor = snd ob2.opb_ctor);
  opbranches_compatible exn env s ob1.opb_sub ob2.opb_sub

let get_open_pred exn env p tys =
  let oper = EcEnv.Op.by_path p env in
  let _, okind = EcSubst.open_oper oper tys in
  match okind with
  | OB_pred (Some pb) -> pb
  | _ -> raise exn

let rec pred_compatible exn env pb1 pb2 =
  match pb1, pb2 with
  | PR_Plain f1, PR_Plain f2 -> error_body exn (EcReduction.is_conv (EcEnv.LDecl.init env []) f1 f2)
  | PR_Plain {f_node = Fop(p,tys)}, _ ->
    let pb1 = get_open_pred exn env p tys  in
    pred_compatible exn env pb1 pb2
  | _, PR_Plain {f_node = Fop(p,tys)} ->
    let pb2 = get_open_pred exn env p tys  in
    pred_compatible exn env pb1 pb2
  | PR_Ind pr1, PR_Ind pr2 ->
    ind_compatible exn env pr1 pr2
  | _, _ -> raise exn

and ind_compatible exn env pi1 pi2 =
  let s = params_compatible exn env EcSubst.empty pi1.pri_args pi2.pri_args in
  error_body exn (List.length pi1.pri_ctors = List.length pi2.pri_ctors);
  List.iter2 (prctor_compatible exn env s) pi1.pri_ctors pi2.pri_ctors

and prctor_compatible exn env s prc1 prc2 =
  error_body exn (EcSymbols.sym_equal prc1.prc_ctor prc2.prc_ctor);
  let env, s = EcReduction.check_bindings exn env s prc1.prc_bds prc2.prc_bds in
  error_body exn (List.length prc1.prc_spec = List.length prc2.prc_spec);
  let doit f1 f2 =
    error_body exn (EcReduction.is_conv (EcEnv.LDecl.init env []) f1 (EcSubst.subst_form s f2)) in
  List.iter2 doit prc1.prc_spec prc2.prc_spec

let nott_compatible exn env nb1 nb2 =
  let s = params_compatible exn env EcSubst.empty nb1.ont_args nb2.ont_args in
  (* We do not check ont_resty because it is redundant *)
  expr_compatible exn env s nb1.ont_body nb2.ont_body

let operator_compatible env oper1 oper2 =
  let open EcDecl in
  let params = oper1.op_tparams in
  tparams_compatible oper1.op_tparams oper2.op_tparams;
  let oty1, okind1 = oper1.op_ty, oper1.op_kind in
  let tparams = List.map (fun (id,_) -> tvar id) params in
  let oty2, okind2 = EcSubst.open_oper oper2 tparams in
  if not (EcReduction.EqTest.for_type env oty1 oty2) then
    raise (Incompatible (DifferentType(oty1, oty2)));
  let hyps = EcEnv.LDecl.init env params in
  let env  = EcEnv.LDecl.toenv hyps in
  let exn  = Incompatible (OpBody(*oper1,oper2*)) in
  match okind1, okind2 with
  | OB_oper None      , OB_oper _          -> ()
  | OB_oper (Some ob1), OB_oper (Some ob2) -> oper_compatible exn env ob2 ob1
  | OB_pred None      , OB_pred _          -> ()
  | OB_pred (Some pb1), OB_pred (Some pb2) -> pred_compatible exn env pb2 pb1
  | OB_nott nb1       , OB_nott nb2        -> nott_compatible exn env nb2 nb1
  | _                 , _                  -> raise exn

(* -------------------------------------------------------------------- *)
let check_evtags (tags : evtags) (src : symbol list) =
  let module E = struct exception Reject end in

  try
    let dfl = not (List.exists (fun (mode, _) -> mode = `Include) tags) in
    let stt =
      List.map (fun src ->
        let do1 status (mode, dst) =
          match mode with
          | `Exclude -> if sym_equal src dst then raise E.Reject; status
          | `Include -> status || (sym_equal src dst)
        in List.fold_left do1 dfl tags)
        src
    in List.mem true stt

  with E.Reject -> false

(* -------------------------------------------------------------------- *)
let xpath ove x =
  EcPath.pappend ove.ovre_opath
    (EcPath.fromqsymbol (fst ove.ovre_prefix, x))

(* -------------------------------------------------------------------- *)
let xnpath ove x =
  EcPath.pappend ove.ovre_npath
    (EcPath.fromqsymbol (snd ove.ovre_prefix, x))

(* -------------------------------------------------------------------- *)
let string_of_renaming_kind = function
  | `Lemma   -> "lemma"
  | `Op      -> "operator"
  | `Pred    -> "predicate"
  | `Type    -> "type"
  | `Module  -> "module"
  | `ModType -> "module type"
  | `Theory  -> "theory"

(* -------------------------------------------------------------------- *)
let rename ove subst (kind, name) =
  try
    let newname =
      List.find_map
        (fun rnm -> EcThCloning.rename rnm (kind, name))
        ove.ovre_rnms in

    let nameok =
      match kind with
      | `Lemma | `Type ->
          EcIo.is_sym_ident newname
      | `Op | `Pred ->
          EcIo.is_op_ident newname
      | `Module | `ModType | `Theory ->
          EcIo.is_mod_ident newname
    in

    if not nameok then
      ove.ovre_hooks.herr
        (Format.sprintf
           "renamings generated an invalid (%s) name: %s -> %s"
           (string_of_renaming_kind kind) name newname);

    let subst =
      EcSubst.add_path subst
        ~src:(xpath ove name) ~dst:(xnpath ove newname)
    in (subst, newname)

  with Not_found -> (subst, name)

(* -------------------------------------------------------------------- *)
let rec replay_tyd (ove : _ ovrenv) (subst, ops, proofs, scope) (import, x, otyd) =
  let scenv = ove.ovre_hooks.henv scope in
  let env   = EcSection.env scenv in
  match Msym.find_opt x ove.ovre_ovrd.evc_types with
  | None ->
      let otyd = EcSubst.subst_tydecl subst otyd in
      let subst, x = rename ove subst (`Type, x) in
      let item = (Th_type (x, otyd)) in
      (subst, ops, proofs, ove.ovre_hooks.hadd_item scope import item)

  | Some { pl_desc = (tydov, mode) } -> begin
      let newtyd, body =
        match tydov with
        | `BySyntax (nargs, ntyd) ->
            let nargs = List.map2
                          (fun (_, tc) x -> (EcIdent.create (unloc x), tc))
                          otyd.tyd_params nargs in
            let ue    = EcUnify.UniEnv.create (Some nargs) in
            let ntyd  = EcTyping.transty EcTyping.tp_tydecl env ue ntyd in
            let decl  =
              { tyd_params  = nargs;
                tyd_type    = `Concrete ntyd;
                tyd_resolve = otyd.tyd_resolve && (mode = `Alias);
                tyd_loca    = otyd.tyd_loca; }

            in (decl, ntyd)

        | `ByPath p -> begin
            match EcEnv.Ty.by_path_opt p env with
            | Some reftyd ->
                let tyargs = List.map (fun (x, _) -> EcTypes.tvar x) reftyd.tyd_params in
                let body   = tconstr p tyargs in
                let decl   =
                  { reftyd with
                      tyd_type    = `Concrete body;
                      tyd_resolve = otyd.tyd_resolve && (mode = `Alias); } in
                (decl, body)

            | _ -> assert false
          end
      in

      let subst, x =
        match mode with
        | `Alias ->
            rename ove subst (`Type, x)

        | `Inline _ ->
          let subst =
            EcSubst.add_tydef
              subst (xpath ove x) (List.map fst newtyd.tyd_params, body) in

          let subst =
            (* FIXME: HACK *)
            match otyd.tyd_type, body.ty_node with
            | `Datatype { tydt_ctors = octors }, Tconstr (np, _) -> begin
                match (EcEnv.Ty.by_path np env).tyd_type with
                | `Datatype { tydt_ctors = _ } ->
                  let newtparams = List.fst newtyd.tyd_params in
                  let newtparams_ty = List.map tvar newtparams in
                  let newdtype = tconstr np newtparams_ty in
                  let tysubst = CS.Tvar.init (List.fst otyd.tyd_params) newtparams_ty in

                  List.fold_left (fun subst (name, tyargs) ->
                      let np = EcPath.pqoname (EcPath.prefix np) name in
                      let newtyargs = List.map (CS.Tvar.subst tysubst) tyargs in
                      EcSubst.add_opdef subst
                        (xpath ove name)
                        (newtparams, e_op np newtparams_ty (toarrow newtyargs newdtype)))
                    subst octors
                | _ -> subst
              end
            | _, _ -> subst

          in (subst, x) in

      let refotyd = EcSubst.subst_tydecl subst otyd in

      begin
        try tydecl_compatible env refotyd newtyd
        with Incompatible err ->
          clone_error env (CE_TyIncompatible ((snd ove.ovre_prefix, x), err))
      end;

      let scope =
        match mode with
        | `Alias ->
            let item = EcTheory.Th_type (x, newtyd) in
            ove.ovre_hooks.hadd_item scope import item

        | `Inline `Keep ->
            let item = EcTheory.Th_type (x, newtyd) in
            ove.ovre_hooks.hadd_item scope EcTheory.noimport item

        | `Inline `Clear ->
            scope

      in (subst, ops, proofs, scope)
  end

(* -------------------------------------------------------------------- *)
and replay_opd (ove : _ ovrenv) (subst, ops, proofs, scope) (import, x, oopd) =
  let scenv = ove.ovre_hooks.henv scope in
  let env   = EcSection.env scenv in

  match Msym.find_opt x ove.ovre_ovrd.evc_ops with
  | None ->
      let (subst, x) = rename ove subst (`Op, x) in
      let oopd = EcSubst.subst_op subst oopd in
      (subst, ops, proofs, ove.ovre_hooks.hadd_item scope import (Th_operator (x, oopd)))

  | Some { pl_desc = (opov, opmode); pl_loc = loc; } ->
      let refop = EcSubst.subst_op subst oopd in
      let (reftyvars, refty) = (refop.op_tparams, refop.op_ty) in

      let (newop, subst, x, alias) =
        let newop, body =
          match opov with
          | `BySyntax opov ->
              let tp = opov.opov_tyvars |> omap (List.map (fun tv -> (tv, []))) in
              let ue = EcTyping.transtyvars env (loc, tp) in
              let tp = EcTyping.tp_relax in
              let (ty, body) =
                let codom   = EcTyping.transty tp env ue opov.opov_retty in
                let env, xs = EcTyping.trans_binding env ue opov.opov_args in
                let body    = EcTyping.trans_form env ue opov.opov_body codom in
                let lam     = EcFol.f_lambda (List.map (fun (x, ty) -> (x, GTty ty)) xs) body in
                (lam.f_ty, lam)
              in
              begin
                try ty_compatible env ue
                    (List.map fst reftyvars, refty)
                    (List.map fst (EcUnify.UniEnv.tparams ue), ty)
                with Incompatible err ->
                  clone_error env (CE_OpIncompatible ((snd ove.ovre_prefix, x), err))
              end;

              if not (EcUnify.UniEnv.closed ue) then
                ove.ovre_hooks.herr
                  ~loc "this operator body contains free type variables";

              let sty     = CS.Tuni.subst (EcUnify.UniEnv.close ue) in
              let body    = EcFol.Fsubst.f_subst sty body in
              let ty      = CS.ty_subst sty ty in
              let tparams = EcUnify.UniEnv.tparams ue in
              let newop   =
                mk_op
                  ~opaque:optransparent ~clinline:(opmode <> `Alias)
                  tparams ty (Some (OP_Plain body)) refop.op_loca in
              (newop, body)

          | `ByPath p -> begin
            match EcEnv.Op.by_path_opt p env with
            | Some ({ op_kind = OB_oper _ } as refop) ->
                let tyargs = List.map (fun (x, _) -> EcTypes.tvar x) refop.op_tparams in
                let body =
                  if refop.op_clinline then
                    (match refop.op_kind with
                    | OB_oper (Some (OP_Plain body)) -> body
                    | _ -> assert false)
                  else EcFol.f_op p tyargs refop.op_ty in
                let decl   =
                  { refop with
                      op_kind = OB_oper (Some (OP_Plain body));
                      op_clinline = (opmode <> `Alias) } in
                (decl, body)

            | _ -> clone_error env (CE_UnkOverride(OVK_Operator, EcPath.toqsymbol p))
          end
        in
          match opmode with
          | `Alias ->
              let subst, x = rename ove subst (`Op, x) in
              (newop, subst, x, true)

          | `Inline _ ->
              let body =
                try
                  EcFol.expr_of_form EcFol.mhr body
                with EcFol.CannotTranslate ->
                  clone_error env (CE_InlinedOpIsForm (snd ove.ovre_prefix, x))
              in
              let subst1 = (List.map fst newop.op_tparams, body) in
              let subst  = EcSubst.add_opdef subst (xpath ove x) subst1
              in  (newop, subst, x, false)
      in

      let ops =
        let opp = EcPath.fromqsymbol (snd ove.ovre_prefix, x) in
        Mp.add opp (newop, alias) ops in

      begin
        try operator_compatible env refop newop
        with Incompatible err ->
          clone_error env (CE_OpIncompatible ((snd ove.ovre_prefix, x), err))
      end;

      let scope =
        match opmode with
        | `Alias ->
            let item = Th_operator (x, newop) in
            ove.ovre_hooks.hadd_item scope import item

        | `Inline `Keep ->
            let item = Th_operator (x, newop) in
            ove.ovre_hooks.hadd_item scope EcTheory.noimport item

        | `Inline `Clear ->
            scope

      in (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_prd (ove : _ ovrenv) (subst, ops, proofs, scope) (import, x, oopr) =
  let scenv = ove.ovre_hooks.henv scope in
  let env   = EcSection.env scenv in
  match Msym.find_opt x ove.ovre_ovrd.evc_preds with
  | None ->
      let subst, x = rename ove subst (`Pred, x) in
      let oopr = EcSubst.subst_op subst oopr in
      (subst, ops, proofs, ove.ovre_hooks.hadd_item scope import (Th_operator (x, oopr)))

  | Some { pl_desc = (prov, prmode); pl_loc = loc; } ->
    let refpr = EcSubst.subst_op subst oopr in
    let (reftyvars, refty) =
      (refpr.op_tparams, refpr.op_ty)
    in

    let (newpr, subst, x) =
      let newpr, body =
        match prov with
        | `BySyntax prov ->
            let tp = prov.prov_tyvars |> omap (List.map (fun tv -> (tv, []))) in
            let ue = EcTyping.transtyvars env (loc, tp) in
            let body =
              let env, xs = EcTyping.trans_binding env ue prov.prov_args in
              let body    = EcTyping.trans_form_opt env ue prov.prov_body None in
              let xs      = List.map (fun (x, ty) -> x, GTty ty) xs in
              let lam     = EcFol.f_lambda xs body in
              lam
            in

            begin
              try
                ty_compatible env ue
                  (List.map fst reftyvars, refty)
                  (List.map fst (EcUnify.UniEnv.tparams ue), body.f_ty)
              with Incompatible err ->
                clone_error env
                  (CE_OpIncompatible ((snd ove.ovre_prefix, x), err))
            end;

            if not (EcUnify.UniEnv.closed ue) then
              ove.ovre_hooks.herr
                ~loc "this predicate body contains free type variables";

            let fs = CS.Tuni.subst (EcUnify.UniEnv.close ue) in
            let body    = EcFol.Fsubst.f_subst fs body in
            let tparams = EcUnify.UniEnv.tparams ue in
            let newpr   =
              { op_tparams  = tparams;
                op_ty       = body.f_ty;
                op_kind     = OB_pred (Some (PR_Plain body));
                op_opaque   = oopr.op_opaque;
                op_clinline = prmode <> `Alias;
                op_loca     = refpr.op_loca;
                op_unfold   = refpr.op_unfold; } in
            (newpr, body)

        | `ByPath p -> begin
          match EcEnv.Op.by_path_opt p env with
          | Some ({ op_kind = OB_pred _ } as refop) ->
              let tyargs = List.map (fun (x, _) -> EcTypes.tvar x) refop.op_tparams in
              let body   =
                if refop.op_clinline then
                  (match refop.op_kind with
                  | OB_pred (Some (PR_Plain body)) -> body
                  | _ -> assert false)
                else EcFol.f_op p tyargs refop.op_ty in
              let newpr =
                { refop with
                  op_kind = OB_pred (Some (PR_Plain body));
                  op_clinline = (prmode <> `Alias) ; }
              in newpr, body

          | _ -> clone_error env (CE_UnkOverride(OVK_Predicate, EcPath.toqsymbol p))
        end
      in

        match prmode with
        | `Alias ->
          let subst, x = rename ove subst (`Pred, x) in
          (newpr, subst, x)

        | `Inline _ ->
            let subst1 = (List.map fst newpr.op_tparams, body) in
            let subst  = EcSubst.add_pddef subst (xpath ove x) subst1 in
            (newpr, subst, x)

    in

    begin
      try operator_compatible env refpr newpr
      with Incompatible err ->
        clone_error env (CE_OpIncompatible ((snd ove.ovre_prefix, x), err))
    end;

    let scope =
      match prmode with
      | `Alias ->
          let item = Th_operator (x, newpr) in
          ove.ovre_hooks.hadd_item scope import item

      | `Inline `Keep ->
          let item = Th_operator (x, newpr) in
          ove.ovre_hooks.hadd_item scope EcTheory.noimport item

      | `Inline `Clear ->
          scope

    in (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_ntd (ove : _ ovrenv) (subst, ops, proofs, scope) (import, x, oont) =
  match Msym.find_opt x ove.ovre_ovrd.evc_abbrevs with
  | None ->
    if EcPath.Sp.mem (xpath ove x) ove.ovre_ntclr then
      (subst, ops, proofs, scope)
    else
      let subst, x = rename ove subst (`Op, x) in
      let oont = EcSubst.subst_op subst oont in
      let item = Th_operator (x, oont) in
      let scope = ove.ovre_hooks.hadd_item scope import item in
      (subst, ops, proofs, scope)

  | Some { pl_desc = (_, mode) } -> begin
    match mode with
    | `Alias | `Inline `Keep ->
      let subst, x = rename ove subst (`Op, x) in
      let oont = EcSubst.subst_op subst oont in
      let item = Th_operator (x, oont) in
      let scope = ove.ovre_hooks.hadd_item scope import item in
      (subst, ops, proofs, scope)
    | `Inline `Clear ->
      (subst, ops, proofs, scope)
  end

(* -------------------------------------------------------------------- *)
and replay_axd (ove : _ ovrenv) (subst, ops, proofs, scope) (import, x, ax) =
  let scenv = ove.ovre_hooks.henv scope in
  let subst, x = rename ove subst (`Lemma, x) in
  let ax = EcSubst.subst_ax subst ax in
  let (ax, proofs, axclear) =
    if ove.ovre_abstract then (ax, proofs, false) else

    let axclear, tags =
      match ax.ax_kind with
        | `Lemma -> (false, Ssym.empty)
        | `Axiom (tags, axc) -> (axc, tags) in

    let doproof =
      match Msym.find_opt x (ove.ovre_ovrd.evc_lemmas.ev_bynames) with
      | Some (pt, hide, explicit) -> Some (pt, hide, explicit)
      | None when is_axiom ax.ax_kind ->
          List.Exceptionless.find_map
            (function (pt, None) -> Some (pt, `Alias, false) | (pt, Some pttags) ->
               if check_evtags pttags (Ssym.elements tags) then
                 Some (pt, `Alias, false)
               else None)
            ove.ovre_glproof
      | _ -> None
    in
      match doproof with
      | None -> (ax, proofs, false)
      | Some (pt, hide, explicit)  ->
          if explicit && not (EcDecl.is_axiom ax.ax_kind) then
            clone_error (EcSection.env scenv) (CE_ProofForLemma (snd ove.ovre_prefix, x));
          let ax  = { ax with
            ax_kind = `Lemma;
            ax_visibility = if hide <> `Alias then `Hidden else ax.ax_visibility
          } in
          let axc = { axc_axiom = (x, ax);
                      axc_path  = EcPath.fromqsymbol (snd ove.ovre_prefix, x);
                      axc_tac   = pt;
                      axc_env   = scenv; } in
            (ax, axc :: proofs, axclear || hide = `Inline `Clear) in

  let scope =
    if axclear then scope else
      ove.ovre_hooks.hadd_item scope import (Th_axiom(x, ax))
  in (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_modtype
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, x, modty)
=
  match Msym.find_opt x ove.ovre_ovrd.evc_modtypes with
  | None ->
      let subst, x = rename ove subst (`ModType, x) in
      let modty = EcSubst.subst_top_modsig subst modty in
      let item = Th_modtype (x, modty) in
      (subst, ops, proofs, ove.ovre_hooks.hadd_item scope import item)

  | Some { pl_desc = (newname, mode) } ->
      let env = EcSection.env (ove.ovre_hooks.henv scope) in
      let np, newmt = EcEnv.ModTy.lookup (unloc newname) env in
      let subst, name =
        match mode with
        | `Alias -> rename ove subst (`Module, x)
        | `Inline _ ->
          let subst = EcSubst.add_path subst ~src:(xpath ove x) ~dst:np in
          subst, x in

      let modty = EcSubst.subst_top_modsig subst modty in

      if not (EcReduction.EqTest.for_msig env modty.tms_sig newmt.tms_sig) then
        clone_error env (CE_ModTyIncompatible (snd ove.ovre_prefix, x));

      let scope =
        if keep_of_mode mode then
          let item = Th_modtype (name, newmt) in
          ove.ovre_hooks.hadd_item scope import item
        else scope
      in (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_mod
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, (me : top_module_expr))
=
  match Msym.find_opt me.tme_expr.me_name ove.ovre_ovrd.evc_modexprs with
  | None ->
      let subst, name = rename ove subst (`Module, me.tme_expr.me_name) in
      let me = EcSubst.subst_top_module subst me in
      let me = { me with tme_expr = { me.tme_expr with me_name = name } } in
      let item = (Th_module me) in
      (subst, ops, proofs, ove.ovre_hooks.hadd_item scope import item)

  | Some { pl_desc = (newname, mode) } ->
      let name  = me.tme_expr.me_name in
      let env   = EcSection.env (ove.ovre_hooks.henv scope) in

      let mp, (newme, newlc) = EcEnv.Mod.lookup (unloc newname) env in

      let np =
        match mp.m_top with
        | `Concrete (p, None) -> p
        | _ -> assert false
      in

      let substme = EcSubst.add_moddef subst ~src:(xpath ove name) ~dst:np in

      let me    = EcSubst.subst_top_module substme me in
      let me    = { me with tme_expr = { me.tme_expr with me_name = name } } in
      let newme = { newme with me_name = name } in
      let newme = { tme_expr = newme; tme_loca = Option.get newlc; } in

      if not (EcReduction.EqTest.for_mexpr ~body:false env me.tme_expr newme.tme_expr) then
        clone_error env (CE_ModIncompatible (snd ove.ovre_prefix, name));

      let (subst, _) =
        match mode with
        | `Alias ->
          rename ove subst (`Module, name)
        | `Inline _ ->
          substme, EcPath.basename np in

      let newme =
        if mode = `Alias || mode = `Inline `Keep then
          let alias = ME_Alias (
              List.length newme.tme_expr.me_params,
              EcPath.m_apply
                mp
                (List.map (fun (id, _) -> EcPath.mident id) newme.tme_expr.me_params)
          )
          in { newme with tme_expr = { newme.tme_expr with me_body = alias } }
        else newme in

      let scope =
        if   keep_of_mode mode
        then ove.ovre_hooks.hadd_item scope import (Th_module newme)
        else scope in

      (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_export
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, p, lc)
=
  let scenv = ove.ovre_hooks.henv scope in
  let env   = EcSection.env scenv in
  let p = EcSubst.subst_path subst p in

  if is_none (EcEnv.Theory.by_path_opt p env) then
    (subst, ops, proofs, scope)
  else
    let scope = ove.ovre_hooks.hadd_item scope import (Th_export (p, lc)) in
    (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_baserw
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, name, lc)
=
  let scope = ove.ovre_hooks.hadd_item scope import (Th_baserw (name, lc)) in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_addrw
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, p, l, lc)
=
  let p     = EcSubst.subst_path subst p in
  let l     = List.map (EcSubst.subst_path subst) l in
  let scope = ove.ovre_hooks.hadd_item scope import (Th_addrw (p, l, lc)) in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_auto
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, lvl, base, ps, lc)
=
  let env = EcSection.env (ove.ovre_hooks.henv scope) in
  let ps = List.map (EcSubst.subst_path subst) ps in
  let ps = List.filter (fun p -> Option.is_some (EcEnv.Ax.by_path_opt p env)) ps in
  let scope = ove.ovre_hooks.hadd_item scope import (Th_auto (lvl, base, ps, lc)) in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_reduction
  (ove : _ ovrenv) (subst, ops, proofs, scope)
  (import, rules : _ * (EcPath.path * EcTheory.rule_option * EcTheory.rule option) list)
=
  let for1 (p, opts, rule) =
    let exception Removed in

    let p = EcSubst.subst_path subst p in

    let rule =
      obind (fun rule ->
        let env = EcSection.env (ove.ovre_hooks.henv scope) in

        try
          if not (is_some (EcEnv.Ax.by_path_opt p env)) then
            raise Removed;
          Some (EcReduction.User.compile ~opts ~prio:rule.rl_prio env p)
        with EcReduction.User.InvalidUserRule _ | Removed -> None) rule

    in (p, opts, rule) in

  let rules = List.map for1 rules in
  let scope = ove.ovre_hooks.hadd_item scope import (Th_reduction rules) in

  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_typeclass
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, x, tc)
=
  let tc = EcSubst.subst_tc subst tc in
  let scope = ove.ovre_hooks.hadd_item scope import (Th_typeclass (x, tc)) in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_instance
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, (typ, ty), tc, lc)
=
  let opath = ove.ovre_opath in
  let npath = ove.ovre_npath in

  let module E = struct exception InvInstPath end in

  let forpath (p : EcPath.path) =
    match EcPath.remprefix ~prefix:opath ~path:p |> omap List.rev with
    | None | Some [] -> None
    | Some (x::px) ->
        let q = EcPath.fromqsymbol (List.rev px, x) in

        match Mp.find_opt q ops with
        | None ->
            Some (EcPath.pappend npath q)
        | Some (op, alias) ->
            match alias with
            | true  -> Some (EcPath.pappend npath q)
            | false ->
                match op.EcDecl.op_kind with
                | OB_pred _
                | OB_nott _    -> assert false
                | OB_oper None -> None
                | OB_oper (Some (OP_Constr _))
                | OB_oper (Some (OP_Record _))
                | OB_oper (Some (OP_Proj   _))
                | OB_oper (Some (OP_Fix    _))
                | OB_oper (Some (OP_TC      )) ->
                    Some (EcPath.pappend npath q)
                | OB_oper (Some (OP_Plain f)) ->
                    match f.f_node with
                    | Fop (r, _) -> Some r
                    | _ -> raise E.InvInstPath
  in

  let forpath p = odfl p (forpath p) in

  try
    let (typ, ty) = EcSubst.subst_genty subst (typ, ty) in
    let tc =
      let rec doring cr =
        { r_type  = EcSubst.subst_ty subst cr.r_type;
          r_zero  = forpath cr.r_zero;
          r_one   = forpath cr.r_one;
          r_add   = forpath cr.r_add;
          r_opp   = cr.r_opp |> omap forpath;
          r_mul   = forpath cr.r_mul;
          r_exp   = cr.r_exp |> omap forpath;
          r_sub   = cr.r_sub |> omap forpath;
          r_embed =
            begin match cr.r_embed with
            | `Direct  -> `Direct
            | `Default -> `Default
            | `Embed p -> `Embed (forpath p)
            end;
          r_kind = cr.r_kind; }

      and dofield cr =
        { f_ring = doring cr.f_ring;
          f_inv  = forpath cr.f_inv;
          f_div  = cr.f_div |> omap forpath; }
      in
        match tc with
        | `Ring    cr -> `Ring  (doring  cr)
        | `Field   cr -> `Field (dofield cr)
        | `General p  -> `General (forpath p)
    in

    let scope = ove.ovre_hooks.hadd_item scope import (Th_instance ((typ, ty), tc, lc)) in
    (subst, ops, proofs, scope)

  with E.InvInstPath ->
    (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay1 (ove : _ ovrenv) (subst, ops, proofs, scope) item =
  match item.ti_item with
  | Th_type (x, otyd) ->
     replay_tyd ove (subst, ops, proofs, scope) (item.ti_import, x, otyd)

  | Th_operator (x, ({ op_kind = OB_oper _ } as oopd)) ->
     replay_opd ove (subst, ops, proofs, scope) (item.ti_import, x, oopd)

  | Th_operator (x, ({ op_kind = OB_pred _} as oopr)) ->
     replay_prd ove (subst, ops, proofs, scope) (item.ti_import, x, oopr)

  | Th_operator (x, ({ op_kind = OB_nott _} as oont)) ->
     replay_ntd ove (subst, ops, proofs, scope) (item.ti_import, x, oont)

  | Th_axiom (x, ax) ->
     replay_axd ove (subst, ops, proofs, scope) (item.ti_import, x, ax)

  | Th_modtype (x, modty) ->
     replay_modtype ove (subst, ops, proofs, scope) (item.ti_import, x, modty)

  | Th_module me ->
     replay_mod ove (subst, ops, proofs, scope) (item.ti_import, me)

  | Th_export (p, lc) ->
     replay_export ove (subst, ops, proofs, scope) (item.ti_import, p, lc)

  | Th_baserw (x, lc) ->
     replay_baserw ove (subst, ops, proofs, scope) (item.ti_import, x, lc)

  | Th_addrw (p, l, lc) ->
     replay_addrw ove (subst, ops, proofs, scope) (item.ti_import, p, l, lc)

  | Th_reduction rules ->
     replay_reduction ove (subst, ops, proofs, scope) (item.ti_import, rules)

  | Th_auto (lvl, base, ps, lc) ->
     replay_auto ove (subst, ops, proofs, scope) (item.ti_import, lvl, base, ps, lc)

  | Th_typeclass (x, tc) ->
     replay_typeclass ove (subst, ops, proofs, scope) (item.ti_import, x, tc)

  | Th_instance ((typ, ty), tc, lc) ->
     replay_instance ove (subst, ops, proofs, scope) (item.ti_import, (typ, ty), tc, lc)

  | Th_theory (ox, cth) -> begin
      let thmode = cth.cth_mode in
      let (subst, x) = rename ove subst (`Theory, ox) in
      let subovrds = Msym.find_opt ox ove.ovre_ovrd.evc_ths in
      let subovrds = EcUtils.odfl evc_empty subovrds in
      let subove   = { ove with
        ovre_ovrd     = subovrds;
        ovre_abstract = ove.ovre_abstract || (thmode = `Abstract);
        ovre_prefix   = (fst ove.ovre_prefix @ [ox], snd ove.ovre_prefix @ [x]);
        ovre_glproof  =
          if   List.is_empty subovrds.evc_lemmas.ev_global
          then ove.ovre_glproof
          else subovrds.evc_lemmas.ev_global; }
      in

      let (subst, ops, proofs, subscope) =
        let subscope = ove.ovre_hooks.hthenter scope thmode x ove.ovre_local in
        let (subst, ops, proofs, subscope) =
          List.fold_left (replay1 subove)
            (subst, ops, proofs, subscope) cth.cth_items in
        let scope = ove.ovre_hooks.hthexit subscope `Full in
        (subst, ops, proofs, scope)

      in (subst, ops, proofs, subscope)
  end

(* -------------------------------------------------------------------- *)
let replay (hooks : 'a ovrhooks)
  ~abstract ~local ~incl ~clears ~renames
  ~opath ~npath ovrds (scope : 'a) (name, items)
=
  let subst = EcSubst.add_path EcSubst.empty ~src:opath ~dst:npath in
  let ove   = {
    ovre_ovrd     = ovrds;
    ovre_rnms     = renames;
    ovre_ntclr    = clears;
    ovre_opath    = opath;
    ovre_npath    = npath;
    ovre_prefix   = ([], []);
    ovre_abstract = abstract;
    ovre_local    = local;
    ovre_hooks    = hooks;
    ovre_glproof  = ovrds.evc_lemmas.ev_global;
  } in

  try
    let mode  = if abstract then `Abstract else `Concrete in
    let scope = if incl then scope else hooks.hthenter scope mode name local in
    let _, _, proofs, scope =
      List.fold_left (replay1 ove)
        (subst, Mp.empty, [], scope) items in
     let scope = if incl then scope else hooks.hthexit scope `No in
    (List.rev proofs, scope)

  with EcEnv.DuplicatedBinding x ->
    hooks.herr
      (Printf.sprintf "name clash for `%s': check your renamings" x)
