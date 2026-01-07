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
  ovre_local    : EcTypes.is_local option;
  ovre_hooks    : 'a ovrhooks;
}

and 'a ovrhooks = {
  henv      : 'a -> EcSection.scenv;
  hadd_item : 'a -> import:bool -> EcTheory.theory_item_r -> 'a;
  hthenter  : 'a -> thmode -> symbol -> is_local -> 'a;
  hthexit   : 'a -> import:bool -> [`Full | `ClearOnly | `No] -> 'a;
  herr      : 'b . ?loc:EcLocation.t -> string -> 'b;
}

(* -------------------------------------------------------------------- *)
let is_inline_mode (mode : clmode) =
  match mode with `Inline _ -> true | `Alias -> false

let keep_of_mode (mode : clmode) =
  match mode with `Inline `Keep | `Alias -> true | `Inline `Clear -> false

(* -------------------------------------------------------------------- *)
exception Incompatible of incompatible

(* -------------------------------------------------------------------- *)
let error_body exn b = if not b then raise exn

(* -------------------------------------------------------------------- *)
let get_open_tydecl (env : EcEnv.env) (p : EcPath.path) (tys : ty list) =
  let tydecl = EcEnv.Ty.by_path p env in
  EcSubst.open_tydecl tydecl tys

(* -------------------------------------------------------------------- *)
exception CoreIncompatible

(* -------------------------------------------------------------------- *)
let get_open_oper (env : EcEnv.env) (p : EcPath.path) (tys : ty list) =
  let oper = EcEnv.Op.by_path p env in
  let _, okind = EcSubst.open_oper oper tys in
  match okind with
  | OB_oper (Some ob) -> ob
  | _ -> raise CoreIncompatible

(* -------------------------------------------------------------------- *)
let get_open_pred (env : EcEnv.env) (p : EcPath.path) (tys : ty list) =
  let oper = EcEnv.Op.by_path p env in
  let _, okind = EcSubst.open_oper oper tys in
  match okind with
  | OB_pred (Some pb) -> pb
  | _ -> raise CoreIncompatible

(* -------------------------------------------------------------------- *)
module Compatible : sig
  type 'a comparator = EcEnv.env -> 'a -> 'a -> unit

  val for_ty :
       EcEnv.env
    -> EcUnify.unienv
    -> EcIdent.ident list * ty
    -> EcIdent.ident list * ty
    -> unit

  val for_tydecl   : tydecl comparator
  val for_operator : operator comparator
end = struct
  open EcEnv.LDecl

  type 'a comparator = EcEnv.env -> 'a -> 'a -> unit

  let ri_compatible =
    { EcReduction.full_red with delta_p = (fun _-> `Force); user = false }

  let check (b : bool) =
    if not b then raise CoreIncompatible

  let for_tparams rtyvars ntyvars =
    let rlen = List.length rtyvars
    and nlen = List.length ntyvars in

    if rlen <> nlen then
      raise (Incompatible (NotSameNumberOfTyParam (rlen, nlen)))

  let for_params 
    (hyps : hyps)
    (s    : EcSubst.subst)
    (p1   : (EcIdent.ident * ty) list)
    (p2   : (EcIdent.ident * ty) list)
  =
    check (List.compare_lengths p1 p2 = 0);

    let do_param s (id1, ty1) (id2, ty2) =
      check (EcReduction.EqTest.for_type (toenv hyps) ty1 ty2);
      EcSubst.add_flocal s id2 (EcFol.f_local id1 ty1)
    in List.fold_left2 do_param s p1 p2

  let for_ty (env : EcEnv.env) (ue : EcUnify.unienv) (rtyvars, rty) (ntyvars, nty) =
    for_tparams rtyvars ntyvars;

    let subst = CS.Tvar.init rtyvars (List.map tvar ntyvars) in
    let rty   = CS.Tvar.subst subst rty in

    try  EcUnify.unify env ue rty nty
    with EcUnify.UnificationFailure _ ->
      raise (Incompatible (DifferentType (rty, nty)))

  let for_expr (hyps : hyps) (s : EcSubst.subst) (e1 : expr) (e2 : expr) =
    let f1 = EcFol.form_of_expr e1 in
    let f2 = EcSubst.subst_form s (EcFol.form_of_expr e2) in
    check (EcReduction.is_conv ~ri:ri_compatible hyps f1 f2)

  let for_datatype (hyps : hyps) (ty1 : ty_dtype) (ty2 : ty_dtype) =
    let for_constr (cs1 : ty_dtype_ctor list) (cs2 : ty_dtype_ctor list) =
      check (List.compare_lengths cs1 cs2 = 0);

      let for_ctor1 (s1,tys1) (s2,tys2) =
        check (EcSymbols.sym_equal s1 s2);
        check (List.compare_lengths tys1 tys2 = 0);
        List.iter2 (fun ty1 ty2 ->
          check (EcReduction.EqTest.for_type (toenv hyps) ty1 ty2)
        ) tys1 tys2
      in List.iter2 for_ctor1 cs1 cs2
    in for_constr ty1.tydt_ctors ty2.tydt_ctors

  let for_record (hyps : hyps) ((f1, pr1) : ty_record) ((f2, pr2) : ty_record) =
    check (EcReduction.is_conv hyps f1 f2);

    let for_field (s1, ty1) (s2, ty2) =
      check (EcSymbols.sym_equal s1 s2);
      check (EcReduction.EqTest.for_type (toenv hyps) ty1 ty2)
    in List.iter2 for_field pr1 pr2

  let rec tybody (hyps : EcEnv.LDecl.hyps) (ty_body1 : ty_body) (ty_body2 : ty_body) =
    match ty_body1, ty_body2 with
    | `Abstract _   ,  `Abstract _   -> () (* FIXME Sp.t *)
    | `Concrete ty1 , `Concrete ty2  -> check (EcReduction.EqTest.for_type (toenv hyps) ty1 ty2)
    | `Datatype ty1 , `Datatype ty2  -> for_datatype hyps ty1 ty2
    | `Record   rec1, `Record   rec2 -> for_record hyps rec1 rec2

    | _, `Concrete { ty_node = Tconstr (p, tys) } ->
      let ty_body2 = get_open_tydecl (toenv hyps) p tys in
      tybody hyps ty_body1 ty_body2

    | `Concrete{ ty_node = Tconstr (p, tys) }, _ ->
      let ty_body1 = get_open_tydecl (toenv hyps) p tys in
      tybody hyps ty_body1 ty_body2

    | _, _ -> raise CoreIncompatible

  let for_tydecl (env : EcEnv.env) (tyd1 : tydecl) (tyd2 : tydecl) =
    try
      let params = tyd1.tyd_params in

      for_tparams params tyd2.tyd_params;

      let tparams = List.map (fun (id,_) -> tvar id) params in
      let ty_body1 = tyd1.tyd_type in
      let ty_body2 = EcSubst.open_tydecl tyd2 tparams in

      let hyps = EcEnv.LDecl.init env params in

      match ty_body1, ty_body2 with
      | `Abstract _, _ -> () (* FIXME Sp.t *)
      | _, _ -> tybody hyps ty_body1 ty_body2

    with CoreIncompatible -> raise (Incompatible TyBody)


  let for_opfix (hyps : hyps) (f1 : opfix) (f2 : opfix) =
    let rec for_opbranch (s : EcSubst.subst) (ob1 : opbranch) (ob2 : opbranch) =
      check (EcPath.p_equal (fst ob1.opb_ctor) (fst ob2.opb_ctor));
      check (snd ob1.opb_ctor = snd ob2.opb_ctor);
      for_opbranches hyps s ob1.opb_sub ob2.opb_sub

    and for_opbranches (hyps : hyps) (s : EcSubst.subst) (ob1 : opbranches) (ob2 : opbranches) =
      match ob1, ob2 with
      | OPB_Leaf (d1, e1), OPB_Leaf (d2, e2) ->
        check (List.compare_lengths d1 d2 = 0);
        let s = List.fold_left2 (for_params hyps) s d1 d2 in
        for_expr hyps s e1 e2

      | OPB_Branch obs1, OPB_Branch obs2 ->
        check (Parray.length obs1 = Parray.length obs2);
        Parray.iter2 (for_opbranch s) obs1 obs2

      | _, _ -> raise CoreIncompatible
      in

    check (EcReduction.EqTest.for_type (toenv hyps) f1.opf_resty f2.opf_resty);
    check (f1.opf_struct = f2.opf_struct);

    let s = for_params hyps EcSubst.empty f1.opf_args f2.opf_args in
    let s = EcSubst.add_path  ~src:f2.opf_recp ~dst:f1.opf_recp s

    in for_opbranches hyps s f1.opf_branches f2.opf_branches

  let for_ind (hyps : hyps) (pi1 : prind) (pi2 : prind) =
    let for_prctor (s : EcSubst.subst) (prc1 : prctor) (prc2 : prctor) =
      check (EcSymbols.sym_equal prc1.prc_ctor prc2.prc_ctor);
      let (env, s) =
        EcReduction.check_bindings
          CoreIncompatible (toenv hyps) s prc1.prc_bds prc2.prc_bds in
      let hyps = EcEnv.LDecl.init env [] in
      check (List.compare_lengths prc1.prc_spec prc2.prc_spec = 0);
      let for_spec (f1 : form) (f2 : form) =
        check (EcReduction.is_conv hyps f1 (EcSubst.subst_form s f2)) in
      List.iter2 for_spec prc1.prc_spec prc2.prc_spec
    in

    let s = for_params hyps EcSubst.empty pi1.pri_args pi2.pri_args in
    check (List.compare_lengths pi1.pri_ctors pi2.pri_ctors = 0);
    List.iter2 (for_prctor s) pi1.pri_ctors pi2.pri_ctors

  let rec for_oper (hyps : hyps) (ob1 : opbody) (ob2 : opbody) =
    match ob1, ob2 with
    | OP_Plain f1, OP_Plain f2 ->
      check (EcReduction.is_conv ~ri:ri_compatible hyps f1 f2)

    | OP_Plain { f_node = Fop (p, tys) }, _ ->
      let ob1 = get_open_oper (toenv hyps) p tys  in
      for_oper hyps ob1 ob2

    | _, OP_Plain { f_node = Fop (p, tys) } ->
      let ob2 = get_open_oper (toenv hyps) p tys in
      for_oper hyps ob1 ob2

    | OP_Constr (p1, i1), OP_Constr (p2, i2) ->
      check (EcPath.p_equal p1 p2 && i1 = i2)

    | OP_Record p1, OP_Record p2 ->
      check (EcPath.p_equal p1 p2)

    | OP_Proj (p1, i11, i12), OP_Proj (p2, i21, i22) ->
      check (EcPath.p_equal p1 p2 && i11 = i21 && i12 = i22)

    | OP_Fix f1, OP_Fix f2 ->
      for_opfix hyps f1 f2

    | OP_TC, OP_TC -> ()

    | _, _ -> raise CoreIncompatible

  let rec for_pred (hyps : EcEnv.LDecl.hyps) (pb1 : prbody) (pb2 : prbody) =
    match pb1, pb2 with
    | PR_Plain f1, PR_Plain f2 ->
      check (EcReduction.is_conv hyps f1 f2)

    | PR_Plain { f_node = Fop (p, tys) }, _ ->
      let pb1 = get_open_pred (toenv hyps) p tys  in
      for_pred hyps pb1 pb2

    | _, PR_Plain { f_node = Fop (p, tys) } ->
      let pb2 = get_open_pred (toenv hyps) p tys  in
      for_pred hyps pb1 pb2

    | PR_Ind pr1, PR_Ind pr2 ->
      for_ind hyps pr1 pr2

    | _, _ -> raise CoreIncompatible

  let for_nott (hyps : hyps) (nb1 : notation) (nb2 : notation) =
    let s = for_params hyps EcSubst.empty nb1.ont_args nb2.ont_args in
    (* We do not check ont_resty because it is redundant *)
    for_expr hyps s nb1.ont_body nb2.ont_body

  let for_operator (env : EcEnv.env) (oper1 : operator) (oper2 : operator) =
    let params = oper1.op_tparams in

    for_tparams oper1.op_tparams oper2.op_tparams;

    let oty1, okind1 = oper1.op_ty, oper1.op_kind in
    let tparams = List.map (fun (id,_) -> tvar id) params in
    let oty2, okind2 = EcSubst.open_oper oper2 tparams in

    if not (EcReduction.EqTest.for_type env oty1 oty2) then
      raise (Incompatible (DifferentType(oty1, oty2)));

    let hyps = EcEnv.LDecl.init env params in

    try
      match okind1, okind2 with
      | OB_oper None      , OB_oper _          -> ()
      | OB_oper (Some ob1), OB_oper (Some ob2) -> for_oper hyps ob2 ob1
      | OB_pred None      , OB_pred _          -> ()
      | OB_pred (Some pb1), OB_pred (Some pb2) -> for_pred hyps pb2 pb1
      | OB_nott nb1       , OB_nott nb2        -> for_nott hyps nb2 nb1
      | _                 , _                  -> raise (Incompatible OpBody)

    with Failure _ -> raise (Incompatible OpBody)
end

(* -------------------------------------------------------------------- *)
let check_evtags ?(tags : evtags option) (src : symbol list) =
  let exception Reject in

  let explicit = "explicit" in

  try
    match tags with
    | None ->
      if List.mem explicit src then
        raise Reject;
      true

    | Some tags ->
      let dfl =
        not (List.mem explicit src) &&
        not (List.exists (fun (mode, _) -> mode = `Include) tags) in
      let stt =
        List.map (fun src ->
          let do1 status (mode, dst) =
            match mode with
            | `Exclude -> if sym_equal src dst then raise Reject; status
            | `Include -> status || (sym_equal src dst)
          in List.fold_left do1 dfl tags)
          src
      in List.mem true stt

  with Reject -> false

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
let rename ?(fold = true) ove subst (kind, name) =
  try
    let newname =
      match fold with
      | false ->
        List.find_map
          (fun rnm -> EcThCloning.rename rnm (kind, name))
          ove.ovre_rnms
      | _ ->
        let newname =
          List.fold_left (* FIXME:parallel substitution *)
            (fun name rnm ->
              Option.value ~default:name (EcThCloning.rename rnm (kind, name)))
            name ove.ovre_rnms in
        if newname = name then raise Not_found;
        newname
    in

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
      (subst, ops, proofs, ove.ovre_hooks.hadd_item scope ~import item)

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
                tyd_loca    = otyd.tyd_loca; }

            in (decl, ntyd)

        | `ByPath p -> begin
            match EcEnv.Ty.by_path_opt p env with
            | Some reftyd ->
                let tyargs = List.map (fun (x, _) -> EcTypes.tvar x) reftyd.tyd_params in
                let body   = tconstr p tyargs in
                let decl   = { reftyd with tyd_type = `Concrete body; } in
                (decl, body)

            | _ -> assert false
          end

        | `Direct ty -> begin
          assert (List.is_empty otyd.tyd_params);
          let decl  =
            { tyd_params  = [];
              tyd_type    = `Concrete ty;
              tyd_loca    = otyd.tyd_loca; }

          in (decl, ty)
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
                    let newtyargs =
                      List.map
                        (CS.Tvar.subst tysubst -| EcSubst.subst_ty subst)
                        tyargs in
                    EcSubst.add_opdef subst
                      (xpath ove name)
                      (newtparams, e_op np newtparams_ty (toarrow newtyargs newdtype))
                    ) subst octors
                | _ -> subst
              end
            | _, _ -> subst

          in (subst, x) in

      let refotyd = EcSubst.subst_tydecl subst otyd in

      begin
        try Compatible.for_tydecl env refotyd newtyd
        with Incompatible err ->
          clone_error env (CE_TyIncompatible ((snd ove.ovre_prefix, x), err))
      end;

      let scope =
        match mode with
        | `Alias ->
            let item = EcTheory.Th_type (x, newtyd) in
            ove.ovre_hooks.hadd_item scope ~import item

        | `Inline `Keep ->
            let item = EcTheory.Th_type (x, newtyd) in
            ove.ovre_hooks.hadd_item scope ~import:false item

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
      (subst, ops, proofs, ove.ovre_hooks.hadd_item scope ~import (Th_operator (x, oopd)))

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
                try Compatible.for_ty env ue
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

          | `Direct body ->
            assert (List.is_empty refop.op_tparams);
            let newop =
              mk_op
                ~opaque:optransparent ~clinline:(opmode <> `Alias)
                [] body.f_ty (Some (OP_Plain body)) refop.op_loca in
            (newop, body)
  
        in
          match opmode with
          | `Alias ->
              let subst, x = rename ove subst (`Op, x) in
              (newop, subst, x, true)

          | `Inline _ ->
              let body =
                try
                  EcFol.expr_of_form body
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
        try Compatible.for_operator env refop newop
        with Incompatible err ->
          clone_error env (CE_OpIncompatible ((snd ove.ovre_prefix, x), err))
      end;

      let scope =
        match opmode with
        | `Alias ->
            let item = Th_operator (x, newop) in
            ove.ovre_hooks.hadd_item scope ~import item

        | `Inline `Keep ->
            let item = Th_operator (x, newop) in
            ove.ovre_hooks.hadd_item scope ~import:false item

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
      (subst, ops, proofs, ove.ovre_hooks.hadd_item scope ~import (Th_operator (x, oopr)))

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
                Compatible.for_ty env ue
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

        | `Direct body ->
          assert (List.is_empty refpr.op_tparams);
          let newpr   =
            { op_tparams  = [];
              op_ty       = body.f_ty;
              op_kind     = OB_pred (Some (PR_Plain body));
              op_opaque   = oopr.op_opaque;
              op_clinline = prmode <> `Alias;
              op_loca     = refpr.op_loca;
              op_unfold   = refpr.op_unfold; } in
          (newpr, body)
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
      try Compatible.for_operator env refpr newpr
      with Incompatible err ->
        clone_error env (CE_OpIncompatible ((snd ove.ovre_prefix, x), err))
    end;

    let scope =
      match prmode with
      | `Alias ->
          let item = Th_operator (x, newpr) in
          ove.ovre_hooks.hadd_item scope ~import item

      | `Inline `Keep ->
          let item = Th_operator (x, newpr) in
          ove.ovre_hooks.hadd_item scope ~import:false item

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
      let scope = ove.ovre_hooks.hadd_item scope ~import item in
      (subst, ops, proofs, scope)

  | Some { pl_desc = (_, mode) } -> begin
    match mode with
    | `Alias | `Inline `Keep ->
      let subst, x = rename ove subst (`Op, x) in
      let oont = EcSubst.subst_op subst oont in
      let item = Th_operator (x, oont) in
      let scope = ove.ovre_hooks.hadd_item scope ~import item in
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
          List.Exceptionless.find_map (function
            | (pt, None) ->
              if check_evtags (Ssym.elements tags) then
                Some (pt, `Alias, false)
              else None
            | (pt, Some pttags) ->
               if check_evtags ~tags:pttags (Ssym.elements tags) then
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
          let ax  = { ax with ax_kind = `Lemma } in
          let axc = { axc_axiom = (x, ax);
                      axc_path  = EcPath.fromqsymbol (snd ove.ovre_prefix, x);
                      axc_tac   = pt;
                      axc_env   = scenv; } in
            (ax, axc :: proofs, axclear || hide = `Inline `Clear) in

  let scope =
    if axclear then scope else
      ove.ovre_hooks.hadd_item scope ~import (Th_axiom(x, ax))
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
      (subst, ops, proofs, ove.ovre_hooks.hadd_item scope ~import item)

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
          ove.ovre_hooks.hadd_item scope ~import item
        else scope
      in (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_mod
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, (me : top_module_expr))
=
    let subst, name = rename ove subst (`Module, me.tme_expr.me_name) in
    let me = EcSubst.subst_top_module subst me in
    let me = { me with tme_expr = { me.tme_expr with me_name = name } } in
    let item = (Th_module me) in
    (subst, ops, proofs, ove.ovre_hooks.hadd_item scope ~import item)

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
    let scope = ove.ovre_hooks.hadd_item scope ~import (Th_export (p, lc)) in
    (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_baserw
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, name, lc)
=
  let scope = ove.ovre_hooks.hadd_item scope ~import (Th_baserw (name, lc)) in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_addrw
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, p, l, lc)
=
  let p     = EcSubst.subst_path subst p in
  let l     = List.map (EcSubst.subst_path subst) l in
  let scope = ove.ovre_hooks.hadd_item scope ~import (Th_addrw (p, l, lc)) in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_auto
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, at_base)
=
  let env = EcSection.env (ove.ovre_hooks.henv scope) in
  let axioms = List.map (fst_map (EcSubst.subst_path subst)) at_base.axioms in
  let axioms = List.filter (fun (p, _) -> Option.is_some (EcEnv.Ax.by_path_opt p env)) axioms in
  let scope = ove.ovre_hooks.hadd_item scope ~import (Th_auto { at_base with axioms }) in
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
  let scope = ove.ovre_hooks.hadd_item scope ~import (Th_reduction rules) in

  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_typeclass
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, x, tc)
=
  let tc = EcSubst.subst_tc subst tc in
  let scope = ove.ovre_hooks.hadd_item scope ~import (Th_typeclass (x, tc)) in
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

    let scope = ove.ovre_hooks.hadd_item scope ~import (Th_instance ((typ, ty), tc, lc)) in
    (subst, ops, proofs, scope)

  with E.InvInstPath ->
    (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_alias
  (ove : _ ovrenv) (subst, ops, proofs, scope) (import, name, target)
=
  let scenv = ove.ovre_hooks.henv scope in
  let env = EcSection.env scenv in
  let p = EcSubst.subst_path subst target in

  if is_none (EcEnv.Theory.by_path_opt p env) then
    (subst, ops, proofs, scope)
  else
    let scope = ove.ovre_hooks.hadd_item scope ~import (Th_alias (name, target)) in
    (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay1 (ove : _ ovrenv) (subst, ops, proofs, scope) (hidden, item) =
  let import = not hidden && item.ti_import in

  match item.ti_item with
  | Th_type (x, otyd) ->
     replay_tyd ove (subst, ops, proofs, scope) (import, x, otyd)

  | Th_operator (x, ({ op_kind = OB_oper _ } as oopd)) ->
     replay_opd ove (subst, ops, proofs, scope) (import, x, oopd)

  | Th_operator (x, ({ op_kind = OB_pred _} as oopr)) ->
     replay_prd ove (subst, ops, proofs, scope) (import, x, oopr)

  | Th_operator (x, ({ op_kind = OB_nott _} as oont)) ->
     replay_ntd ove (subst, ops, proofs, scope) (import, x, oont)

  | Th_axiom (x, ax) ->
     replay_axd ove (subst, ops, proofs, scope) (import, x, ax)

  | Th_modtype (x, modty) ->
     replay_modtype ove (subst, ops, proofs, scope) (import, x, modty)

  | Th_module me ->
     replay_mod ove (subst, ops, proofs, scope) (import, me)

  | Th_export (p, lc) ->
     replay_export ove (subst, ops, proofs, scope) (import, p, lc)

  | Th_baserw (x, lc) ->
     replay_baserw ove (subst, ops, proofs, scope) (import, x, lc)

  | Th_addrw (p, l, lc) ->
     replay_addrw ove (subst, ops, proofs, scope) (import, p, l, lc)

  | Th_reduction rules ->
     replay_reduction ove (subst, ops, proofs, scope) (import, rules)

  | Th_auto at_base ->
     replay_auto ove (subst, ops, proofs, scope) (import, at_base)

  | Th_typeclass (x, tc) ->
     replay_typeclass ove (subst, ops, proofs, scope) (import, x, tc)

  | Th_instance ((typ, ty), tc, lc) ->
     replay_instance ove (subst, ops, proofs, scope) (import, (typ, ty), tc, lc)

  | Th_alias (name, target) ->
     replay_alias ove (subst, ops, proofs, scope) (item.ti_import, name, target)

  | Th_theory (ox, cth) -> begin
      let thmode = cth.cth_mode in
      let (subst, x) = rename ove subst (`Theory, ox) in
      let subovrds = Msym.find_opt ox ove.ovre_ovrd.evc_ths in
      let subovrds = EcUtils.odfl (evc_empty, false) subovrds in
      let subovrds, clear = subovrds in
      let hidden = hidden || clear in
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
        let new_local = odfl cth.cth_loca ove.ovre_local in
        let subscope = ove.ovre_hooks.hthenter scope thmode x new_local in
        let (subst, ops, proofs, subscope) =
          List.fold_left
            (fun state item -> replay1 subove state (hidden, item))
            (subst, ops, proofs, subscope) cth.cth_items in
        let scope = ove.ovre_hooks.hthexit ~import:(not hidden) subscope `Full in
        (subst, ops, proofs, scope)

      in (subst, ops, proofs, subscope)
  end

(* -------------------------------------------------------------------- *)
let replay (hooks : 'a ovrhooks)
  ~abstract ~override_locality ~incl ~clears ~renames
  ~opath ~npath ovrds (scope : 'a) (name, hidden, items, base_local)
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
    ovre_local    = override_locality;
    ovre_hooks    = hooks;
    ovre_glproof  = ovrds.evc_lemmas.ev_global;
  } in

  let mode  = if abstract then `Abstract else `Concrete in
  let new_local = odfl base_local override_locality in
  let scope = if incl then scope else hooks.hthenter scope mode name new_local in
  try
    let _, _, proofs, scope =
      List.fold_left
        (fun state item -> replay1 ove state (hidden, item))
        (subst, Mp.empty, [], scope) items in
     let scope = if incl then scope else hooks.hthexit scope ~import:true `No in
    (List.rev proofs, scope)

  with EcEnv.DuplicatedBinding x ->
    hooks.herr
      (Printf.sprintf "name clash for `%s': check your renamings" x)
