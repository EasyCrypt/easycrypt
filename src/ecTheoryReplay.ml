(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* ------------------------------------------------------------------ *)
open EcSymbols
open EcUtils
open EcLocation
open EcParsetree
open EcTypes
open EcDecl
open EcModules
open EcTheory
open EcThCloning

module Sp = EcPath.Sp
module Mp = EcPath.Mp

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
  ovre_prefix   : symbol list;
  ovre_glproof  : (ptactic_core option * evtags option) list;
  ovre_abstract : bool;
  ovre_local    : bool;
  ovre_hooks    : 'a ovrhooks;
}

and 'a ovrhooks = {
  henv     : 'a -> EcEnv.env;
  hty      : 'a -> (symbol * tydecl) -> 'a;
  hop      : 'a -> (symbol * operator) -> 'a;
  hmodty   : 'a -> (symbol * module_sig) -> 'a;
  hmod     : 'a -> bool -> module_expr -> 'a;
  hax      : 'a -> bool -> (symbol * axiom) -> 'a;
  hexport  : 'a -> EcPath.path -> 'a;
  hbaserw  : 'a -> symbol -> 'a;
  haddrw   : 'a -> EcPath.path * EcPath.path list -> 'a;
  hauto    : 'a -> bool * Sp.t -> 'a;
  htycl    : 'a -> symbol * typeclass -> 'a;
  hinst    : 'a -> (ty_params * ty) * tcinstance -> 'a;
  hthenter : 'a -> thmode -> symbol -> 'a;
  hthexit  : 'a -> [`Full | `ClearOnly | `No] -> 'a;
  herr     : 'b . ?loc:EcLocation.t -> string -> 'b;
}

(* -------------------------------------------------------------------- *)
exception Incompatible of incompatible

let ty_compatible env ue (rtyvars, rty) (ntyvars, nty) =
  let rlen = List.length rtyvars and nlen = List.length ntyvars in
  if rlen <> nlen then
    raise (Incompatible (NotSameNumberOfTyParam(rlen,nlen)));

  let subst = Tvar.init rtyvars (List.map tvar ntyvars) in
  let rty   = Tvar.subst subst rty in

  try  EcUnify.unify env ue rty nty
  with EcUnify.UnificationFailure _ ->
    raise (Incompatible (DifferentType (rty, nty)))

(* -------------------------------------------------------------------- *)
let check_evtags (tags : evtags) (src : symbol list) =
  let module E = struct exception Reject end in

  try
    let dfl = not (List.exists (fun (mode, _) -> mode = `Include) tags) in
    let stt =
      List.map (fun src ->
        let rec do1 status (mode, dst) =
          match mode with
          | `Exclude -> if sym_equal src dst then raise E.Reject; status
          | `Include -> status || (sym_equal src dst)
        in List.fold_left do1 dfl tags)
        src
    in List.mem true stt

  with E.Reject -> false

(* -------------------------------------------------------------------- *)
let xpath ove x =
  EcPath.pappend ove.ovre_opath (EcPath.fromqsymbol (ove.ovre_prefix, x))

(* -------------------------------------------------------------------- *)
let xnpath ove x =
  EcPath.pappend ove.ovre_npath (EcPath.fromqsymbol (ove.ovre_prefix, x))

(* -------------------------------------------------------------------- *)
let rename ove subst (kind, name) =
  try
    let newname =
      List.find_map
        (fun rnm -> EcThCloning.rename rnm (kind, name))
        ove.ovre_rnms in
    let subst =
      EcSubst.add_path subst
        ~src:(xpath ove name) ~dst:(xnpath ove newname)
    in (subst, newname)

  with Not_found -> (subst, name)

(* -------------------------------------------------------------------- *)
let rec replay_tyd (ove : _ ovrenv) (subst, ops, proofs, scope) (x, otyd) =
  let scenv = ove.ovre_hooks.henv scope in

  match Msym.find_opt x ove.ovre_ovrd.evc_types with
  | None ->
      let otyd = EcSubst.subst_tydecl subst otyd in
      let subst, x = rename ove subst (`Type, x) in
      (subst, ops, proofs, ove.ovre_hooks.hty scope (x, otyd))

  | Some { pl_desc = (nargs, ntyd, mode) } -> begin
      let nargs = List.map2
                    (fun (_, tc) x -> (EcIdent.create (unloc x), tc))
                    otyd.tyd_params nargs in
      let ue    = EcUnify.UniEnv.create (Some nargs) in
      let ntyd  = EcTyping.transty EcTyping.tp_tydecl scenv ue ntyd in

      match mode with
      | `Alias ->
          let binding =
            { tyd_params = nargs;
              tyd_type   = `Concrete ntyd; } in
          let subst, x = rename ove subst (`Type, x) in
          (subst, ops, proofs, ove.ovre_hooks.hty scope (x, binding))

      | `Inline ->
          let subst =
            EcSubst.add_tydef subst (xpath ove x) (List.map fst nargs, ntyd)
          in (subst, ops, proofs, scope)
  end

(* -------------------------------------------------------------------- *)
and replay_opd (ove : _ ovrenv) (subst, ops, proofs, scope) (x, oopd) =
  let scenv = ove.ovre_hooks.henv scope in

  match Msym.find_opt x ove.ovre_ovrd.evc_ops with
  | None ->
      let (subst, x) = rename ove subst (`Op, x) in
      let oopd = EcSubst.subst_op subst oopd in
      (subst, ops, proofs, ove.ovre_hooks.hop scope (x, oopd))

  | Some { pl_desc = (opov, opmode); pl_loc = loc; } ->
      let (reftyvars, refty) =
        let refop = EcSubst.subst_op subst oopd in
        (refop.op_tparams, refop.op_ty)
      in

      let (newop, subst, x, alias) =
        let tp = opov.opov_tyvars |> omap (List.map (fun tv -> (tv, []))) in
        let ue = EcTyping.transtyvars scenv (loc, tp) in
        let tp = EcTyping.tp_relax in
        let (ty, body) =
          let env     = scenv in
          let codom   = EcTyping.transty tp env ue opov.opov_retty in
          let env, xs = EcTyping.trans_binding env ue opov.opov_args in
          let body    = EcTyping.transexpcast env `InOp ue codom opov.opov_body in
          let lam     = EcTypes.e_lam xs body in

          (lam.EcTypes.e_ty, lam)
        in

        begin
          try ty_compatible scenv ue
              (List.map fst reftyvars, refty)
              (List.map fst (EcUnify.UniEnv.tparams ue), ty)
          with Incompatible err ->
            clone_error scenv (CE_OpIncompatible ((ove.ovre_prefix, x), err))
        end;

        if not (EcUnify.UniEnv.closed ue) then
          ove.ovre_hooks.herr
            ~loc "this operator body contains free type variables";

        let uni     = EcTypes.Tuni.offun (EcUnify.UniEnv.close ue) in
        let body    = body |> EcTypes.e_mapty uni in
        let ty      = uni ty in
        let tparams = EcUnify.UniEnv.tparams ue in
        let newop   = mk_op tparams ty (Some (OP_Plain body)) in
          match opmode with
          | `Alias ->
              let subst, x = rename ove subst (`Op, x) in
              (newop, subst, x, true)

          | `Inline ->
              let subst1 = (List.map fst tparams, body) in
              let subst  = EcSubst.add_opdef subst (xpath ove x) subst1
              in  (newop, subst, x, false)
      in

      let ops =
        let opp = EcPath.fromqsymbol (ove.ovre_prefix, x) in
        Mp.add opp (newop, alias) ops in
      let scope =
        if alias then ove.ovre_hooks.hop scope (x, newop) else scope

      in (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_prd (ove : _ ovrenv) (subst, ops, proofs, scope) (x, oopr) =
  let scenv = ove.ovre_hooks.henv scope in

  match Msym.find_opt x ove.ovre_ovrd.evc_preds with
  | None ->
      let subst, x = rename ove subst (`Pred, x) in
      let oopr = EcSubst.subst_op subst oopr in
      (subst, ops, proofs, ove.ovre_hooks.hop scope (x, oopr))

  | Some { pl_desc = (prov, prmode); pl_loc = loc; } ->
      let (reftyvars, refty) =
        let refpr = EcSubst.subst_op subst oopr in
          (refpr.op_tparams, refpr.op_ty)
      in

      let (newpr, subst, x, alias) =
         let tp = prov.prov_tyvars |> omap (List.map (fun tv -> (tv, []))) in
         let ue = EcTyping.transtyvars scenv (loc, tp) in
         let body =
           let env     = scenv in
           let env, xs = EcTyping.trans_binding env ue prov.prov_args in
           let body    = EcTyping.trans_form_opt env ue prov.prov_body None in
           let xs      = List.map (fun (x, ty) -> x, EcFol.GTty ty) xs in
           let lam     = EcFol.f_lambda xs body in
           lam
         in

         begin
           try
             ty_compatible scenv ue
               (List.map fst reftyvars, refty)
               (List.map fst (EcUnify.UniEnv.tparams ue), body.EcFol.f_ty)
           with Incompatible err ->
             clone_error scenv
               (CE_OpIncompatible ((ove.ovre_prefix, x), err))
         end;

         if not (EcUnify.UniEnv.closed ue) then
           ove.ovre_hooks.herr
             ~loc "this predicate body contains free type variables";

         let uni     = EcUnify.UniEnv.close ue in
         let body    = EcFol.Fsubst.uni uni body in
         let tparams = EcUnify.UniEnv.tparams ue in
         let newpr   =
           { op_tparams = tparams;
             op_ty      = body.EcFol.f_ty;
             op_kind    = OB_pred (Some (PR_Plain body)); } in

          match prmode with
          | `Alias ->
            let subst, x = rename ove subst (`Pred, x) in
            (newpr, subst, x, true)

          | `Inline ->
              let subst1 = (List.map fst tparams, body) in
              let subst  = EcSubst.add_pddef subst (xpath ove x) subst1
              in (newpr, subst, x, false)

      in

      let scope =
        if alias then ove.ovre_hooks.hop scope (x, newpr) else scope
      in (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_ntd (ove : _ ovrenv) (subst, ops, proofs, scope) (x, oont) =
  if EcPath.Sp.mem (xpath ove x) ove.ovre_ntclr then
    (subst, ops, proofs, scope)
  else
    let subst, x = rename ove subst (`Op, x) in
    let oont = EcSubst.subst_op subst oont in
    let scope = ove.ovre_hooks.hop scope (x, oont) in
    (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_axd (ove : _ ovrenv) (subst, ops, proofs, scope) (x, ax) =
  let scenv = ove.ovre_hooks.henv scope in
  let subst, x = rename ove subst (`Lemma, x) in
  let ax = EcSubst.subst_ax subst ax in
  let (ax, proofs, axclear) =
    if ove.ovre_abstract then (ax, proofs, false) else

    let doproof =
      match ax.ax_kind with
      | `Lemma -> None
      | `Axiom (tags, axclear) -> begin
          match Msym.find_opt x (ove.ovre_ovrd.evc_lemmas.ev_bynames) with
          | Some pt -> Some (pt, axclear)
          | None ->
              List.Exceptionless.find_map
                (function (pt, None) -> Some (pt, axclear) | (pt, Some pttags) ->
                   if check_evtags pttags (Ssym.elements tags) then
                     Some (pt, axclear)
                   else None)
                ove.ovre_glproof
      end
    in
      match doproof with
      | None -> (ax, proofs, false)
      | Some (pt, axclear)  ->
          let ax  = { ax with ax_kind = `Lemma } in
          let axc = { axc_axiom = (x, ax);
                      axc_path  = EcPath.fromqsymbol (ove.ovre_prefix, x);
                      axc_tac   = pt;
                      axc_env   = scenv; } in
            (ax, axc :: proofs, axclear) in

  let scope =
    if axclear then scope else
      ove.ovre_hooks.hax scope ove.ovre_local (x, ax)
  in (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_modtype
  (ove : _ ovrenv) (subst, ops, proofs, scope) (x, modty)
=
  let subst, x = rename ove subst (`ModType, x) in
  let modty = EcSubst.subst_modsig subst modty in
  (subst, ops, proofs, ove.ovre_hooks.hmodty scope (x, modty))

(* -------------------------------------------------------------------- *)
and replay_mod
  (ove : _ ovrenv) (subst, ops, proofs, scope) me
=
  let subst, name = rename ove subst (`Module, me.me_name) in
  let me = EcSubst.subst_module subst me in
  let me = { me with me_name = name } in
  (subst, ops, proofs, ove.ovre_hooks.hmod scope ove.ovre_local me)

(* -------------------------------------------------------------------- *)
and replay_export
  (ove : _ ovrenv) (subst, ops, proofs, scope) p
=
  let scenv = ove.ovre_hooks.henv scope in
  let p = EcSubst.subst_path subst p in

  if is_none (EcEnv.Theory.by_path_opt p scenv) then
    (subst, ops, proofs, scope)
  else
    let scope = ove.ovre_hooks.hexport scope p in
    (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_baserw
  (ove : _ ovrenv) (subst, ops, proofs, scope) name
=
  let scope = ove.ovre_hooks.hbaserw scope name in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_addrw
  (ove : _ ovrenv) (subst, ops, proofs, scope) (p, l)
=
  let p     = EcSubst.subst_path subst p in
  let l     = List.map (EcSubst.subst_path subst) l in
  let scope = ove.ovre_hooks.haddrw scope (p, l) in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_auto
  (ove : _ ovrenv) (subst, ops, proofs, scope) (lc, ps)
=
  let ps = Sp.map (EcSubst.subst_path subst) ps in
  let scope = ove.ovre_hooks.hauto scope (lc, ps) in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_typeclass
  (ove : _ ovrenv) (subst, ops, proofs, scope) (x, tc)
=
  let tc = EcSubst.subst_tc subst tc in
  let scope = ove.ovre_hooks.htycl scope (x, tc) in
  (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay_instance
  (ove : _ ovrenv) (subst, ops, proofs, scope) ((typ, ty), tc)
=
  let opath = ove.ovre_opath in
  let npath = ove.ovre_npath in

  let module E = struct exception InvInstPath end in

  let forpath (p : EcPath.path) =
    match EcPath.getprefix opath p |> omap List.rev with
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
                | OB_oper (Some (OP_Plain e)) ->
                    match e.EcTypes.e_node with
                    | EcTypes.Eop (r, _) -> Some r
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

    let scope = ove.ovre_hooks.hinst scope ((typ, ty), tc) in
    (subst, ops, proofs, scope)

  with E.InvInstPath ->
    (subst, ops, proofs, scope)

(* -------------------------------------------------------------------- *)
and replay1 (ove : _ ovrenv) (subst, ops, proofs, scope) item =
  match item with
  | CTh_type (x, otyd) ->
     replay_tyd ove (subst, ops, proofs, scope) (x, otyd)

  | CTh_operator (x, ({ op_kind = OB_oper _ } as oopd)) ->
     replay_opd ove (subst, ops, proofs, scope) (x, oopd)

  | CTh_operator (x, ({ op_kind = OB_pred _} as oopr)) ->
     replay_prd ove (subst, ops, proofs, scope) (x, oopr)

  | CTh_operator (x, ({ op_kind = OB_nott _} as oont)) ->
     replay_ntd ove (subst, ops, proofs, scope) (x, oont)

  | CTh_axiom (x, ax) ->
     replay_axd ove (subst, ops, proofs, scope) (x, ax)

  | CTh_modtype (x, modty) ->
     replay_modtype ove (subst, ops, proofs, scope) (x, modty)

  | CTh_module me ->
     replay_mod ove (subst, ops, proofs, scope) me

  | CTh_export p ->
     replay_export ove (subst, ops, proofs, scope) p

  | CTh_baserw x ->
     replay_baserw ove (subst, ops, proofs, scope) x

  | CTh_addrw (p, l) ->
     replay_addrw ove (subst, ops, proofs, scope) (p, l)

  | CTh_auto (lc, ps) ->
     replay_auto ove (subst, ops, proofs, scope) (lc, ps)

  | CTh_typeclass (x, tc) ->
     replay_typeclass ove (subst, ops, proofs, scope) (x, tc)

  | CTh_instance ((typ, ty), tc) ->
     replay_instance ove (subst, ops, proofs, scope) ((typ, ty), tc)

  | CTh_theory (x, (cth, thmode)) -> begin
      let (subst, x) = rename ove subst (`Theory, x) in
      let subovrds = Msym.find_opt x ove.ovre_ovrd.evc_ths in
      let subovrds = EcUtils.odfl evc_empty subovrds in
      let subove   = { ove with
        ovre_ovrd     = subovrds;
        ovre_abstract = ove.ovre_abstract || (thmode = `Abstract);
        ovre_prefix   = ove.ovre_prefix @ [x];
        ovre_glproof  =
          if   List.is_empty subovrds.evc_lemmas.ev_global
          then ove.ovre_glproof
          else subovrds.evc_lemmas.ev_global; }
      in

      let (subst, ops, proofs, subscope) =
        let subscope = ove.ovre_hooks.hthenter scope thmode x in
        let (subst, ops, proofs, subscope) =
          List.fold_left (replay1 subove)
            (subst, ops, proofs, subscope) cth.cth_struct in
        let scope = ove.ovre_hooks.hthexit subscope `Full in
        (subst, ops, proofs, scope)

      in (subst, ops, proofs, subscope)
  end

(* -------------------------------------------------------------------- *)
let replay (hooks : 'a ovrhooks)
  ~abstract ~local ~incl ~clears ~renames
  ~opath ~npath ovrds (scope : 'a) (name, items)
=
  let subst = EcSubst.add_path EcSubst.empty opath npath in
  let ove   = {
    ovre_ovrd     = ovrds;
    ovre_rnms     = renames;
    ovre_ntclr    = clears;
    ovre_opath    = opath;
    ovre_npath    = npath;
    ovre_prefix   = [];
    ovre_abstract = abstract;
    ovre_local    = local;
    ovre_hooks    = hooks;
    ovre_glproof  = ovrds.evc_lemmas.ev_global;
  } in

  try
    let mode  = if abstract then `Abstract else `Concrete in
    let scope = if incl then scope else hooks.hthenter scope mode name in
    let _, _, proofs, scope =
      List.fold_left (replay1 ove)
        (subst, Mp.empty, [], scope) items in
     let scope = if incl then scope else hooks.hthexit scope `No in
    (List.rev proofs, scope)

  with EcEnv.DuplicatedBinding x ->
    hooks.herr
      (Printf.sprintf "name clash for `%s': check your renamings" x)
