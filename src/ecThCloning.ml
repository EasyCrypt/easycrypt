(* ------------------------------------------------------------------ *)
open EcUtils
open EcSymbols
open EcLocation
open EcParsetree
open EcDecl
open EcModules
open EcTheory

(* ------------------------------------------------------------------ *)
type evclone = {
  evc_types : (psymbol list * pty) Msym.t;
  evc_ops   : (psymbol list * pexpr) Msym.t;
}

let evc_empty = {
  evc_types = Msym.empty;
  evc_ops   = Msym.empty;
}

let clone (scenv : EcEnv.env) (thcl : theory_cloning) =
  let cpath = EcEnv.root scenv in

  let opath, oth = EcEnv.Theory.lookup (unloc thcl.pthc_base) scenv in
  let name  = odfl (EcPath.basename opath) (omap thcl.pthc_name unloc) in
  let npath = EcPath.pqname cpath name in
  let subst = EcSubst.add_path EcSubst.empty opath npath in

  let ovrds =
    let do1 evc (x, ovrd) =
      let x = unloc x in
        match ovrd with
        | PTHO_Type tyd ->
          begin
            if Msym.mem x evc.evc_types then
              failwith "duplicated-type-override";
            match EcEnv.Ty.by_path_opt (EcPath.pqname opath x) scenv with
            | None ->
                failwith "non-existent-type-override"
            | Some { EcDecl.tyd_type = Some _ } ->
                failwith "concrete-type-cloning"
            | _ -> ()
          end;
          { evc with evc_types = Msym.add x tyd evc.evc_types }

        | PTHO_Op opd ->
          begin
            if Msym.mem x evc.evc_ops then
              failwith "duplicated-op-override";
            match EcEnv.Op.by_path_opt (EcPath.pqname opath x) scenv with
            | None
            | Some { op_kind = OB_pred _ } ->
                failwith "non-existent-op-override";
            | Some { op_kind = OB_oper (Some _) } ->
                failwith "concrete-operator-cloning"
            | _ -> ()
          end;
          { evc with evc_ops = Msym.add x opd evc.evc_ops }
    in
      List.fold_left do1 evc_empty thcl.pthc_ext
  in

  let nth =
    let ovr1 scenv item =
      match item with
      | CTh_type (x, otyd) -> begin
          match Msym.find_opt x ovrds.evc_types with
          | None -> EcEnv.Ty.bind x (EcSubst.subst_tydecl subst otyd) scenv
          | Some (nargs, ntyd) ->
            let refty = EcEnv.Ty.by_path (EcPath.pqname opath x) scenv in
              if List.length refty.tyd_params <> List.length nargs then
                failwith "type-override-parameters-count-mismatch";
              if refty.tyd_type <> None then
                failwith "type-override-of-non-abstract";

              let nargs = List.map (EcIdent.create -| unloc) nargs in
              let ue    = EcUnify.UniEnv.create (Some nargs) in
              let ntyd  = EcTyping.transty EcTyping.tp_tydecl scenv ue ntyd in

              let binding =
                { tyd_params = nargs;
                  tyd_type   = Some ntyd; }
              in
                EcEnv.Ty.bind x binding scenv
      end

      | CTh_operator (x, ({ op_kind = OB_oper None } as oopd)) -> begin
          match Msym.find_opt x ovrds.evc_ops with
          | None -> EcEnv.Op.bind x (EcSubst.subst_op subst oopd) scenv
          | Some (locals, opbody) ->
              assert (locals = []);

              let refop = EcEnv.Op.by_path (EcPath.pqname opath x) scenv in
              let newop = EcSubst.subst_op subst refop in

(*
              let locals = List.map (EcIdent.create -| unloc) locals in
              let benv   = EcEnv.Var.bind_locals (List.combine locals newop.op_dom) scenv in
*)

              let benv = scenv in
              let ue   = EcUnify.UniEnv.create (Some newop.op_tparams) in

              let opbody = EcTyping.transexpcast benv ue newop.op_ty opbody in

                if List.length (EcUnify.UniEnv.tparams ue) <> List.length newop.op_tparams then
                  failwith "body-less-generic";

              let newop =
                { newop with op_kind = OB_oper (Some opbody) }
              in
                EcEnv.Op.bind x newop scenv
        end

      | CTh_operator (x, oopd) ->
          EcEnv.Op.bind x (EcSubst.subst_op subst oopd) scenv

      | CTh_axiom (x, ax) ->
          EcEnv.Ax.bind x (EcSubst.subst_ax subst ax) scenv

      | CTh_modtype (x, modty) ->
          EcEnv.ModTy.bind x (EcSubst.subst_modsig subst modty) scenv

      | CTh_module me ->
          EcEnv.Mod.bind me.me_name (EcSubst.subst_module subst me) scenv

      | CTh_theory (x, cth) ->
          EcEnv.Theory.bindx x (EcSubst.subst_ctheory subst cth) scenv

      | CTh_export p ->               (* FIXME: subst in p? *)
          EcEnv.Theory.export p scenv
    in
      let scenv = EcEnv.Theory.enter name scenv in
      let scenv = List.fold_left ovr1 scenv oth.cth_struct in
        EcEnv.Theory.close scenv
  in
    (name, nth)
