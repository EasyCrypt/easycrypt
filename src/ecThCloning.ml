(* ------------------------------------------------------------------ *)
open EcUtils
open EcSymbols
open EcLocation
open EcParsetree
open EcDecl
open EcModules
open EcTheory

(* ------------------------------------------------------------------ *)
type ovkind =
| OVK_Type
| OVK_Operator

type clone_error =
| CE_DupOverride   of ovkind * symbol
| CE_UnkOverride   of ovkind * symbol
| CE_CrtOverride   of ovkind * symbol
| CE_TypeArgMism   of ovkind * symbol
| CE_OpBodyLessGen of symbol

exception CloneError of EcEnv.env * clone_error

let clone_error env error =
  raise (CloneError (env, error))

(* -------------------------------------------------------------------- *)
let string_of_ovkind = function
  | OVK_Type     -> "type"
  | OVK_Operator -> "operator"

(* -------------------------------------------------------------------- *)
let pp_clone_error fmt _env error =
  let msg x = Format.fprintf fmt x in

  match error with
  | CE_DupOverride (kd, x) ->
      msg "the %s `%s' is instantiate twice"
        (string_of_ovkind kd) x

  | CE_UnkOverride (kd, x) ->
      msg "unknown %s `%s'"
        (string_of_ovkind kd) x

  | CE_CrtOverride (kd, x) ->
      msg "cannot instantiate the _concrete_ %s `%s'"
        (string_of_ovkind kd) x

  | CE_TypeArgMism (kd, x) ->
      msg "type argument mismatch for %s `%s'"
        (string_of_ovkind kd) x

  | CE_OpBodyLessGen x ->
      msg "operator `%s' body type is not generic enough" x

let () =
  let pp fmt exn =
    match exn with
    | CloneError (env, e) -> pp_clone_error fmt env e
    | _ -> raise exn
  in
    EcPException.register pp

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
              clone_error scenv (CE_DupOverride (OVK_Type, x));
            match EcEnv.Ty.by_path_opt (EcPath.pqname opath x) scenv with
            | None ->
                clone_error scenv (CE_UnkOverride (OVK_Type, x));
            | Some { EcDecl.tyd_type = Some _ } ->
                clone_error scenv (CE_CrtOverride (OVK_Type, x));
            | Some refty ->
                if List.length refty.tyd_params <> List.length (fst tyd) then
                  clone_error scenv (CE_TypeArgMism (OVK_Type, x));
          end;
          { evc with evc_types = Msym.add x tyd evc.evc_types }

        | PTHO_Op opd ->
          begin
            if Msym.mem x evc.evc_ops then
              clone_error scenv (CE_DupOverride (OVK_Operator, x));
            match EcEnv.Op.by_path_opt (EcPath.pqname opath x) scenv with
            | None
            | Some { op_kind = OB_pred _ } ->
                clone_error scenv (CE_UnkOverride (OVK_Operator, x));
            | Some { op_kind = OB_oper (Some _) } ->
                clone_error scenv (CE_CrtOverride (OVK_Operator, x));
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
          | None ->
              EcEnv.Ty.bind x (EcSubst.subst_tydecl subst otyd) scenv

          | Some (nargs, ntyd) ->
              (* Already checked:
               *   1. type is abstract
               *   2. type argument count are equal *)
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
                  clone_error scenv (CE_OpBodyLessGen x);

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
