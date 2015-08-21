(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* ------------------------------------------------------------------ *)
open EcUtils
open EcSymbols
open EcLocation
open EcParsetree
open EcDecl
open EcTheory

module Mp = EcPath.Mp

(* ------------------------------------------------------------------ *)
type incompatible =
| NotSameNumberOfTyParam of int * int 
| DifferentType of EcTypes.ty * EcTypes.ty

type ovkind =
| OVK_Type
| OVK_Operator
| OVK_Predicate
| OVK_Theory
| OVK_Lemma

type clone_error =
| CE_UnkTheory      of qsymbol
| CE_DupOverride    of ovkind * qsymbol
| CE_UnkOverride    of ovkind * qsymbol
| CE_CrtOverride    of ovkind * qsymbol
| CE_TypeArgMism    of ovkind * qsymbol
| CE_OpIncompatible of qsymbol * incompatible
| CE_PrIncompatible of qsymbol * incompatible
| CE_InvalidRE      of string

exception CloneError of EcEnv.env * clone_error

let clone_error env error =
  raise (CloneError (env, error))

(* -------------------------------------------------------------------- *)
let string_of_ovkind = function
  | OVK_Type      -> "type"
  | OVK_Operator  -> "operator"
  | OVK_Predicate -> "predicate"
  | OVK_Theory    -> "theory"
  | OVK_Lemma     -> "lemma/axiom"

(* -------------------------------------------------------------------- *)
type axclone = {
  axc_axiom : symbol * EcDecl.axiom;
  axc_path  : EcPath.path;
  axc_env   : EcEnv.env;
  axc_tac   : EcParsetree.ptactic_core option;
}

(* -------------------------------------------------------------------- *)
let pp_incompatible env fmt = function
  | NotSameNumberOfTyParam(exp, got) ->
    Format.fprintf fmt "contains %i type parameter instead of %i" got exp
  | DifferentType(exp,got) ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    Format.fprintf fmt "has type %a instead of %a" 
      (EcPrinting.pp_type ppe) got  (EcPrinting.pp_type ppe) exp

let pp_clone_error fmt env error =
  let msg x = Format.fprintf fmt x in

  match error with
  | CE_UnkTheory name ->
      msg "cannot find theory to clone: `%s'"
        (string_of_qsymbol name)

  | CE_DupOverride (kd, x) ->
      msg "the %s `%s' is instantiate twice"
        (string_of_ovkind kd) (string_of_qsymbol x)

  | CE_UnkOverride (kd, x) ->
      msg "unknown %s `%s'"
        (string_of_ovkind kd) (string_of_qsymbol x)

  | CE_CrtOverride (kd, x) ->
      msg "cannot instantiate the _concrete_ %s `%s'"
        (string_of_ovkind kd) (string_of_qsymbol x)

  | CE_TypeArgMism (kd, x) ->
      msg "type argument mismatch for %s `%s'"
        (string_of_ovkind kd) (string_of_qsymbol x)

  | CE_OpIncompatible (x, err) ->
      msg "operator `%s' body %a"
        (string_of_qsymbol x) (pp_incompatible env) err

  | CE_PrIncompatible (x, err) ->
      msg "predicate `%s' body %a"
        (string_of_qsymbol x) (pp_incompatible env) err

  | CE_InvalidRE x ->
      msg "invalid regexp: `%s'" x

let () =
  let pp fmt exn =
    match exn with
    | CloneError (env, e) -> pp_clone_error fmt env e
    | _ -> raise exn
  in
    EcPException.register pp

(* ------------------------------------------------------------------ *)
type evclone = {
  evc_types  : (ty_override located) Msym.t;
  evc_ops    : (op_override located) Msym.t;
  evc_preds  : (pr_override located) Msym.t;
  evc_lemmas : evlemma;
  evc_ths    : evclone Msym.t;
}

and evlemma = {
  ev_global  : (ptactic_core option * Ssym.t option) list;
  ev_bynames : (ptactic_core option) Msym.t;
}

(*-------------------------------------------------------------------- *)
let evc_empty =
  let evl = { ev_global = []; ev_bynames = Msym.empty; } in
    { evc_types  = Msym.empty;
      evc_ops    = Msym.empty;
      evc_preds  = Msym.empty;
      evc_lemmas = evl;
      evc_ths    = Msym.empty; }

let rec evc_update (upt : evclone -> evclone) (nm : symbol list) (evc : evclone) =
  match nm with
  | []      -> upt evc
  | x :: nm ->
      let ths =
        Msym.change
          (fun sub -> Some (evc_update upt nm (odfl evc_empty sub)))
          x evc.evc_ths
      in
        { evc with evc_ths = ths }

let rec evc_get (nm : symbol list) (evc : evclone) =
  match nm with
  | []      -> Some evc
  | x :: nm ->
      match Msym.find_opt x evc.evc_ths with
      | None     -> None
      | Some evc -> evc_get nm evc

(* -------------------------------------------------------------------- *)
let find_mc =
  let for1 cth nm =
    let test = function
      | CTh_theory (x, (sub, _)) when x = nm -> Some sub.cth_struct
      | _ -> None
    in List.opick test cth
  in

  let rec doit nm cth =
    match nm with
    | []      -> Some cth
    | x :: nm -> for1 cth x |> obind (doit nm)

  in fun cth nm -> doit nm cth

(* -------------------------------------------------------------------- *)
let find_type cth (nm, x) =
  let test = function
    | CTh_type (xty, ty) when xty = x -> Some ty
    | _ -> None
  in find_mc cth.cth_struct nm |> obind (List.opick test)

(* -------------------------------------------------------------------- *)
let find_theory cth (nm, x) =
  let test = function
    | CTh_theory (xth, th) when xth = x -> Some th
    | _ -> None
  in find_mc cth.cth_struct nm |> obind (List.opick test)

(* -------------------------------------------------------------------- *)
let find_op cth (nm, x) =
  let test = function
    | CTh_operator (xop, op) when xop = x && EcDecl.is_oper op -> Some op
    | _ -> None
  in find_mc cth.cth_struct nm |> obind (List.opick test)

(* -------------------------------------------------------------------- *)
let find_pr cth (nm, x) =
  let test = function
    | CTh_operator (xpr, pr) when xpr = x && EcDecl.is_pred pr -> Some pr
    | _ -> None
  in find_mc cth.cth_struct nm |> obind (List.opick test)

(* -------------------------------------------------------------------- *)
let find_ax cth (nm, x) =
  let test = function
    | CTh_axiom (xax, ax) when xax = x -> Some ax
    | _ -> None
  in find_mc cth.cth_struct nm |> obind (List.opick test)

(* -------------------------------------------------------------------- *)
type clone = {
  cl_name   : symbol;
  cl_theory : EcPath.path * (EcEnv.Theory.t * EcTheory.thmode);
  cl_clone  : evclone;
  cl_rename : renaming list;
}

and renaming_kind = [
  | `All
  | `Selected of rk_categories
]

and renaming =
  renaming_kind * (Pcre.regexp * Pcre.substitution)

and rk_categories = {
  rkc_lemmas  : bool;
  rkc_ops     : bool;
  rkc_preds   : bool;
  rkc_types   : bool;
  rkc_module  : bool;
  rkc_modtype : bool;
}

(* -------------------------------------------------------------------- *)
let rename ((rk, (rex, itempl)) : renaming) (k, x) =
  let selected =
    match rk, k with
    | `All, _ -> true
    | `Selected { rkc_lemmas  = true }, `Lemma   -> true
    | `Selected { rkc_ops     = true }, `Op      -> true
    | `Selected { rkc_preds   = true }, `Pred    -> true
    | `Selected { rkc_types   = true }, `Type    -> true
    | `Selected { rkc_module  = true }, `Module  -> true
    | `Selected { rkc_modtype = true }, `ModType -> true
    | _, _ -> false in

  let newx =
    try  if selected then Pcre.replace ~rex ~itempl x else x
    with Failure _ -> x in

  if x = newx then None else Some newx

(* -------------------------------------------------------------------- *)
let clone (scenv : EcEnv.env) (thcl : theory_cloning) =
  let opath, (oth, othmode) =
    match EcEnv.Theory.lookup_opt ~mode:`All (unloc thcl.pthc_base) scenv with
    | None   -> clone_error scenv (CE_UnkTheory (unloc thcl.pthc_base))
    | Some x -> x
  in

  let name = odfl (EcPath.basename opath) (thcl.pthc_name |> omap unloc) in

  let (genproofs, ovrds) =
    let rec do1 ?(cancrt = false) (proofs, evc) ({ pl_loc = l; pl_desc = ((nm, x) as name) }, ovrd) =
       match ovrd with
       | PTHO_Type ((tyargs, _, _) as tyd) -> begin
           match find_type oth name with
           | None ->
               clone_error scenv (CE_UnkOverride (OVK_Type, name));
           | Some { EcDecl.tyd_type = `Concrete _ } when not cancrt ->
               clone_error scenv (CE_CrtOverride (OVK_Type, name));
           | Some refty ->
               if List.length refty.tyd_params <> List.length tyargs then
                 clone_error scenv (CE_TypeArgMism (OVK_Type, name))
         end;
         let evc =
           evc_update
             (fun evc ->
               if Msym.mem x evc.evc_types then
                 clone_error scenv (CE_DupOverride (OVK_Type, name));
               { evc with evc_types = Msym.add x (mk_loc l tyd) evc.evc_types })
             nm evc
         in
           (proofs, evc)

       | PTHO_Op opd -> begin
           match find_op oth name with
           | None
           | Some { op_kind = OB_pred _ } ->
               clone_error scenv (CE_UnkOverride (OVK_Operator, name));
           | Some { op_kind = OB_oper (Some _) } when not cancrt ->
               clone_error scenv (CE_CrtOverride (OVK_Operator, name));
           | _ -> ()
         end;
         let evc =
           evc_update
             (fun evc ->
               if Msym.mem x evc.evc_ops then
                 clone_error scenv (CE_DupOverride (OVK_Operator, name));
               { evc with evc_ops = Msym.add x (mk_loc l opd) evc.evc_ops })
             nm evc
         in
           (proofs, evc)

       | PTHO_Pred pr -> begin
           match find_pr oth name with
           | None
           | Some { op_kind = OB_oper _ } ->
               clone_error scenv (CE_UnkOverride (OVK_Predicate, name));
           | Some { op_kind = OB_pred (Some _) } when not cancrt ->
               clone_error scenv (CE_CrtOverride (OVK_Predicate, name));
           | _ -> ()
         end;
         let evc =
           evc_update
             (fun evc ->
               if Msym.mem x evc.evc_preds then
                 clone_error scenv (CE_DupOverride (OVK_Predicate, name));
               { evc with evc_preds = Msym.add x (mk_loc l pr) evc.evc_preds })
             nm evc
         in
           (proofs, evc)

       | PTHO_Theory xsth ->
           let dth =
             match find_theory oth name with
             | None | Some (_, `Abstract) ->
                 clone_error scenv (CE_UnkOverride (OVK_Theory, name))
             | Some (th, `Concrete) -> th
           in

           let sp =
             match EcEnv.Theory.lookup_opt (unloc xsth) scenv with
             | None -> clone_error scenv (CE_UnkOverride (OVK_Theory, unloc xsth))
             | Some (sp, _) -> sp
           in

           let xsth = let xsth = EcPath.toqsymbol sp in (fst xsth @ [snd xsth]) in
           let xdth = nm @ [x] in

           let rec doit prefix (proofs, evc) dth =
             match dth with
             | CTh_type (x, otyd) ->
                 (* FIXME: TC HOOK *)
                 let params = List.map (EcIdent.name |- fst) otyd.tyd_params in
                 let params = List.map (mk_loc l) params in
                 let tyd    =
                   match List.map (fun a -> mk_loc l (PTvar a)) params with
                   | [] -> PTnamed (mk_loc l (xsth @ prefix, x))
                   | pt -> PTapp   (mk_loc l (xsth @ prefix, x), pt)
                 in
                 let tyd  = mk_loc l tyd in
                 let ovrd = PTHO_Type (params, tyd, `Inline) in
                   do1 ~cancrt:true (proofs, evc) (mk_loc l (xdth @ prefix, x), ovrd)

             | CTh_operator (x, ({ op_kind = OB_oper _ } as oopd)) ->
                 (* FIXME: TC HOOK *)
                 let params = List.map (EcIdent.name |- fst) oopd.op_tparams in
                 let params = List.map (mk_loc l) params in
                 let ovrd   = {
                   opov_tyvars = Some params;
                   opov_args   = [];
                   opov_retty  = mk_loc l PTunivar;
                   opov_body   =
                     let sym = mk_loc l (xsth @ prefix, x) in
                     let tya = List.map (fun a -> mk_loc l (PTvar a)) params in
                       mk_loc l (PEident (sym, Some (mk_loc l (TVIunamed tya))));
                 } in
                   do1 ~cancrt:true (proofs, evc) (mk_loc l (xdth @ prefix, x), PTHO_Op (ovrd, `Inline))

             | CTh_operator (x, ({ op_kind = OB_pred _ } as oprd)) ->
                 (* FIXME: TC HOOK *)
                 let params = List.map (EcIdent.name |- fst) oprd.op_tparams in
                 let params = List.map (mk_loc l) params in
                 let ovrd   = {
                   prov_tyvars = Some params;
                   prov_args   = [];
                   prov_body   =
                     let sym = mk_loc l (xsth @ prefix, x) in
                     let tya = List.map (fun a -> mk_loc l (PTvar a)) params in
                       mk_loc l (PFident (sym, Some (mk_loc l (TVIunamed tya))));
                 } in
                   do1 ~cancrt:true (proofs, evc) (mk_loc l (xdth @ prefix, x), PTHO_Pred (ovrd, `Inline))

             | CTh_axiom (x, ({ ax_spec = Some _ } as ax)) ->
                 (* FIXME: TC HOOK *)
               if is_axiom ax.ax_kind then
                 let params = List.map (EcIdent.name |- fst) ax.ax_tparams in
                 let params = List.map (mk_loc l) params in
                 let params = List.map (fun a -> mk_loc l (PTvar a)) params in

                 let tc = FPNamed (mk_loc l (xsth @ prefix, x),
                                   Some (mk_loc l (TVIunamed params))) in
                 let tc = Papply (`Apply ([`Explicit, { fp_head = tc; fp_args = []}], `Exact)) in
                 let tc = mk_loc l (Plogic tc) in
                 let pr = { pthp_mode   = `Named (mk_loc l (xdth @ prefix, x));
                            pthp_tactic = Some tc }
                 in
                   (pr :: proofs, evc)
               else (proofs,evc)

             | CTh_theory (x, (dth, `Concrete)) ->
                 List.fold_left (doit (prefix @ [x])) (proofs, evc) dth.cth_struct

             | CTh_export _ ->
                 (proofs, evc)

             | _ -> clone_error scenv (CE_CrtOverride (OVK_Theory, name))
           in
             List.fold_left (doit []) (proofs, evc) dth.cth_struct
    in
      List.fold_left do1 ([], evc_empty) thcl.pthc_ext
  in

  let ovrds =
    let do1 evc prf =
      match prf.pthp_mode with
      | `All (name, tags) -> begin
          let tags =
            if   List.is_empty tags then None
            else Some (Ssym.of_list (List.map unloc tags)) in
          let name =
            match name with
            | None -> []
            | Some name ->
                match find_theory oth (unloc name) with
                | None   -> clone_error scenv (CE_UnkOverride (OVK_Lemma, unloc name))
                | Some _ -> let (nm, name) = unloc name in nm @ [name]
          in

          let update1 evc =
            let evl = evc.evc_lemmas in
            let evl = {
              evl with ev_global = evl.ev_global @ [(prf.pthp_tactic, tags)]
            } in { evc with evc_lemmas = evl }
          in
            evc_update update1 name evc
      end

      | `Named name -> begin
          let name = unloc name in

          match find_ax oth name with
          | None ->
              clone_error scenv (CE_UnkOverride (OVK_Lemma, name))

          | Some ax ->
              if not (is_axiom ax.ax_kind) || ax.ax_spec = None then
                clone_error scenv (CE_CrtOverride (OVK_Lemma, name));

              let update1 evc =
                match Msym.find_opt (snd name) evc.evc_lemmas.ev_bynames with
                | Some (Some _) ->
                    clone_error scenv (CE_DupOverride (OVK_Lemma, name))
                | _ ->
                    let map = evc.evc_lemmas.ev_bynames in
                    let map = Msym.add (snd name) prf.pthp_tactic map in
                    let evl = { evc.evc_lemmas with ev_bynames = map } in
                      { evc with evc_lemmas = evl }
              in
                evc_update update1 (fst name) evc
      end

    in List.fold_left do1 ovrds (genproofs @ thcl.pthc_prf)
  in

  let rename =
    let rename1 (k, (r1, r2)) : renaming =
      let e1 =
        try  Pcre.regexp (unloc r1)
        with Pcre.Error _ -> clone_error scenv (CE_InvalidRE (unloc r1)) in
      let e2 =
        try  Pcre.subst (unloc r2)
        with Pcre.Error _ -> clone_error scenv (CE_InvalidRE (unloc r2)) in

      Array.iter
        (fun m ->
          if Pcre.pmatch ~pat:"^0+$" m.(1) then
            clone_error scenv (CE_InvalidRE (unloc r2)))
        (try  Pcre.extract_all ~pat:"\\$([0-9]+)" (unloc r2)
         with Not_found -> [||]);

      let k =
        if List.is_empty k then `All else

          let update rk = function
            | `Lemma   -> { rk with rkc_lemmas  = true; }
            | `Type    -> { rk with rkc_types   = true; }
            | `Op      -> { rk with rkc_ops     = true; }
            | `Pred    -> { rk with rkc_preds   = true; }
            | `Module  -> { rk with rkc_module  = true; }
            | `ModType -> { rk with rkc_modtype = true; } in

          let init = {
            rkc_lemmas  = false; rkc_types   = false; rkc_ops     = false;
            rkc_preds   = false; rkc_module  = false; rkc_modtype = false; } in

          `Selected (List.fold_left update init k)

      in (k, (e1, e2))

    in List.map rename1 thcl.pthc_rnm
  in

  { cl_name   = name;
    cl_theory = (opath, (oth, othmode));
    cl_clone  = ovrds;
    cl_rename = rename; }
