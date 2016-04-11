(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
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

module Sp = EcPath.Sp
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
| CE_UnkAbbrev      of qsymbol
| CE_TypeArgMism    of ovkind * qsymbol
| CE_OpIncompatible of qsymbol * incompatible
| CE_PrIncompatible of qsymbol * incompatible
| CE_InvalidRE      of string

exception CloneError of EcEnv.env * clone_error

let clone_error env error =
  raise (CloneError (env, error))

(* -------------------------------------------------------------------- *)
type axclone = {
  axc_axiom : symbol * EcDecl.axiom;
  axc_path  : EcPath.path;
  axc_env   : EcEnv.env;
  axc_tac   : EcParsetree.ptactic_core option;
}

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
let find_nt cth (nm, x) =
  let test = function
    | CTh_operator (xop, op) when xop = x && EcDecl.is_abbrev op ->
       Some op
    | _ -> None
  in find_mc cth.cth_struct nm |> obind (List.opick test)

(* -------------------------------------------------------------------- *)
type clone = {
  cl_name   : symbol;
  cl_theory : EcPath.path * (EcEnv.Theory.t * EcTheory.thmode);
  cl_clone  : evclone;
  cl_rename : renaming list;
  cl_ntclr  : Sp.t;
}

and renaming_kind = [
  | `All
  | `Selected of rk_categories
]

and renaming =
  renaming_kind * (EcRegexp.regexp * EcRegexp.subst)

and rk_categories = {
  rkc_lemmas  : bool;
  rkc_ops     : bool;
  rkc_preds   : bool;
  rkc_types   : bool;
  rkc_module  : bool;
  rkc_modtype : bool;
  rkc_theory  : bool;
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
    | `Selected { rkc_theory  = true }, `Theory  -> true
    | _, _ -> false in

  let newx =
    try  if selected then EcRegexp.sub (`C rex) (`C itempl) x else x
    with Failure _ -> x in

  if x = newx then None else Some newx

(* -------------------------------------------------------------------- *)
type octxt = {
  oc_env : EcEnv.env;
  oc_oth : ctheory;
}

(* -------------------------------------------------------------------- *)
module OVRD : sig
  type state = theory_cloning_proof list * evclone

  type 'a ovrd =
    cancrt:bool -> octxt -> state -> pqsymbol -> 'a -> state

  val ty_ovrd : ty_override ovrd
  val op_ovrd : op_override ovrd
  val pr_ovrd : pr_override ovrd
  val th_ovrd : th_override ovrd

  val ovrd :
       ?cancrt:bool -> octxt -> state -> pqsymbol
    -> theory_override -> state
end = struct
  type state = theory_cloning_proof list * evclone

  type 'a ovrd =
    cancrt:bool -> octxt -> state -> pqsymbol -> 'a -> state

  (* ------------------------------------------------------------------ *)
  let ty_ovrd ~cancrt oc ((proofs, evc) : state) name (tyd : ty_override) =
    let (tyargs, _, _) = tyd in
    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in

    let () =
      match find_type oc.oc_oth name with
      | None ->
         clone_error oc.oc_env (CE_UnkOverride (OVK_Type, name));
      | Some { EcDecl.tyd_type = `Concrete _ } when not cancrt ->
         clone_error oc.oc_env (CE_CrtOverride (OVK_Type, name))
      | Some refty ->
         if List.length refty.tyd_params <> List.length tyargs then
           clone_error oc.oc_env (CE_TypeArgMism (OVK_Type, name)) in

    let evc =
      evc_update
        (fun evc ->
          if Msym.mem x evc.evc_types then
            clone_error oc.oc_env (CE_DupOverride (OVK_Type, name));
          { evc with evc_types = Msym.add x (mk_loc lc tyd) evc.evc_types })
        nm evc

    in (proofs, evc)

  (* ------------------------------------------------------------------ *)
  let op_ovrd ~cancrt oc ((proofs, evc) : state) name (opd : op_override) =
    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in
    let (_ : bool) = cancrt in

    let () =
      match find_op oc.oc_oth name with
      | None
      | Some { op_kind = OB_pred _ } ->
         clone_error oc.oc_env (CE_UnkOverride (OVK_Operator, name));
      | Some { op_kind = OB_oper (Some _) } ->
         (* FIXME: check convertibility *) ()
      | _ -> () in

    let evc =
      evc_update
        (fun evc ->
         if Msym.mem x evc.evc_ops then
           clone_error oc.oc_env (CE_DupOverride (OVK_Operator, name));
         { evc with evc_ops = Msym.add x (mk_loc lc opd) evc.evc_ops })
        nm evc

    in (proofs, evc)

  (* ------------------------------------------------------------------ *)
  let pr_ovrd ~cancrt oc ((proofs, evc) : state) name (prd : pr_override) =
    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in

    let () =
      match find_pr oc.oc_oth name with
      | None
      | Some { op_kind = OB_oper _ } ->
         clone_error oc.oc_env (CE_UnkOverride (OVK_Predicate, name));
      | Some { op_kind = OB_pred (Some _) } when not cancrt ->
         clone_error oc.oc_env (CE_CrtOverride (OVK_Predicate, name));
      | _ -> () in

    let evc =
      evc_update
        (fun evc ->
         if Msym.mem x evc.evc_preds then
           clone_error oc.oc_env (CE_DupOverride (OVK_Predicate, name));
         { evc with evc_preds = Msym.add x (mk_loc lc prd) evc.evc_preds })
        nm evc

    in (proofs, evc)

  (* ------------------------------------------------------------------ *)
  let th_ovrd ~cancrt oc ((proofs, evc) : state) name (thd : th_override) =
    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in
    let (_ : bool) = cancrt in

    let loced x = mk_loc lc x in

    let dth =
      match find_theory oc.oc_oth name with
      | None | Some (_, `Abstract) ->
         clone_error oc.oc_env (CE_UnkOverride (OVK_Theory, name))
      | Some (th, `Concrete) -> th
    in

    let sp =
      match EcEnv.Theory.lookup_opt (unloc thd) oc.oc_env with
      | None -> clone_error oc.oc_env (CE_UnkOverride (OVK_Theory, unloc thd))
      | Some (sp, _) -> sp
    in

    let thd = let thd = EcPath.toqsymbol sp in (fst thd @ [snd thd]) in
    let xdth = nm @ [x] in

    let rec doit prefix (proofs, evc) dth =
      match dth with
      | CTh_type (x, otyd) ->
         let params = List.map (EcIdent.name |- fst) otyd.tyd_params in
         let params = List.map (mk_loc lc) params in
         let tyd    =
           match List.map (fun a -> loced (PTvar a)) params with
           | [] -> PTnamed (loced (thd @ prefix, x))
           | pt -> PTapp   (loced (thd @ prefix, x), pt)
         in
         let ovrd = (params, loced tyd, `Inline) in
         ty_ovrd ~cancrt:true oc (proofs, evc) (loced (xdth @ prefix, x)) ovrd

      | CTh_operator (x, ({ op_kind = OB_oper _ } as oopd)) ->
         let params = List.map (EcIdent.name |- fst) oopd.op_tparams in
         let params = List.map (mk_loc lc) params in
         let ovrd   = {
             opov_tyvars = Some params;
             opov_args   = [];
             opov_retty  = loced PTunivar;
             opov_body   =
               let sym = loced (thd @ prefix, x) in
               let tya = List.map (fun a -> loced (PTvar a)) params in
               loced (PEident (sym, Some (loced (TVIunamed tya))));
           } in
         let ovrd = (ovrd, `Inline) in
         op_ovrd ~cancrt:true oc (proofs, evc) (loced (xdth @ prefix, x)) ovrd

      | CTh_operator (x, ({ op_kind = OB_pred _ } as oprd)) ->
         let params = List.map (EcIdent.name |- fst) oprd.op_tparams in
         let params = List.map (mk_loc lc) params in
         let ovrd   = {
             prov_tyvars = Some params;
             prov_args   = [];
             prov_body   =
               let sym = loced (thd @ prefix, x) in
               let tya = List.map (fun a -> loced (PTvar a)) params in
               loced (PFident (sym, Some (loced (TVIunamed tya))));
           } in
         let ovrd = (ovrd, `Inline) in
         pr_ovrd ~cancrt:true oc (proofs, evc) (loced (xdth @ prefix, x)) ovrd

      | CTh_axiom (x, ax) ->
         if is_axiom ax.ax_kind then
           let params = List.map (EcIdent.name |- fst) ax.ax_tparams in
           let params = List.map (mk_loc lc) params in
           let params = List.map (fun a -> loced (PTvar a)) params in

           let tc = FPNamed (loced (thd @ prefix, x),
                             Some (loced (TVIunamed params))) in
           let tc = { fp_mode = `Explicit; fp_head = tc; fp_args = []; } in
           let tc = Papply (`Apply ([tc], `Exact)) in
           let tc = loced (Plogic tc) in
           let pr = { pthp_mode   = `Named (loced (xdth @ prefix, x));
                      pthp_tactic = Some tc }
           in (pr :: proofs, evc)
         else (proofs, evc)

      | CTh_theory (x, (dth, `Concrete)) ->
         List.fold_left (doit (prefix @ [x])) (proofs, evc) dth.cth_struct

      | CTh_export _ ->
         (proofs, evc)

      | _ -> clone_error oc.oc_env (CE_CrtOverride (OVK_Theory, name))

    in List.fold_left (doit []) (proofs, evc) dth.cth_struct

  (* ------------------------------------------------------------------ *)
  let ovrd ?(cancrt = false) oc state name (ovrd : theory_override) =
     match ovrd with
     | PTHO_Type tyd ->
        ty_ovrd ~cancrt oc state name tyd

     | PTHO_Op opd ->
        op_ovrd ~cancrt oc state name opd

     | PTHO_Pred prd ->
        pr_ovrd ~cancrt oc state name prd

     | PTHO_Theory thd ->
        th_ovrd ~cancrt oc state name thd
end

(* -------------------------------------------------------------------- *)
module Renaming : sig
  val rename1 : octxt -> theory_renaming -> renaming
end = struct
  let rename1 oc (k, (r1, r2)) : renaming =
    let e1 =
      try  EcRegexp.regexp (unloc r1)
      with EcRegexp.Error _ -> clone_error oc.oc_env (CE_InvalidRE (unloc r1)) in
    let e2 =
      try  EcRegexp.subst (unloc r2)
      with EcRegexp.Error _ -> clone_error oc.oc_env (CE_InvalidRE (unloc r2)) in

    Array.iter
      (fun m ->
        if EcRegexp.match_ (`S "^0+$") (oget m.(1)) then
          clone_error oc.oc_env (CE_InvalidRE (unloc r2)))
      (try  EcRegexp.extract (`S "\\$([0-9]+)") (unloc r2)
       with Not_found -> [||]);

    let k =
      if List.is_empty k then `All else

        let update rk = function
          | `Lemma   -> { rk with rkc_lemmas  = true; }
          | `Type    -> { rk with rkc_types   = true; }
          | `Op      -> { rk with rkc_ops     = true; }
          | `Pred    -> { rk with rkc_preds   = true; }
          | `Module  -> { rk with rkc_module  = true; }
          | `ModType -> { rk with rkc_modtype = true; }
          | `Theory  -> { rk with rkc_theory  = true; } in

        let init = {
          rkc_lemmas  = false; rkc_types   = false; rkc_ops     = false;
          rkc_preds   = false; rkc_module  = false; rkc_modtype = false;
          rkc_theory  = false; } in

        `Selected (List.fold_left update init k)

    in (k, (e1, e2))
end

(* -------------------------------------------------------------------- *)
module Proofs : sig
  val proof : octxt -> evclone -> theory_cloning_proof -> evclone
end = struct
  let all_proof oc evc (name, tags, tactics) =
    let tags =
      if   List.is_empty tags then None
      else Some (Ssym.of_list (List.map unloc tags)) in
    let name =
      match name with
      | None -> []
      | Some name ->
         match find_theory oc.oc_oth (unloc name) with
         | None ->
            clone_error oc.oc_env (CE_UnkOverride (OVK_Lemma, unloc name))
         | Some _ -> let (nm, name) = unloc name in nm @ [name]
    in

    let update1 evc =
      let evl = evc.evc_lemmas in
      let evl = {
          evl with ev_global = evl.ev_global @ [(tactics, tags)]
        } in { evc with evc_lemmas = evl }
    in evc_update update1 name evc

  let name_proof oc evc ({ pl_desc = name }, tactics) =
    match find_ax oc.oc_oth name with
    | None ->
        clone_error oc.oc_env (CE_UnkOverride (OVK_Lemma, name))

    | Some ax ->
        if not (is_axiom ax.ax_kind) then
          clone_error oc.oc_env (CE_CrtOverride (OVK_Lemma, name));

        let update1 evc =
          match Msym.find_opt (snd name) evc.evc_lemmas.ev_bynames with
          | Some (Some _) ->
              clone_error oc.oc_env (CE_DupOverride (OVK_Lemma, name))
          | _ ->
              let map = evc.evc_lemmas.ev_bynames in
              let map = Msym.add (snd name) tactics map in
              let evl = { evc.evc_lemmas with ev_bynames = map } in
                { evc with evc_lemmas = evl }
        in
          evc_update update1 (fst name) evc

  let proof oc evc prf =
    match prf.pthp_mode with
    | `All (name, tags) ->
         all_proof oc evc (name, tags, prf.pthp_tactic)
    | `Named name ->
         name_proof oc evc (name, prf.pthp_tactic)
end

(* -------------------------------------------------------------------- *)
let clone (scenv : EcEnv.env) (thcl : theory_cloning) =
  let opath, (oth, othmode) =
    match EcEnv.Theory.lookup_opt ~mode:`All (unloc thcl.pthc_base) scenv with
    | None -> clone_error scenv (CE_UnkTheory (unloc thcl.pthc_base))
    | Some x -> x
  in

  let name = odfl (EcPath.basename opath) (thcl.pthc_name |> omap unloc) in
  let oc   = { oc_env = scenv; oc_oth = oth; } in

  let (genproofs, ovrds) =
    List.fold_left
      (fun st -> curry (OVRD.ovrd ~cancrt:false oc st))
      ([], evc_empty) thcl.pthc_ext
  in

  let ovrds =
    List.fold_left (Proofs.proof oc) ovrds (genproofs @ thcl.pthc_prf) in
  let rename = List.map (Renaming.rename1 oc) thcl.pthc_rnm in

  let ntclr =
    let ntclr1 (`Abbrev, { pl_desc = (nm, x) as q }) =
      if is_none (find_nt oth q) then
        clone_error scenv (CE_UnkAbbrev q);
      EcPath.pqname (EcPath.extend opath nm) x

    in List.map ntclr1 thcl.pthc_clears
  in

  { cl_name   = name;
    cl_theory = (opath, (oth, othmode));
    cl_clone  = ovrds;
    cl_rename = rename;
    cl_ntclr  = Sp.of_list ntclr; }
