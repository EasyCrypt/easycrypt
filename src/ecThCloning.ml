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
| OpBody (* of (EcPath.path * EcDecl.operator) * (EcPath.path * EcDecl.operator) *)
| TyBody (* of (EcPath.path * EcDecl.tydecl) * (EcPath.path * EcDecl.tydecl) *)

type ovkind =
| OVK_Type
| OVK_Operator
| OVK_Predicate
| OVK_Abbrev
| OVK_Theory
| OVK_Lemma
| OVK_ModType

type clone_error =
| CE_UnkTheory         of qsymbol
| CE_DupOverride       of ovkind * qsymbol
| CE_UnkOverride       of ovkind * qsymbol
| CE_ThyOverride       of qsymbol
| CE_UnkAbbrev         of qsymbol
| CE_TypeArgMism       of ovkind * qsymbol
| CE_OpIncompatible    of qsymbol * incompatible
| CE_PrIncompatible    of qsymbol * incompatible
| CE_TyIncompatible    of qsymbol * incompatible
| CE_ModTyIncompatible of qsymbol
| CE_ModIncompatible   of qsymbol
| CE_InvalidRE         of string
| CE_InlinedOpIsForm   of qsymbol
| CE_ProofForLemma     of qsymbol

exception CloneError of EcEnv.env * clone_error

let clone_error env ce = raise (CloneError(env,ce))

(* -------------------------------------------------------------------- *)
type axclone = {
  axc_axiom : symbol * EcDecl.axiom;
  axc_path  : EcPath.path;
  axc_env   : EcSection.scenv;
  axc_tac   : EcParsetree.ptactic_core option;
}

(* ------------------------------------------------------------------ *)
type evclone = {
  evc_types    : (ty_override located) Msym.t;
  evc_ops      : (op_override located) Msym.t;
  evc_preds    : (pr_override located) Msym.t;
  evc_abbrevs  : (nt_override located) Msym.t;
  evc_modexprs : (me_override located) Msym.t;
  evc_modtypes : (mt_override located) Msym.t;
  evc_lemmas   : evlemma;
  evc_ths      : evclone Msym.t;
}

and evlemma = {
  ev_global  : (ptactic_core option * evtags option) list;
  ev_bynames : evinfo Msym.t;
}

and evtags = ([`Include | `Exclude] * symbol) list
and evinfo = ptactic_core option * clmode * bool

(*-------------------------------------------------------------------- *)
let evc_empty =
  let evl = { ev_global = []; ev_bynames = Msym.empty; } in
    { evc_types    = Msym.empty;
      evc_ops      = Msym.empty;
      evc_preds    = Msym.empty;
      evc_abbrevs  = Msym.empty;
      evc_modexprs = Msym.empty;
      evc_modtypes = Msym.empty;
      evc_lemmas   = evl;
      evc_ths      = Msym.empty; }

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
      | Th_theory (x, sub) when x = nm -> Some sub.cth_items
      | _ -> None
    in List.opick (fun item -> test item.ti_item) cth
  in

  let rec doit nm cth =
    match nm with
    | []      -> Some cth
    | x :: nm -> for1 cth x |> obind (doit nm)

  in fun cth nm -> doit nm cth

(* -------------------------------------------------------------------- *)
let find_type cth (nm, x) =
  let test = function
    | Th_type (xty, ty) when xty = x -> Some ty
    | _ -> None
  in find_mc cth.cth_items nm |> obind (List.opick (fun item -> test item.ti_item))

(* -------------------------------------------------------------------- *)
let find_theory cth (nm, x) =
  let test = function
    | Th_theory (xth, th) when xth = x -> Some th
    | _ -> None
  in find_mc cth.cth_items nm |> obind (List.opick (fun item -> test item.ti_item))

(* -------------------------------------------------------------------- *)
let find_op cth (nm, x) =
  let test = function
    | Th_operator (xop, op) when xop = x && EcDecl.is_oper op -> Some op
    | _ -> None
  in find_mc cth.cth_items nm |> obind (List.opick (fun item -> test item.ti_item))

(* -------------------------------------------------------------------- *)
let find_pr cth (nm, x) =
  let test = function
    | Th_operator (xpr, pr) when xpr = x && EcDecl.is_pred pr -> Some pr
    | _ -> None
  in find_mc cth.cth_items nm |> obind (List.opick (fun item -> test item.ti_item))

(* -------------------------------------------------------------------- *)
let find_ax cth (nm, x) =
  let test = function
    | Th_axiom (xax, ax) when xax = x -> Some ax
    | _ -> None
  in find_mc cth.cth_items nm |> obind (List.opick (fun item -> test item.ti_item))

(* -------------------------------------------------------------------- *)
let find_nt cth (nm, x) =
  let test = function
    | Th_operator (xop, op) when xop = x && EcDecl.is_abbrev op ->
       Some op
    | _ -> None
  in find_mc cth.cth_items nm |> obind (List.opick (fun item -> test item.ti_item))

(* -------------------------------------------------------------------- *)
let find_modexpr cth (nm, x) =
  let test = function
    | Th_module me when me.tme_expr.me_name = x ->
       Some me
    | _ -> None
  in find_mc cth.cth_items nm |> obind (List.opick (fun item -> test item.ti_item))

(* -------------------------------------------------------------------- *)
let find_modtype cth (nm, x) =
  let test = function
    | Th_modtype (mtx, mt) when mtx = x ->
       Some mt
    | _ -> None
  in find_mc cth.cth_items nm |> obind (List.opick (fun item -> test item.ti_item))

(* -------------------------------------------------------------------- *)
type clone = {
  cl_name   : symbol;
  cl_theory : EcPath.path * EcEnv.Theory.t;
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

  type 'a ovrd = octxt -> state -> pqsymbol -> 'a -> state

  val ty_ovrd : ty_override ovrd
  val op_ovrd : op_override ovrd
  val pr_ovrd : pr_override ovrd
  val th_ovrd : th_override ovrd

  val ovrd : octxt -> state -> pqsymbol -> theory_override -> state
end = struct
  type state = theory_cloning_proof list * evclone

  type 'a ovrd = octxt -> state -> pqsymbol -> 'a -> state

  (* ------------------------------------------------------------------ *)
  let ty_ovrd oc ((proofs, evc) : state) name (tyd : ty_override) =
    let ntyargs =
      match fst tyd with
      | `BySyntax (tyargs, _) -> List.length tyargs
      | `ByPath p -> List.length (EcEnv.Ty.by_path p oc.oc_env).tyd_params in

    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in

    let () =
      match find_type oc.oc_oth name with
      | None ->
         clone_error oc.oc_env (CE_UnkOverride (OVK_Type, name));
      | Some refty ->
         if List.length refty.tyd_params <> ntyargs then
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
  let op_ovrd oc ((proofs, evc) : state) name (opd : op_override) =
    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in

    if find_op oc.oc_oth name = None then
      clone_error oc.oc_env (CE_UnkOverride (OVK_Operator, name));

    let evc =
      evc_update
        (fun evc ->
         if Msym.mem x evc.evc_ops then
           clone_error oc.oc_env (CE_DupOverride (OVK_Operator, name));
         { evc with evc_ops = Msym.add x (mk_loc lc opd) evc.evc_ops })
        nm evc

    in (proofs, evc)

  (* ------------------------------------------------------------------ *)
  let pr_ovrd oc ((proofs, evc) : state) name (prd : pr_override) =
    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in

    if find_pr oc.oc_oth name = None then
      clone_error oc.oc_env (CE_UnkOverride (OVK_Predicate, name));

    let evc =
      evc_update
        (fun evc ->
         if Msym.mem x evc.evc_preds then
           clone_error oc.oc_env (CE_DupOverride (OVK_Predicate, name));
         { evc with evc_preds = Msym.add x (mk_loc lc prd) evc.evc_preds })
        nm evc

    in (proofs, evc)

  (* ------------------------------------------------------------------ *)
  let nt_ovrd oc ((proofs, evc) : state) name (ntd : nt_override) =
    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in

    if find_nt oc.oc_oth name = None then
      clone_error oc.oc_env (CE_UnkOverride (OVK_Abbrev, name));

    let evc =
      evc_update
        (fun evc ->
         if Msym.mem x evc.evc_abbrevs then
           clone_error oc.oc_env (CE_DupOverride (OVK_Abbrev, name));
         { evc with evc_abbrevs = Msym.add x (mk_loc lc ntd) evc.evc_abbrevs })
        nm evc

    in (proofs, evc)

  (* ------------------------------------------------------------------ *)
  let ax_ovrd _oc ((proofs, evc) : state) name ((axd, mode) : ax_override) =
    let loc = axd.pl_loc in
    let tc = Papply (`ExactType axd, None) in
    let tc = mk_loc loc (Plogic tc) in
    let pr = { pthp_mode   = `Named (name, mode);
               pthp_tactic = Some tc; } in
    (pr :: proofs, evc)

  (* ------------------------------------------------------------------ *)
  let modtype_ovrd oc ((proofs, evc) : state) name (mtd : mt_override) =
    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in

    let () =
      match find_modtype oc.oc_oth name with
      | None ->
         clone_error oc.oc_env (CE_UnkOverride (OVK_ModType, name));
      | _ -> () in

    let evc =
      evc_update
        (fun evc ->
         if Msym.mem x evc.evc_modtypes then
           clone_error oc.oc_env (CE_DupOverride (OVK_ModType, name));
         { evc with evc_modtypes = Msym.add x (mk_loc lc mtd) evc.evc_modtypes })
        nm evc

    in (proofs, evc)

  (* ------------------------------------------------------------------ *)
  let th_ovrd oc ((proofs, evc) : state) name ((thd, mode) : th_override) =
    let { pl_loc = lc; pl_desc = ((nm, x) as name) } = name in

    let loced x = mk_loc lc x in

    let dth =
      match find_theory oc.oc_oth name with
      | None | Some { cth_mode = `Abstract } ->
         clone_error oc.oc_env (CE_UnkOverride (OVK_Theory, name))
      | Some ({cth_mode = `Concrete} as th) -> th
    in

    let rec contains_module cth =
      let doit it =
        match it.ti_item with
        | Th_module _ -> true
        | Th_theory (_, cth) -> contains_module cth
        | _ -> false
      in
      List.exists doit cth.cth_items
    in
    if contains_module dth then
      clone_error oc.oc_env (CE_ThyOverride name);

    let sp =
      match EcEnv.Theory.lookup_opt (unloc thd) oc.oc_env with
      | None -> clone_error oc.oc_env (CE_UnkOverride (OVK_Theory, unloc thd))
      | Some (sp, _) -> sp
    in

    let thd  = let thd = EcPath.toqsymbol sp in (fst thd @ [snd thd]) in
    let xdth = nm @ [x] in

    let rec doit_r prefix (proofs, evc) dth =
      match dth with
      | Th_type (x, _) ->
         let ovrd = `ByPath (EcPath.fromqsymbol (thd @ prefix, x)) in
         let ovrd = (ovrd, mode) in
         ty_ovrd oc (proofs, evc) (loced (xdth @ prefix, x)) ovrd

      | Th_operator (x, ({ op_kind = OB_oper _ })) ->
         let ovrd = `ByPath (EcPath.fromqsymbol (thd @ prefix, x)) in
         let ovrd = (ovrd, mode) in
         op_ovrd oc (proofs, evc) (loced (xdth @ prefix, x)) ovrd

      | Th_operator (x, ({ op_kind = OB_pred _ })) ->
         let ovrd = `ByPath (EcPath.fromqsymbol (thd @ prefix, x)) in
         let ovrd = (ovrd, mode) in
         pr_ovrd oc (proofs, evc) (loced (xdth @ prefix, x)) ovrd

      | Th_operator (x, {op_kind=OB_nott _; _ }) ->
         let ovrd = EcPath.fromqsymbol (thd @ prefix, x) in
         let ovrd = (ovrd, mode) in
         nt_ovrd oc (proofs, evc) (loced (xdth @ prefix, x)) ovrd

      | Th_axiom (x, _) ->
        let axd = loced (thd @ prefix, x) in
        let name = (loced (xdth @ prefix, x)) in
        ax_ovrd oc (proofs, evc) name  (axd, mode)

      | Th_theory (x, dth) when dth.cth_mode = `Concrete ->
         List.fold_left (doit (prefix @ [x])) (proofs, evc) dth.cth_items

      | Th_theory (_, _) ->
          (proofs, evc)

      | Th_export _ ->
         (proofs, evc)

      | Th_module _ ->
         (proofs, evc)

      | Th_modtype (x, _) ->
         modtype_ovrd
           oc (proofs, evc) (loced (xdth @ prefix, x))
           (loced (thd @ prefix, x), mode)

      | Th_instance _   -> (proofs, evc)
      | Th_typeclass _  -> (proofs, evc)

      | Th_baserw _     -> (proofs, evc)
      | Th_addrw  _     -> (proofs, evc)
      | Th_reduction _  -> (proofs, evc)
      | Th_auto _       -> (proofs, evc)

    and doit prefix (proofs, evc) dth =
      doit_r prefix (proofs, evc) dth.ti_item

    in List.fold_left (doit []) (proofs, evc) dth.cth_items

  (* ------------------------------------------------------------------ *)
  let ovrd oc state name (ovrd : theory_override) =
     match ovrd with
     | PTHO_Type tyd ->
        ty_ovrd oc state name tyd

     | PTHO_Op opd ->
        op_ovrd oc state name opd

     | PTHO_Pred prd ->
        pr_ovrd oc state name prd

     | PTHO_Axiom axd ->
        ax_ovrd oc state name axd

     | PTHO_ModTyp mtd ->
       modtype_ovrd oc state name mtd

     | PTHO_Theory thd ->
        th_ovrd oc state name thd
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
  val proof : intheory:bool -> octxt -> evclone -> theory_cloning_proof -> evclone
end = struct
  let all_proof oc evc (name, tags, tactics) =
    let tags =
      if   List.is_empty tags then None
      else Some (List.map (snd_map unloc) tags) in
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

    | Some _ ->
        let update1 evc =
          if Msym.mem (snd name) evc.evc_lemmas.ev_bynames then
              clone_error oc.oc_env (CE_DupOverride (OVK_Lemma, name));
          let map = evc.evc_lemmas.ev_bynames in
          let map = Msym.add (snd name) tactics map in
          let evl = { evc.evc_lemmas with ev_bynames = map } in
          { evc with evc_lemmas = evl }
        in
          evc_update update1 (fst name) evc

  let proof ~intheory oc evc prf =
    match prf.pthp_mode with
    | `All (name, tags) ->
         all_proof oc evc (name, tags, prf.pthp_tactic)
    | `Named (name, hide) ->
         name_proof oc evc (name, (prf.pthp_tactic, hide, not intheory))
end

(* -------------------------------------------------------------------- *)
let clone (scenv : EcSection.scenv) (thcl : theory_cloning) =
  let env = EcSection.env scenv in
  let opath, oth =
    match EcEnv.Theory.lookup_opt ~mode:`All (unloc thcl.pthc_base) env with
    | None -> clone_error env (CE_UnkTheory (unloc thcl.pthc_base))
    | Some x -> x
  in

  let name = odfl (EcPath.basename opath) (thcl.pthc_name |> omap unloc) in
  let oc   = { oc_env = env; oc_oth = oth; } in

  let (genproofs, ovrds) =
    List.fold_left
      (fun st -> curry (OVRD.ovrd oc st))
      ([], evc_empty) thcl.pthc_ext
  in

  let ovrds = List.fold_left (Proofs.proof ~intheory:true oc) ovrds genproofs in
  let ovrds = List.fold_left (Proofs.proof ~intheory:false oc) ovrds thcl.pthc_prf in
  let rename = List.map (Renaming.rename1 oc) thcl.pthc_rnm in

  let ntclr =
    let ntclr1 (`Abbrev, { pl_desc = (nm, x) as q }) =
      if is_none (find_nt oth q) then
        clone_error env (CE_UnkAbbrev q);
      EcPath.pqname (EcPath.extend opath nm) x

    in List.map ntclr1 thcl.pthc_clears
  in

  { cl_name   = name;
    cl_theory = (opath, oth);
    cl_clone  = ovrds;
    cl_rename = rename;
    cl_ntclr  = Sp.of_list ntclr; }
