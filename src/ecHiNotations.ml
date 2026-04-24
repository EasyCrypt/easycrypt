(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcLocation
open EcParsetree
open EcTypes
open EcCoreSubst
open EcEnv

module TT = EcTyping

(* -------------------------------------------------------------------- *)
type nterror =
| NTE_Typing        of EcTyping.tyerror
| NTE_TyNotClosed
| NTE_DupIdent
| NTE_UnknownBinder of symbol
| NTE_AbbrevIsVar
| NTE_UnknownSlot    of symbol
| NTE_DuplicateSlot  of symbol
| NTE_TemplateEmpty
| NTE_BadPunct       of string
| NTE_OptionalEmpty
| NTE_OptionalMustStartWithPunct
| NTE_DefaultOnNonOptional of symbol
| NTE_MissingDefault       of symbol

exception NotationError of EcLocation.t * EcEnv.env * nterror

let nterror loc env e = raise (NotationError (loc, env, e))

(* -------------------------------------------------------------------- *)
let trans_abbrev_opts (opts : abrvopts) =
  List.fold_left (fun _ -> function
   | (b, `Printing) -> not b)
  false opts

(* -------------------------------------------------------------------- *)
(* Pipeline stages used by [trans_notation_r]. Kept internal; the
   public API is [trans_notation]/[trans_abbrev]. *)
module Internal = struct

type binder_slots = {
  bs_entries : (symbol * (EcIdent.t * ty)) list;
  (* (name, ident, type) in declaration order *)
  bs_map     : (EcIdent.t * ty) Msym.t;
  (* name -> (ident, type) for downstream slot lookups *)
}

type form_slots = {
  fs_args     : (EcIdent.t * ty) list;
  (* ident + curried type, in declaration order *)
  fs_map      : (EcIdent.t * ty) Msym.t;
  (* name -> (ident, curried type) *)
  fs_deps     : symbol list Msym.t;
  (* slot name -> binder-dep names, in order *)
  fs_defaults : pformula Msym.t;
  (* slot name -> raw default formula (validated at stage 4,
     typechecked at stage 5) *)
}

type template_info = {
  ti_items : EcDecl.nt_template_item list;
  (* compiled template items; the full [nt_template] record is built
     later by combining these with the typechecked defaults *)
  ti_seen  : bool Msym.t;
  (* slot name -> true if its single occurrence is at a mandatory
     position, false if only inside an optional group *)
}

(* Stage 1: compile binder slots (`#< i : ty, j : ty >`). Each slot
   becomes a fresh ident paired with its translated type. Rejects
   duplicate binder names with [NTE_DupIdent]. *)
let compile_binder_slots
    (env   : env)
    (ue    : EcUnify.unienv)
    (gloc  : EcLocation.t)
    (nt_bd : (psymbol * pty) list)
  : binder_slots
=
  let bd = List.map (fun (x, pty) ->
    let id = EcIdent.create (unloc x) in
    let ty = TT.transty TT.tp_relax env ue pty in
    (unloc x, (id, ty))) nt_bd in

  if not (List.is_unique ~eq:(fun (x, _) (y, _) -> sym_equal x y) bd) then
    nterror gloc env NTE_DupIdent;

  { bs_entries = bd; bs_map = Msym.of_list bd; }

(* -------------------------------------------------------------------- *)
(* Stage 2: compile form slots. Each declared `(f : b1, ..., bn ==> ty)`
   yields a fresh ident whose type is the curried
   `bty_1 -> ... -> bty_n -> ty`, so the body treats the slot as a
   function. Also collects the per-slot binder-dep list (stored on the
   template) and the raw default formulas — those are validated in
   stage 4 and typechecked in stage 5. Rejects duplicate slot names
   with [NTE_DupIdent] and unknown binder deps with
   [NTE_UnknownBinder]. *)
let compile_form_slots
    (env     : env)
    (ue      : EcUnify.unienv)
    (gloc    : EcLocation.t)
    (bd_map  : (EcIdent.t * ty) Msym.t)
    (nt_args : (psymbol * (psymbol list * pty option) * pformula option) list)
  : form_slots
=
  let abd, args_raw = List.split (List.map (fun (x, (xbd, ty), _dflt) ->
      let dty = fun () -> mk_loc (loc x) PTunivar in
      let raw = ([mk_loc (loc x) (Some x)], ofdfl dty ty) in
      (xbd, raw))
    nt_args) in

  let args_plain = snd (TT.trans_binding env ue args_raw) in

  let args =
    List.map2 (fun xbd (aid, aty) ->
      let bd_tys =
        List.map (fun b ->
          match Msym.find_opt (unloc b) bd_map with
          | Some (_, t) -> t
          | None -> nterror (loc b) env (NTE_UnknownBinder (unloc b))) xbd in
      (aid, toarrow bd_tys aty)) abd args_plain in

  if not (List.is_unique ~eq:sym_equal
            (List.map (fun (id, _) -> EcIdent.name id) args)) then
    nterror gloc env NTE_DupIdent;

  let fs_map =
    List.fold_left (fun m (id, ty) -> Msym.add (EcIdent.name id) (id, ty) m)
      Msym.empty args in

  let fs_deps =
    List.fold_left2 (fun m (x, _, _) xbd ->
      Msym.add (unloc x) (List.map unloc xbd) m)
      Msym.empty nt_args abd in

  let fs_defaults =
    List.fold_left (fun m (x, _, d) ->
      match d with
      | None -> m
      | Some f -> Msym.add (unloc x) f m)
      Msym.empty nt_args in

  { fs_args = args; fs_map; fs_deps; fs_defaults; }

(* -------------------------------------------------------------------- *)
(* Stage 3: compile the surface template. Produces the stored
   [nt_template] AND a map [seen] from each referenced slot name to a
   bool — [true] if the (single) occurrence is at a mandatory position,
   [false] if it is inside an optional group. Each slot may appear at
   most once (enforced by [NTE_DuplicateSlot]), so a plain map suffices.
   The map drives the default-validation in stage 4. *)
let compile_template
    (env         : env)
    (gloc        : EcLocation.t)
    (bd_map      : (EcIdent.t * ty) Msym.t)
    (args_map    : (EcIdent.t * ty) Msym.t)
    (slot_deps   : symbol list Msym.t)
    (nt_template : pnt_template)
  : template_info
=
  if List.is_empty nt_template then
    nterror gloc env NTE_TemplateEmpty;

  let compile_punct loc str : EcDecl.nt_punct =
    let kind =
      match EcIo.lex_only_token str with
      | Some EcParser.LBRACKET  -> `LBRACKET
      | Some EcParser.RBRACKET  -> `RBRACKET
      | Some EcParser.COLON     -> `COLON
      | Some EcParser.PIPE      -> `PIPE
      | Some EcParser.COMMA     -> `COMMA
      | Some EcParser.SEMICOLON -> `SEMICOLON
      | _ -> nterror loc env (NTE_BadPunct str) in
    { EcDecl.np_kind = kind; np_display = str; }
  in

  let rec compile_item ~in_optional seen item =
    match item with
    | PNTI_Punct p ->
      (seen, EcDecl.NTI_Punct (compile_punct (loc p) (unloc p)))

    | PNTI_Slot  s ->
      let name = unloc s in
      if Msym.mem name seen then
        nterror (loc s) env (NTE_DuplicateSlot name);
      let seen = Msym.add name (not in_optional) seen in
      if Msym.mem name bd_map then
        (seen, EcDecl.NTI_Slot (name, EcDecl.NTS_Ident))
      else if Msym.mem name args_map then
        let deps = Msym.find name slot_deps in
        (seen, EcDecl.NTI_Slot (name, EcDecl.NTS_Form deps))
      else
        nterror (loc s) env (NTE_UnknownSlot name)

    | PNTI_Optional items ->
      if List.is_empty items then
        nterror gloc env NTE_OptionalEmpty;
      (match List.hd items with
       | PNTI_Punct _ -> ()
       | _ -> nterror gloc env NTE_OptionalMustStartWithPunct);
      let (seen, compiled) =
        List.fold_left (fun (seen, acc) it ->
          let (seen, it) = compile_item ~in_optional:true seen it in
          (seen, it :: acc))
          (seen, []) items in
      (seen, EcDecl.NTI_Optional (List.rev compiled))
  in
  let ti_seen, template_rev =
    List.fold_left (fun (seen, acc) it ->
      let (seen, it) = compile_item ~in_optional:false seen it in
      (seen, it :: acc))
      (Msym.empty, []) nt_template in
  { ti_items = List.rev template_rev; ti_seen; }

(* -------------------------------------------------------------------- *)
(* Stage 4: validate the default/optional-slot invariants. A slot with
   [seen name = false] (only inside an optional group) MUST have a
   default — the expansion needs a value when the group is omitted. A
   slot with a declared default MUST have [seen name = false] —
   otherwise the mandatory occurrence always supplies a value and the
   default is unreachable. *)
let check_defaults
    (env           : env)
    (gloc          : EcLocation.t)
    (slot_dflt_raw : pformula Msym.t)
    (seen          : bool Msym.t)
  : unit
=
  Msym.iter (fun slot_name _ ->
    match Msym.find_opt slot_name seen with
    | Some false -> ()
    | _ -> nterror gloc env (NTE_DefaultOnNonOptional slot_name))
    slot_dflt_raw;
  Msym.iter (fun slot_name is_mandatory ->
    if not is_mandatory && not (Msym.mem slot_name slot_dflt_raw) then
      nterror gloc env (NTE_MissingDefault slot_name))
    seen

(* -------------------------------------------------------------------- *)
(* Stage 5: typecheck each declared default at the slot's curried
   type in the body environment [benv], so the default may reference
   any binder or slot the body can reference. *)
let typecheck_defaults
    (ue            : EcUnify.unienv)
    (benv          : env)
    (args          : (EcIdent.t * ty) list)
    (slot_dflt_raw : pformula Msym.t)
  : expr EcIdent.Mid.t
=
  let args_by_name =
    List.fold_left (fun m (id, ty) ->
      Msym.add (EcIdent.name id) (id, ty) m)
      Msym.empty args in
  Msym.fold (fun slot_name dflt_pf acc ->
    let (slot_id, slot_ty) = Msym.find slot_name args_by_name in
    let pe = mk_loc (loc dflt_pf) (Expr dflt_pf) in
    let dflt_e = TT.transexpcast benv `InOp ue slot_ty pe in
    EcIdent.Mid.add slot_id dflt_e acc)
    slot_dflt_raw EcIdent.Mid.empty

end

(* -------------------------------------------------------------------- *)
let trans_notation_r (env : env) (nt : pnotation located) =
  let nt = nt.pl_desc and gloc = nt.pl_loc in
  let ue = TT.transtyvars env (gloc, nt.nt_tv) in

  let bs = Internal.compile_binder_slots env ue gloc nt.nt_bd in
  let fs = Internal.compile_form_slots env ue gloc bs.bs_map nt.nt_args in

  (* Body env: binder idents + form-slot idents (with curried types). *)
  let all_locals = List.map snd bs.bs_entries @ fs.fs_args in
  let benv       = EcEnv.Var.bind_locals all_locals env in
  let codom      = TT.transty TT.tp_relax env ue nt.nt_codom in
  let body_pe    = mk_loc (loc nt.nt_body) (Expr nt.nt_body) in
  let body       = TT.transexpcast benv `InOp ue codom body_pe in

  let ti =
    Internal.compile_template env gloc bs.bs_map fs.fs_map fs.fs_deps
      nt.nt_template in

  Internal.check_defaults env gloc fs.fs_defaults ti.ti_seen;

  let defaults = Internal.typecheck_defaults ue benv fs.fs_args fs.fs_defaults in

  if not (EcUnify.UniEnv.closed ue) then
    nterror gloc env NTE_TyNotClosed;

  let ts       = Tuni.subst (EcUnify.UniEnv.close ue) in
  let es       = e_subst ts in
  let body     = es body in
  let codom    = ty_subst ts codom in
  let all_xs   = List.map (snd_map (ty_subst ts)) all_locals in
  let defaults = EcIdent.Mid.map es defaults in

  let template : EcDecl.nt_template = {
    nt_items    = ti.ti_items;
    nt_defaults = defaults;
  } in
  let tparams  = EcUnify.UniEnv.tparams ue in
  let op       = EcDecl.mk_notation tparams all_xs (codom, body)
                   template (nt.nt_local :> locality) in

  (unloc nt.nt_name, op)

(* -------------------------------------------------------------------- *)
let trans_notation (env : EcEnv.env) (nt : pnotation located) =
  try  trans_notation_r env nt
  with TT.TyError (loc, env, e) -> nterror loc env (NTE_Typing e)

(* -------------------------------------------------------------------- *)
let trans_abbrev_r (env : env) (at : pabbrev located) =
  let at = at.pl_desc and gloc = at.pl_loc in
  let ue = TT.transtyvars env (gloc, at.ab_tv) in
  let benv, xs = TT.trans_binding env ue at.ab_args in
  let codom = TT.transty TT.tp_relax env ue (fst at.ab_def) in
  let body = TT.transexpcast benv `InOp ue codom (snd at.ab_def) in

  if not (EcUnify.UniEnv.closed ue) then
    nterror gloc env NTE_TyNotClosed;

  let ts = Tuni.subst (EcUnify.UniEnv.close ue) in
  let es = e_subst ts in
  let body    = es body in
  let codom   = ty_subst ts codom in
  let xs      = List.map (snd_map (ty_subst ts)) xs in
  let tparams = EcUnify.UniEnv.tparams ue in
  let ponly   = trans_abbrev_opts at.ab_opts in
  let tyat    = EcDecl.mk_abbrev ~ponly
                  tparams xs (codom, body) (at.ab_local :> locality) in

  if not ponly && EcTypes.is_local body then
    nterror gloc env NTE_AbbrevIsVar;

  (unloc at.ab_name, tyat)

(* -------------------------------------------------------------------- *)
let trans_abbrev (env : EcEnv.env) (nt : pabbrev located) =
  try  trans_abbrev_r env nt
  with TT.TyError (loc, env, e) -> nterror loc env (NTE_Typing e)
