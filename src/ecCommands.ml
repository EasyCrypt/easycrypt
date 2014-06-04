(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcTyping

module Sid = EcIdent.Sid
module Mx  = EcPath.Mx

(* -------------------------------------------------------------------- *)
type pragma = {
  pm_verbose : bool; (* true  => display goal after each command *)
  pm_check   : bool; (* false => don't check proof scripts *)
}

let pragma = ref { pm_verbose = true; pm_check = true; }

let pragma_verbose (b : bool) =
  pragma := { !pragma with pm_verbose = b; }

let pragma_check (b : bool) =
  pragma := { !pragma with pm_check = b; }

(* -------------------------------------------------------------------- *)
exception TopError of EcLocation.t * exn

let rec toperror_of_exn ?gloc exn =
  match exn with
  | TyError  (loc, _, _)   -> Some (loc, exn)
  | ParseError (loc, _)    -> Some (loc, exn)

  | EcCoreGoal.TcError (_, _, _) ->
      Some (odfl _dummy gloc, exn)

  | LocError (loc, e)    -> begin
      let gloc = if EcLocation.isdummy loc then gloc else Some loc in
      match toperror_of_exn ?gloc e with
      | None -> Some (loc, e)
      | Some (loc, e) -> Some (loc, e)
    end

  | TopError (loc, e) ->
      let gloc = if EcLocation.isdummy loc then gloc else Some loc in
        Some (odfl _dummy gloc, e)

  | EcScope.HiScopeError (loc, msg) ->
      let gloc =
        match loc with
        | None     -> gloc
        | Some loc -> if EcLocation.isdummy loc then gloc else Some loc
      in
        Some (odfl _dummy gloc, EcScope.HiScopeError (None, msg))

  | _ -> None

let toperror_of_exn ?gloc exn =
  match toperror_of_exn ?gloc exn with
  | Some (loc, exn) -> TopError (loc, exn)
  | None            -> exn

let pp_toperror fmt loc exn =
  Format.fprintf fmt "%s: %a"
    (EcLocation.tostring loc)
    EcPException.exn_printer exn

let () =
  let pp fmt exn =
    match exn with
    | TopError (loc, exn) -> pp_toperror fmt loc exn
    | _ -> raise exn
  in
    EcPException.register pp

(* -------------------------------------------------------------------- *)
let process_pr fmt scope p =
  let env = EcScope.env scope in
  let ppe = EcPrinting.PPEnv.ofenv env in

  match p with
  | Pr_ty qs ->
      let (x, ty) = EcEnv.Ty.lookup qs.pl_desc env in
      Format.fprintf fmt "%a@." (EcPrinting.pp_typedecl ppe) (x, ty)

  | Pr_glob pm -> begin
      let (p, _) = EcTyping.trans_msymbol env pm in
      let us = EcEnv.NormMp.mod_use env p in

      Format.fprintf fmt "Globals [# = %d]:@."
        (Sid.cardinal us.EcEnv.us_gl);
      Sid.iter (fun id ->
        Format.fprintf fmt "  %s@." (EcIdent.name id))
        us.EcEnv.us_gl;

      Format.fprintf fmt "@.";

      Format.fprintf fmt "Prog. variables [# = %d]:@."
        (Mx.cardinal us.EcEnv.us_pv);
      Mx.iter (fun xp _ ->
        let pv = EcTypes.pv_glob xp in
        let ty = EcEnv.Var.by_xpath xp env in
        Format.fprintf fmt "  @[%a : %a@]@."
          (EcPrinting.pp_pv ppe) pv
          (EcPrinting.pp_type ppe) ty.EcEnv.vb_type)
        us.EcEnv.us_pv
  end

  | Pr_op qs | Pr_pr qs ->
      let (x, op) = EcEnv.Op.lookup qs.pl_desc env in
      Format.fprintf fmt "%a@." (EcPrinting.pp_opdecl ppe) (x, op)

  | Pr_th qs ->
      let (p, th) = EcEnv.Theory.lookup qs.pl_desc env in
      Format.fprintf fmt "%a@." (EcPrinting.pp_theory ppe) (p, th)

  | Pr_ax qs ->
      let (p, ax) = EcEnv.Ax.lookup qs.pl_desc env in
      Format.fprintf fmt "%a@." (EcPrinting.pp_axiom ppe) (p, ax)

  | Pr_mod qs ->
      let (_p, me) = EcEnv.Mod.lookup qs.pl_desc env in
      Format.fprintf fmt "%a@." (EcPrinting.pp_modexp ppe) me

  | Pr_mty qs ->
      let (p, ms) = EcEnv.ModTy.lookup qs.pl_desc env in
      Format.fprintf fmt "%a@." (EcPrinting.pp_modsig ppe) (p, ms)

let process_print scope p =
  process_pr Format.std_formatter scope p

(* -------------------------------------------------------------------- *)
type notifier = string -> unit

let default_notifier msg =
  Format.eprintf "%s\n%!" msg

let _notifier = ref (default_notifier : notifier)

let set_notifier (n : notifier) = _notifier := n
let get_notifier () = !_notifier

let notify scope msg =
  Format.ksprintf
    (fun msg ->
      if EcScope.verbose scope then !_notifier msg)
    msg

(* -------------------------------------------------------------------- *)
let rec process_type (scope : EcScope.scope) (tyd : ptydecl located) =
  EcScope.check_state `InTop "type" scope;

  let tyname = (tyd.pl_desc.pty_tyvars, tyd.pl_desc.pty_name) in
  let scope =
    match tyd.pl_desc.pty_body with
    | PTYD_Abstract bd -> EcScope.Ty.add          scope (mk_loc tyd.pl_loc tyname) bd
    | PTYD_Alias    bd -> EcScope.Ty.define       scope (mk_loc tyd.pl_loc tyname) bd
    | PTYD_Datatype bd -> EcScope.Ty.add_datatype scope (mk_loc tyd.pl_loc tyname) bd
    | PTYD_Record   bd -> EcScope.Ty.add_record   scope (mk_loc tyd.pl_loc tyname) bd
  in
    notify scope "added type: `%s'" (unloc tyd.pl_desc.pty_name);
    scope

(* -------------------------------------------------------------------- *)
and process_types (scope : EcScope.scope) tyds =
  List.fold_left process_type scope tyds

(* -------------------------------------------------------------------- *)
and process_typeclass (scope : EcScope.scope) (tcd : ptypeclass located) =
  EcScope.check_state `InTop "type class" scope;
  let scope = EcScope.Ty.add_class scope tcd in
    notify scope "added type class: `%s'" (unloc tcd.pl_desc.ptc_name);
    scope

(* -------------------------------------------------------------------- *)
and process_tycinst (scope : EcScope.scope) (tci : ptycinstance located) =
  EcScope.check_state `InTop "type class instance" scope;
  let mode = if (!pragma).pm_check then `Check else `WeakCheck in
  let scope = EcScope.Ty.add_instance scope mode tci in
    scope

(* -------------------------------------------------------------------- *)
and process_module (scope : EcScope.scope) m =
  EcScope.check_state `InTop "module" scope;
  EcScope.Mod.add scope m

(* -------------------------------------------------------------------- *)
and process_declare (scope : EcScope.scope) m =
  EcScope.check_state `InTop "module" scope;
  EcScope.Mod.declare scope m

(* -------------------------------------------------------------------- *)
and process_interface (scope : EcScope.scope) (x, i) =
  EcScope.check_state `InTop "interface" scope;
  EcScope.ModType.add scope x.pl_desc i

(* -------------------------------------------------------------------- *)
and process_operator (scope : EcScope.scope) (op : poperator located) =
  EcScope.check_state `InTop "operator" scope;
  let scope = EcScope.Op.add scope op in
    notify scope "added operator: `%s'" (unloc op.pl_desc.po_name);
    scope

(* -------------------------------------------------------------------- *)
and process_predicate (scope : EcScope.scope) (p : ppredicate located) =
  EcScope.check_state `InTop "predicate" scope;
  let scope = EcScope.Pred.add scope p in
    notify scope "added predicate: `%s'" (unloc p.pl_desc.pp_name);
    scope

(* -------------------------------------------------------------------- *)
and process_axiom (scope : EcScope.scope) (ax : paxiom located) =
  EcScope.check_state `InTop "axiom" scope;
  let mode = if (!pragma).pm_check then `Check else `WeakCheck in
  let (name, scope) = EcScope.Ax.add scope mode ax in
    name |> EcUtils.oiter
      (fun x -> notify scope "added axiom: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_th_open (scope : EcScope.scope) name =
  EcScope.check_state `InTop "theory" scope;
  EcScope.Theory.enter scope name

(* -------------------------------------------------------------------- *)
and process_th_close (scope : EcScope.scope) name =
  EcScope.check_state `InTop "theory closing" scope;
  if (EcScope.name scope) <> name then
    EcScope.hierror
      "active theory has name `%s', not `%s'"
      (EcScope.name scope) name;
  snd (EcScope.Theory.exit scope)

(* -------------------------------------------------------------------- *)
and process_th_require ld scope (x, io) =
  EcScope.check_state `InTop "theory require" scope;

  let name  = x.pl_desc in
    match EcLoader.locate name ld with
    | None ->
        EcScope.hierror "cannot locate theory `%s'" name

    | Some filename ->
        let dirname = Filename.dirname filename in
        let subld   = EcLoader.dup ld in

        EcLoader.addidir dirname subld;

        let loader iscope =
          let i_pragma = !pragma in

          try
            let commands = EcIo.parseall (EcIo.from_file filename) in
            let commands = List.fold_left (process_internal subld) iscope commands in
              pragma := i_pragma; commands
          with e ->
            pragma := i_pragma; raise e
        in

        let scope = EcScope.Theory.require scope name loader in
          match io with
          | None         -> scope
          | Some `Export -> process_th_export scope ([], name)
          | Some `Import -> process_th_import scope ([], name)

(* -------------------------------------------------------------------- *)
and process_th_import (scope : EcScope.scope) name =
  EcScope.check_state `InTop "theory import" scope;
  EcScope.Theory.import scope name

(* -------------------------------------------------------------------- *)
and process_th_export (scope : EcScope.scope) name =
  EcScope.check_state `InTop "theory export" scope;
  EcScope.Theory.export scope name

(* -------------------------------------------------------------------- *)
and process_th_clone (scope : EcScope.scope) (thcl, io) =
  EcScope.check_state `InTop "theory cloning" scope;
  let mode = if (!pragma).pm_check then `Check else `WeakCheck in
  let (name, scope) = EcScope.Theory.clone scope mode thcl in
    match io with
    | None         -> scope
    | Some `Export -> process_th_export scope ([], name)
    | Some `Import -> process_th_import scope ([], name)

(* -------------------------------------------------------------------- *)
and process_w3_import (scope : EcScope.scope) (p, f, r) =
  EcScope.check_state `InTop "why3 import" scope;
  EcScope.Theory.import_w3 scope p f r

(* -------------------------------------------------------------------- *)
and process_sct_open (scope : EcScope.scope) =
  EcScope.check_state `InTop "section opening" scope;
  EcScope.Section.enter scope

(* -------------------------------------------------------------------- *)
and process_sct_close (scope : EcScope.scope) =
  EcScope.check_state `InTop "section closing" scope;
  EcScope.Section.exit scope

(* -------------------------------------------------------------------- *)
and process_tactics (scope : EcScope.scope) t =
  let mode = if (!pragma.pm_check) then `Check else `WeakCheck in

  match t with
  | `Actual t  -> EcScope.Tactics.process scope mode t
  | `Proof  pm -> EcScope.Tactics.proof   scope mode pm.pm_strict

(* -------------------------------------------------------------------- *)
and process_save (scope : EcScope.scope) loc =
  let (name, scope) = EcScope.Ax.save scope loc in
    name |> EcUtils.oiter
      (fun x -> notify scope "added lemma: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_realize (scope : EcScope.scope) name =
  EcScope.Ax.activate scope name

(* -------------------------------------------------------------------- *)
and process_proverinfo scope pi =
  let scope = EcScope.Prover.process scope pi in
    scope

(* -------------------------------------------------------------------- *)
and process_pragma (scope : EcScope.scope) opt =
  let check mode =
    match EcScope.goal scope with
    | Some { EcScope.puc_mode = Some false } ->
        EcScope.hierror "pragma [check|nocheck] in non-strict proof script";
    | _ -> pragma_check mode
  in

  begin
    match unloc opt with
    | "silent"  -> pragma_verbose false
    | "verbose" -> pragma_verbose true
    | "nocheck" -> check false
    | "check"   -> check true
    | "noop"    -> ()
    | _         -> ()
  end

(* -------------------------------------------------------------------- *)
and process_extract scope todo =
  EcScope.Extraction.process scope todo

(* -------------------------------------------------------------------- *)
and process_addrw scope todo =
  EcScope.BaseRw.process_addrw scope todo

(* -------------------------------------------------------------------- *)
and process (ld : EcLoader.ecloader) (scope : EcScope.scope) g =
  let loc = g.pl_loc in

  let scope =
    match
      match g.pl_desc with
      | Gtype        t    -> `Fct   (fun scope -> process_types      scope  (List.map (mk_loc loc) t))
      | Gtypeclass   t    -> `Fct   (fun scope -> process_typeclass  scope  (mk_loc loc t))
      | Gtycinstance t    -> `Fct   (fun scope -> process_tycinst    scope  (mk_loc loc t))
      | Gmodule      m    -> `Fct   (fun scope -> process_module     scope  m)
      | Gdeclare     m    -> `Fct   (fun scope -> process_declare    scope  m)
      | Ginterface   i    -> `Fct   (fun scope -> process_interface  scope  i)
      | Goperator    o    -> `Fct   (fun scope -> process_operator   scope  (mk_loc loc o))
      | Gpredicate   p    -> `Fct   (fun scope -> process_predicate  scope  (mk_loc loc p))
      | Gaxiom       a    -> `Fct   (fun scope -> process_axiom      scope  (mk_loc loc a))
      | GthOpen      name -> `Fct   (fun scope -> process_th_open    scope  name.pl_desc)
      | GthClose     name -> `Fct   (fun scope -> process_th_close   scope  name.pl_desc)
      | GthRequire   name -> `Fct   (fun scope -> process_th_require ld scope name)
      | GthImport    name -> `Fct   (fun scope -> process_th_import  scope  name.pl_desc)
      | GthExport    name -> `Fct   (fun scope -> process_th_export  scope  name.pl_desc)
      | GthClone     thcl -> `Fct   (fun scope -> process_th_clone   scope  thcl)
      | GsctOpen          -> `Fct   (fun scope -> process_sct_open   scope)
      | GsctClose         -> `Fct   (fun scope -> process_sct_close  scope)
      | GthW3        a    -> `Fct   (fun scope -> process_w3_import  scope  a)
      | Gprint       p    -> `Fct   (fun scope -> process_print      scope  p; scope)
      | Gtactics     t    -> `Fct   (fun scope -> process_tactics    scope  t)
      | Grealize     p    -> `Fct   (fun scope -> process_realize    scope  p)
      | Gprover_info pi   -> `Fct   (fun scope -> process_proverinfo scope  pi)
      | Gsave        loc  -> `Fct   (fun scope -> process_save       scope  loc)
      | Gpragma      opt  -> `State (fun scope -> process_pragma     scope  opt)
      | Gextract     todo -> `Fct   (fun scope -> process_extract    scope todo)
      | Gaddrw       hint -> `Fct   (fun scope -> process_addrw      scope hint)
    with
    | `Fct   f -> Some (f scope)
    | `State f -> f scope; None
  in
    scope

(* -------------------------------------------------------------------- *)
and process_internal ld scope g =
  odfl scope (process ld scope g)

(* -------------------------------------------------------------------- *)
let loader  = EcLoader.create ()

let addidir ?system ?recursive (idir : string) =
  EcLoader.addidir ?system ?recursive idir loader

let loadpath () =
  List.map fst (EcLoader.aslist loader)

(* -------------------------------------------------------------------- *)
let initial ~boot ~wrapper =
  let prelude = (mk_loc _dummy "Prelude", Some `Export) in
  let loader  = EcLoader.forsys loader in
  let scope   = EcScope.empty in
  let scope   =
    if   boot
    then scope
    else
      List.fold_left
        (fun scope th -> process_th_require loader scope th)
        scope [prelude]
  in

  let scope   = EcScope.Prover.set_wrapper scope wrapper in
    scope

(* -------------------------------------------------------------------- *)
let context = ref None

(* -------------------------------------------------------------------- *)
let initialize ~boot ~wrapper =
  assert (!context = None);
  context := Some (0, initial ~boot ~wrapper, [])

(* -------------------------------------------------------------------- *)
let current () =
  let (_, scope, _) = oget !context in scope

(* -------------------------------------------------------------------- *)
let full_check b ~timeout ~nprovers provers =
  let (idx, scope, l) = oget !context in
  assert (idx = 0 && l = []);
  let scope = EcScope.Prover.set_default scope ~timeout ~nprovers provers in
  let scope = if b then EcScope.Prover.full_check scope else scope in
    context := Some (idx, scope, l)

(* -------------------------------------------------------------------- *)
let uuid () : int =
  let (idx, _, _) = oget !context in idx

(* -------------------------------------------------------------------- *)
let mode () : string =
  match (!pragma).pm_check with
  | true  -> "check"
  | false -> "nocheck"

(* -------------------------------------------------------------------- *)
let undo (olduuid : int) =
  if olduuid < (uuid ()) then
    begin
      for i = (uuid ()) - 1 downto olduuid do
        let (_, _scope, stack) = oget !context in
        context := Some (i, List.hd stack, List.tl stack)
      done
    end

(* -------------------------------------------------------------------- *)
let process (g : global located) =
  let (idx, scope, stack) = oget !context in
    match process loader scope g with
    | None -> ()
    | Some newscope -> context := Some (idx+1, newscope, scope :: stack)

(* -------------------------------------------------------------------- *)
module S = EcScope
module L = EcBaseLogic

let pp_current_goal stream =
  let (_, scope, _) = oget !context in

  match S.xgoal scope with
  | None -> ()

  | Some { S.puc_active = None; S.puc_cont = ct } ->
      Format.fprintf stream "Remaining lemmas to prove:@\n%!";
      List.iter
        (fun ((_, ax), p, env) ->
           let ppe = EcPrinting.PPEnv.ofenv env in
           Format.fprintf stream " %s: %a@\n%!"
             (EcPath.tostring p)
             (EcPrinting.pp_form ppe) (oget ax.EcDecl.ax_spec))
        (fst ct)

  | Some { S.puc_active = Some puc } -> begin
      match puc.S.puc_jdg with
      | S.PSNoCheck -> ()

      | S.PSCheck pf -> begin
          let ppe = EcPrinting.PPEnv.ofenv (S.env scope) in

          match EcCoreGoal.opened pf with
          | None -> Format.fprintf stream "No more goals@\n%!"

          | Some (n, { EcCoreGoal.g_hyps  = hyps;
                       EcCoreGoal.g_concl = concl; })
            ->
              let g = EcEnv.LDecl.tohyps hyps, concl in
                EcPrinting.pp_goal ppe stream (n, g)
      end
  end

let pp_maybe_current_goal stream =
  match (!pragma).pm_verbose with
  | true  -> pp_current_goal stream
  | false -> ()
