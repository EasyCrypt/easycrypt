(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcTyping
open EcHiInductive

module Sid = EcIdent.Sid
module Mx  = EcPath.Mx

(* -------------------------------------------------------------------- *)
type pragma = {
  pm_verbose : bool; (* true  => display goal after each command *)
  pm_g_prall : bool; (* true  => display all open goals *)
  pm_check   : [`Check | `WeakCheck | `Report];
}

let pragma = ref {
  pm_verbose = true  ;
  pm_g_prall = false ;
  pm_check   = `Check;
}

let pragma_verbose (b : bool) =
  pragma := { !pragma with pm_verbose = b; }

let pragma_g_prall (b : bool) =
  pragma := {!pragma with pm_g_prall = b; }

let pragma_check mode =
  pragma := { !pragma with pm_check = mode; }

module Pragmas = struct
  let silent     = "silent"
  let verbose    = "verbose"

  module Proofs = struct
    let check  = "Proofs:check"
    let weak   = "Proofs:weak"
    let report = "Proofs:report"
  end

  module Goals = struct
    let printall = "Goals:printall"
    let printone = "Goals:printone"
  end
end

exception InvalidPragma of string

let apply_pragma (x : string) =
  match x with
  | x when x = Pragmas.silent         -> pragma_verbose false
  | x when x = Pragmas.verbose        -> pragma_verbose true
  | x when x = Pragmas.Proofs.check   -> pragma_check   `Check
  | x when x = Pragmas.Proofs.weak    -> pragma_check   `WeakCheck
  | x when x = Pragmas.Proofs.report  -> pragma_check   `Report
  | x when x = Pragmas.Goals.printone -> pragma_g_prall false
  | x when x = Pragmas.Goals.printall -> pragma_g_prall true

  | _ -> raise (InvalidPragma x)

(* -------------------------------------------------------------------- *)
exception TopError of EcLocation.t * exn

let rec toperror_of_exn ?gloc exn =
  match exn with
  | TyError    (loc, _, _) -> Some (loc, exn)
  | RcError    (loc, _, _) -> Some (loc, exn)
  | DtError    (loc, _, _) -> Some (loc, exn)
  | ParseError (loc, _)    -> Some (loc, exn)

  | EcCoreGoal.TcError (_, None, _) ->
      Some (odfl _dummy gloc, exn)

  | EcCoreGoal.TcError (_, Some { EcCoreGoal.plc_loc = loc }, _) ->
      let gloc = if EcLocation.isdummy loc then gloc else Some loc in
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
let process_search scope qs =
  EcScope.Search.search scope qs

(* -------------------------------------------------------------------- *)
module ObjectInfo = struct
  exception NoObject

  (* ------------------------------------------------------------------ *)
  type 'a objdump = {
    od_name    : string;
    od_lookup  : EcSymbols.qsymbol -> EcEnv.env -> 'a;
    od_printer : EcPrinting.PPEnv.t -> Format.formatter -> 'a -> unit;
  }

  (* -------------------------------------------------------------------- *)
  let pr_gen_r ?(prcat = false) dumper = fun fmt env qs ->
    try
      let ppe = EcPrinting.PPEnv.ofenv env in
      let obj = dumper.od_lookup qs env in
      if prcat then
        Format.fprintf fmt "* In [%s]:@\n@." dumper.od_name;
      Format.fprintf fmt "%a@\n@." (dumper.od_printer ppe) obj

    with EcEnv.LookupFailure _ -> raise NoObject

  (* -------------------------------------------------------------------- *)
  let pr_gen dumper =
    let theprinter = pr_gen_r dumper in

    fun fmt env qs ->
      try
        theprinter fmt env qs
      with NoObject ->
        Format.fprintf fmt
          "no such object in the category [%s]@." dumper.od_name

  (* ------------------------------------------------------------------ *)
  let pr_ty_r =
    { od_name    = "type declarations";
      od_lookup  = EcEnv.Ty.lookup;
      od_printer = EcPrinting.pp_typedecl; }

  let pr_ty = pr_gen pr_ty_r

  (* ------------------------------------------------------------------ *)
  let pr_op_r =
    let get_ops qs env =
      let l = EcEnv.Op.all qs env in
      if l = [] then raise NoObject;
      l in
    { od_name    = "operators or predicates";
      od_lookup  = get_ops;
      od_printer = 
        fun ppe fmt l ->
          Format.fprintf fmt "@[<v>%a@]"
            (EcPrinting.pp_list "@ " (EcPrinting.pp_opdecl ~long:true ppe)) l; }

  let pr_op = pr_gen pr_op_r

  (* ------------------------------------------------------------------ *)
  let pr_th_r =
    { od_name    = "theories";
      od_lookup  = EcEnv.Theory.lookup ~mode:`All;
      od_printer = EcPrinting.pp_theory; }

  let pr_th = pr_gen pr_th_r

  (* ------------------------------------------------------------------ *)
  let pr_ax_r =
    let get_ops qs env =
      let l = EcEnv.Ax.all ~name:qs env in
      if l = [] then raise NoObject;
      l in
    { od_name    = "lemmas or axioms";
      od_lookup  = get_ops;
      od_printer = 
        fun ppe fmt l ->
          Format.fprintf fmt "@[<v>%a@]"
            (EcPrinting.pp_list "@ " (EcPrinting.pp_axiom ~long:true ppe)) l; }

  let pr_ax = pr_gen pr_ax_r

  (* ------------------------------------------------------------------ *)
  let pr_mod_r =
    { od_name    = "modules";
      od_lookup  = EcEnv.Mod.lookup;
      od_printer = (fun ppe fmt (_, me) -> EcPrinting.pp_modexp ppe fmt me); }

  let pr_mod = pr_gen pr_mod_r

  (* ------------------------------------------------------------------ *)
  let pr_mty_r =
    { od_name    = "module types";
      od_lookup  = EcEnv.ModTy.lookup;
      od_printer = EcPrinting.pp_modsig; }

  let pr_mty = pr_gen pr_mty_r

  (* ------------------------------------------------------------------ *)
  let pr_any fmt env qs =
    let printers = [pr_gen_r ~prcat:true pr_ty_r ;
                    pr_gen_r ~prcat:true pr_op_r ;
                    pr_gen_r ~prcat:true pr_th_r ;
                    pr_gen_r ~prcat:true pr_ax_r ;
                    pr_gen_r ~prcat:true pr_mod_r;
                    pr_gen_r ~prcat:true pr_mty_r; ] in

    let ok = ref (List.length printers) in

    List.iter
      (fun f -> try f fmt env qs with NoObject -> decr ok)
      printers;
    if !ok = 0 then
      Format.fprintf fmt "%s@." "no such object in any category"
end

(* -------------------------------------------------------------------- *)
let process_pr fmt scope p =
  let env = EcScope.env scope in

  match p with
  | Pr_ty   qs -> ObjectInfo.pr_ty  fmt env qs.pl_desc
  | Pr_op   qs -> ObjectInfo.pr_op  fmt env qs.pl_desc
  | Pr_pr   qs -> ObjectInfo.pr_op  fmt env qs.pl_desc
  | Pr_th   qs -> ObjectInfo.pr_th  fmt env qs.pl_desc
  | Pr_ax   qs -> ObjectInfo.pr_ax  fmt env qs.pl_desc
  | Pr_mod  qs -> ObjectInfo.pr_mod fmt env qs.pl_desc
  | Pr_mty  qs -> ObjectInfo.pr_mty fmt env qs.pl_desc
  | Pr_any  qs -> ObjectInfo.pr_any fmt env qs.pl_desc

  | Pr_glob pm -> begin
      let ppe = EcPrinting.PPEnv.ofenv env in
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
      List.iter (fun (xp,_) ->
        let pv = EcTypes.pv_glob xp in
        let ty = EcEnv.Var.by_xpath xp env in
        Format.fprintf fmt "  @[%a : %a@]@."
          (EcPrinting.pp_pv ppe) pv
          (EcPrinting.pp_type ppe) ty.EcEnv.vb_type)
        (List.rev (Mx.bindings us.EcEnv.us_pv))
  end

  | Pr_goal n -> begin
      match EcScope.xgoal scope with
      | None | Some { EcScope.puc_active = None} ->
          EcScope.hierror "no active proof"

      | Some { EcScope.puc_active = Some puc } -> begin
          match puc.EcScope.puc_jdg with
          | EcScope.PSNoCheck -> ()

          | EcScope.PSCheck pf -> begin
              let hds = EcCoreGoal.all_hd_opened pf in
              let sz  = List.length hds in
              let ppe = EcPrinting.PPEnv.ofenv (EcScope.env scope) in

              if n > sz then
                EcScope.hierror "only %n goal(s) remaining" sz;
              if n <= 0 then
                EcScope.hierror "goal ID must be positive";
              let penv = EcCoreGoal.proofenv_of_proof pf in
              let goal = List.nth hds (n-1) in
              let goal = EcCoreGoal.FApi.get_pregoal_by_id goal penv in
              let goal = (EcEnv.LDecl.tohyps goal.EcCoreGoal.g_hyps,
                          goal.EcCoreGoal.g_concl) in

              Format.fprintf fmt "Printing Goal %d\n\n%!" n;
              EcPrinting.pp_goal ppe fmt (goal, `One sz)
          end
      end
  end

(* -------------------------------------------------------------------- *)
let process_print scope p =
  process_pr Format.std_formatter scope p

(* -------------------------------------------------------------------- *)
exception Pragma of [`Reset]

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
    EcScope.notify scope `Info "added type: `%s'" (unloc tyd.pl_desc.pty_name);
    scope

(* -------------------------------------------------------------------- *)
and process_types (scope : EcScope.scope) tyds =
  List.fold_left process_type scope tyds

(* -------------------------------------------------------------------- *)
and process_typeclass (scope : EcScope.scope) (tcd : ptypeclass located) =
  EcScope.check_state `InTop "type class" scope;
  let scope = EcScope.Ty.add_class scope tcd in
    EcScope.notify scope `Info "added type class: `%s'" (unloc tcd.pl_desc.ptc_name);
    scope

(* -------------------------------------------------------------------- *)
and process_tycinst (scope : EcScope.scope) (tci : ptycinstance located) =
  EcScope.check_state `InTop "type class instance" scope;
  EcScope.Ty.add_instance scope (!pragma).pm_check tci

(* -------------------------------------------------------------------- *)
and process_module (scope : EcScope.scope) m =
  EcScope.check_state `InTop "module" scope;
  EcScope.Mod.add scope m

(* -------------------------------------------------------------------- *)
and process_declare (scope : EcScope.scope) x =
  match x with
  | PDCL_Module m -> begin
      EcScope.check_state `InTop "module" scope;
      EcScope.Mod.declare scope m
  end

(* -------------------------------------------------------------------- *)
and process_interface (scope : EcScope.scope) (x, i) =
  EcScope.check_state `InTop "interface" scope;
  EcScope.ModType.add scope x.pl_desc i

(* -------------------------------------------------------------------- *)
and process_operator (scope : EcScope.scope) (op : poperator located) =
  EcScope.check_state `InTop "operator" scope;
  let scope = EcScope.Op.add scope op in
    List.iter
      (fun { pl_desc = name } ->
        EcScope.notify scope `Info "added operator: `%s'" name)
      (op.pl_desc.po_name :: op.pl_desc.po_aliases);
    scope

(* -------------------------------------------------------------------- *)
and process_predicate (scope : EcScope.scope) (p : ppredicate located) =
  EcScope.check_state `InTop "predicate" scope;
  let scope = EcScope.Pred.add scope p in
    EcScope.notify scope `Info "added predicate: `%s'" (unloc p.pl_desc.pp_name);
    scope

(* -------------------------------------------------------------------- *)
and process_choice (scope : EcScope.scope) (c : pchoice located) =
  EcScope.check_state `InTop "choice" scope;
  let scope = EcScope.Op.add_choiceop scope c in
    EcScope.notify scope `Info "added choice operator: `%s'" (unloc c.pl_desc.pc_name);
    scope                                 (* FIXME *)

(* -------------------------------------------------------------------- *)
and process_axiom (scope : EcScope.scope) (ax : paxiom located) =
  EcScope.check_state `InTop "axiom" scope;
  let (name, scope) = EcScope.Ax.add scope (!pragma).pm_check ax in
    name |> EcUtils.oiter
      (fun x ->
         match (unloc ax).pa_kind with
         | PAxiom _ -> EcScope.notify scope `Info "added axiom: `%s'" x
         | _        -> EcScope.notify scope `Info "added lemma: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_th_open (scope : EcScope.scope) (abs, name) =
  EcScope.check_state `InTop "theory" scope;
  EcScope.Theory.enter scope (if abs then `Abstract else `Concrete) name

(* -------------------------------------------------------------------- *)
and process_th_close (scope : EcScope.scope) name =
  EcScope.check_state `InTop "theory closing" scope;
  if (fst (EcScope.name scope)) <> name then
    EcScope.hierror
      "active theory has name `%s', not `%s'"
      (fst (EcScope.name scope)) name;
  snd (EcScope.Theory.exit scope)

(* -------------------------------------------------------------------- *)
and process_th_require1 ld scope (x, io) =
  EcScope.check_state `InTop "theory require" scope;

  let name  = x.pl_desc in
    match EcLoader.locate name ld with
    | None ->
        EcScope.hierror "cannot locate theory `%s'" name

    | Some (filename, kind) ->
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

        let kind = match kind with `Ec -> `Concrete | `EcA -> `Abstract in

        let scope = EcScope.Theory.require scope (name, kind) loader in
          match io with
          | None         -> scope
          | Some `Export -> EcScope.Theory.export scope ([], name)
          | Some `Import -> EcScope.Theory.import scope ([], name)

(* -------------------------------------------------------------------- *)
and process_th_require ld scope (xs, io) =
  List.fold_left
    (fun scope x -> process_th_require1 ld scope (x, io))
    scope xs

(* -------------------------------------------------------------------- *)
and process_th_import (scope : EcScope.scope) (names : pqsymbol list) =
  EcScope.check_state `InTop "theory import" scope;
  List.fold_left EcScope.Theory.import scope (List.map unloc names)

(* -------------------------------------------------------------------- *)
and process_th_export (scope : EcScope.scope) (names : pqsymbol list) =
  EcScope.check_state `InTop "theory export" scope;
  List.fold_left EcScope.Theory.export scope (List.map unloc names)

(* -------------------------------------------------------------------- *)
and process_th_clone (scope : EcScope.scope) thcl =
  EcScope.check_state `InTop "theory cloning" scope;
  EcScope.Cloning.clone scope (!pragma).pm_check thcl

(* -------------------------------------------------------------------- *)
and process_w3_import (scope : EcScope.scope) (p, f, r) =
  EcScope.check_state `InTop "why3 import" scope;
  EcScope.Theory.import_w3 scope p f r

(* -------------------------------------------------------------------- *)
and process_sct_open (scope : EcScope.scope) name =
  EcScope.check_state `InTop "section opening" scope;
  EcScope.Section.enter scope name

(* -------------------------------------------------------------------- *)
and process_sct_close (scope : EcScope.scope) name =
  EcScope.check_state `InTop "section closing" scope;
  EcScope.Section.exit scope name

(* -------------------------------------------------------------------- *)
and process_tactics (scope : EcScope.scope) t =
  let mode = !pragma.pm_check in
  match t with
  | `Actual t  -> EcScope.Tactics.process scope mode t
  | `Proof  pm -> EcScope.Tactics.proof   scope mode pm.pm_strict

(* -------------------------------------------------------------------- *)
and process_save (scope : EcScope.scope) loc =
  let (name, scope) = EcScope.Ax.save scope loc in
    name |> EcUtils.oiter
      (fun x -> EcScope.notify scope `Info "added lemma: `%s'" x);
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
  let pragma_check mode =
    match EcScope.goal scope with
    | Some { EcScope.puc_mode = Some false } ->
        EcScope.hierror "pragma [Proofs:*] in non-strict proof script";
    | _ -> pragma_check mode
  in

  match unloc opt with
  | x when x = Pragmas.silent         -> pragma_verbose false
  | x when x = Pragmas.verbose        -> pragma_verbose true
  | x when x = Pragmas.Proofs.weak    -> pragma_check   `WeakCheck
  | x when x = Pragmas.Proofs.check   -> pragma_check   `Check
  | x when x = Pragmas.Proofs.report  -> pragma_check   `Report
  | x when x = Pragmas.Goals.printall -> pragma_g_prall true
  | x when x = Pragmas.Goals.printone -> pragma_g_prall false

  | "noop"    -> ()
  | "compact" -> Gc.compact ()
  | "reset"   -> raise (Pragma `Reset)
  | _         -> ()

(* -------------------------------------------------------------------- *)
and process_option (scope : EcScope.scope) (name, value) =
  match unloc name with
  | "implicits" -> EcScope.Options.set_implicits scope value
  | _ -> EcScope.hierror "unknown option: %s" (unloc name)

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
      | Gchoice      c    -> `Fct   (fun scope -> process_choice     scope  (mk_loc loc c))
      | Gaxiom       a    -> `Fct   (fun scope -> process_axiom      scope  (mk_loc loc a))
      | GthOpen      name -> `Fct   (fun scope -> process_th_open    scope  (snd_map unloc name))
      | GthClose     name -> `Fct   (fun scope -> process_th_close   scope  name.pl_desc)
      | GthRequire   name -> `Fct   (fun scope -> process_th_require ld scope name)
      | GthImport    name -> `Fct   (fun scope -> process_th_import  scope  name)
      | GthExport    name -> `Fct   (fun scope -> process_th_export  scope  name)
      | GthClone     thcl -> `Fct   (fun scope -> process_th_clone   scope  thcl)
      | GsctOpen     name -> `Fct   (fun scope -> process_sct_open   scope  name)
      | GsctClose    name -> `Fct   (fun scope -> process_sct_close  scope  name)
      | GthW3        a    -> `Fct   (fun scope -> process_w3_import  scope  a)
      | Gprint       p    -> `Fct   (fun scope -> process_print      scope  p; scope)
      | Gsearch      qs   -> `Fct   (fun scope -> process_search     scope  qs; scope)
      | Gtactics     t    -> `Fct   (fun scope -> process_tactics    scope  t)
      | Grealize     p    -> `Fct   (fun scope -> process_realize    scope  p)
      | Gprover_info pi   -> `Fct   (fun scope -> process_proverinfo scope  pi)
      | Gsave        loc  -> `Fct   (fun scope -> process_save       scope  loc)
      | Gpragma      opt  -> `State (fun scope -> process_pragma     scope  opt)
      | Goption      opt  -> `Fct   (fun scope -> process_option     scope  opt)
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
let loader = EcLoader.create ()

let addidir ?system ?recursive (idir : string) =
  EcLoader.addidir ?system ?recursive idir loader

let loadpath () =
  List.map fst (EcLoader.aslist loader)

(* -------------------------------------------------------------------- *)
type checkmode = {
  cm_checkall  : bool;
  cm_timeout   : int;
  cm_cpufactor : int;
  cm_nprovers  : int;
  cm_provers   : string list option;
  cm_wrapper   : string option;
  cm_profile   : bool;
}

let initial ~checkmode ~boot =
  let checkall  = checkmode.cm_checkall  in
  let wrapper   = checkmode.cm_wrapper   in
  let profile   = checkmode.cm_profile   in
  let poptions  = {
    EcScope.Prover.po_timeout   = Some checkmode.cm_timeout;
    EcScope.Prover.po_cpufactor = Some checkmode.cm_cpufactor;
    EcScope.Prover.po_nprovers  = Some checkmode.cm_nprovers;
    EcScope.Prover.po_provers   = checkmode.cm_provers;
  } in

  let prelude = (mk_loc _dummy "Prelude", Some `Export) in
  let loader  = EcLoader.forsys loader in
  let gstate  = EcGState.from_flags [("profile", profile)] in
  let scope   = EcScope.empty gstate in
  let scope   = if boot then scope else process_th_require1 loader scope prelude in

  let scope = EcScope.Prover.set_wrapper scope wrapper in
  let scope = EcScope.Prover.set_default scope poptions in
  let scope = if checkall then EcScope.Prover.full_check scope else scope in

  EcScope.freeze scope

(* -------------------------------------------------------------------- *)
type context = {
  ct_level   : int;
  ct_current : EcScope.scope;
  ct_root    : EcScope.scope;
  ct_stack   : (EcScope.scope list) option;
}

let context = ref (None : context option)

let rootctxt ?(undo = true) (scope : EcScope.scope) =
  { ct_level   = 0;
    ct_current = scope;
    ct_root    = scope;
    ct_stack   = if undo then Some [] else None; }

(* -------------------------------------------------------------------- *)
let pop_context context =
  match context.ct_stack with
  | None -> EcScope.hierror "undo stack disabled"
  | Some stack ->
      assert (not (List.is_empty stack));
      { ct_level   = context.ct_level - 1;
        ct_root    = context.ct_root;
        ct_current = List.hd stack;
        ct_stack   = Some (List.tl stack); }

(* -------------------------------------------------------------------- *)
let push_context scope context =
  { ct_level   = context.ct_level + 1;
    ct_root    = context.ct_root;
    ct_current = scope;
    ct_stack   = context.ct_stack
      |> omap (fun st -> context.ct_current :: st); }

(* -------------------------------------------------------------------- *)
let initialize ~undo ~boot ~checkmode =
  assert (!context = None);
  context := Some (rootctxt ~undo (initial ~checkmode ~boot))

(* -------------------------------------------------------------------- *)
type notifier = EcGState.loglevel -> string Lazy.t -> unit

let addnotifier (notifier : notifier) =
  assert (EcUtils.is_some !context);
  let gstate = EcScope.gstate (oget !context).ct_root in
  ignore (EcGState.add_notifier notifier gstate)

(* -------------------------------------------------------------------- *)
let current () =
  (oget !context).ct_current

(* -------------------------------------------------------------------- *)
let uuid () : int =
  (oget !context).ct_level

(* -------------------------------------------------------------------- *)
let mode () : string =
  match (!pragma).pm_check with
  | `Check     -> "check"
  | `WeakCheck -> "weakcheck"
  | `Report    -> "report"

(* -------------------------------------------------------------------- *)
let undo (olduuid : int) =
  if olduuid < (uuid ()) then
    for i = (uuid ()) - 1 downto olduuid do
      context := Some (pop_context (oget !context))
    done

(* -------------------------------------------------------------------- *)
let reset () =
  context := Some (rootctxt (oget !context).ct_root)

(* -------------------------------------------------------------------- *)
let process (g : global located) : unit =
  let current = oget !context in
  let scope   = current.ct_current in

  try
    process loader scope g
      |> oiter (fun scope -> context := Some (push_context scope current))
  with Pragma `Reset ->
    reset ()

(* -------------------------------------------------------------------- *)
module S = EcScope
module L = EcBaseLogic

let pp_current_goal ?(all = false) stream =
  let scope = current () in

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

          | Some (n, g) ->
              let get_hc { EcCoreGoal.g_hyps; EcCoreGoal.g_concl } =
                (EcEnv.LDecl.tohyps g_hyps, g_concl)
              in

              if all then
                let subgoals = EcCoreGoal.all_opened pf in
                let subgoals = odfl [] (List.otail subgoals) in
                let subgoals = List.map get_hc subgoals in
                EcPrinting.pp_goal ppe stream (get_hc g, `All subgoals)
              else
                EcPrinting.pp_goal ppe stream (get_hc g, `One n)
      end
  end

let pp_maybe_current_goal stream =
  match (!pragma).pm_verbose with
  | true  -> pp_current_goal ~all:(!pragma).pm_g_prall stream
  | false -> ()
