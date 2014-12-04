(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
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
  | TyError    (loc, _, _) -> Some (loc, exn)
  | RcError    (loc, _, _) -> Some (loc, exn)
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
module Search = struct
  let search fmt (scope : EcScope.scope) qs  =
    let env = EcScope.env scope in
    let all_path = EcEnv.Op.all (fun _ -> true) qs.pl_desc env in
    let ppe = EcPrinting.PPEnv.ofenv env in

    let do1 fmt (p, _) =
      let rec exists f =
        match f.EcFol.f_node with
        | EcFol.Fop(p', _) -> EcPath.p_equal p p' 
        | _ -> EcFol.form_exists exists f in

      let doax pax ax = 
        match ax.EcDecl.ax_spec with
        | None -> ()
        | Some f -> 
          if exists f then
            Format.fprintf fmt "%a@ " (EcPrinting.pp_axiom ppe) (pax, ax)
      in EcEnv.Ax.iter doax env

    in Format.fprintf fmt "@[<v>%a@]@."(EcPrinting.pp_list "@ " do1) all_path
end

let process_search scope qs =
  let buffer = Buffer.create 0 in
  let fmt    = Format.formatter_of_buffer buffer in

  Format.fprintf fmt "%a%!"
    (fun fmt (scope, qs) -> Search.search fmt scope qs)
    (scope, qs);
  EcScope.notify scope `Info "%s" (Buffer.contents buffer)

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
    { od_name    = "operators or predicates";
      od_lookup  = EcEnv.Op.all (fun _ -> true) ;
      od_printer = 
        fun ppe fmt l ->
          let long = l <> [] in
          Format.fprintf fmt "@[<v>%a@]"
            (EcPrinting.pp_list "@ " (EcPrinting.pp_opdecl ~long ppe)) l; }

  let pr_op = pr_gen pr_op_r

  (* ------------------------------------------------------------------ *)
  let pr_th_r =
    { od_name    = "theories";
      od_lookup  = EcEnv.Theory.lookup;
      od_printer = EcPrinting.pp_theory; }

  let pr_th = pr_gen pr_th_r

  (* ------------------------------------------------------------------ *)
  let pr_ax_r =
    { od_name    = "lemmas or axioms";
      od_lookup  = EcEnv.Ax.lookup;
      od_printer = EcPrinting.pp_axiom; }

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
      Mx.iter (fun xp _ ->
        let pv = EcTypes.pv_glob xp in
        let ty = EcEnv.Var.by_xpath xp env in
        Format.fprintf fmt "  @[%a : %a@]@."
          (EcPrinting.pp_pv ppe) pv
          (EcPrinting.pp_type ppe) ty.EcEnv.vb_type)
        us.EcEnv.us_pv
  end

  | Pr_goal n -> begin
      match EcScope.xgoal scope with
      | None | Some { EcScope.puc_active = None} ->
          EcScope.hierror "no active proof"

      | Some { EcScope.puc_active = Some puc } -> begin
          match puc.EcScope.puc_jdg with
          | EcScope.PSNoCheck -> ()

          | EcScope.PSCheck pf -> begin
              let hds = EcCoreGoal.all_opened pf in
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
              EcPrinting.pp_goal ppe fmt (sz, goal)
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
  let mode = if (!pragma).pm_check then `Check else `WeakCheck in
  let scope = EcScope.Ty.add_instance scope mode tci in
    scope

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
and process_axiom (scope : EcScope.scope) (ax : paxiom located) =
  EcScope.check_state `InTop "axiom" scope;
  let mode = if (!pragma).pm_check then `Check else `WeakCheck in
  let (name, scope) = EcScope.Ax.add scope mode ax in
    name |> EcUtils.oiter
      (fun x ->
         match (unloc ax).pa_kind with
         | PAxiom _ -> EcScope.notify scope `Info "added axiom: `%s'" x
         | _        -> EcScope.notify scope `Info "added lemma: `%s'" x);
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
and process_sct_open (scope : EcScope.scope) name =
  EcScope.check_state `InTop "section opening" scope;
  EcScope.Section.enter scope name

(* -------------------------------------------------------------------- *)
and process_sct_close (scope : EcScope.scope) name =
  EcScope.check_state `InTop "section closing" scope;
  EcScope.Section.exit scope name

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
  let check mode =
    match EcScope.goal scope with
    | Some { EcScope.puc_mode = Some false } ->
        EcScope.hierror "pragma [check|nocheck] in non-strict proof script";
    | _ -> pragma_check mode
  in

  match unloc opt with
  | "silent"  -> pragma_verbose false
  | "verbose" -> pragma_verbose true
  | "nocheck" -> check false
  | "check"   -> check true
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
      | GsctOpen     name -> `Fct   (fun scope -> process_sct_open   scope  name)
      | GsctClose    name -> `Fct   (fun scope -> process_sct_close  scope  name)
      | GthW3        a    -> `Fct   (fun scope -> process_w3_import  scope  a)
      | Gprint       p    -> `Fct   (fun scope -> process_print      scope  p; scope)
      | Gsearch      qs   -> `Fct   (fun scope -> process_search     scope qs ; scope)
      | Gtactics     t    -> `Fct   (fun scope -> process_tactics    scope  t)
      | Grealize     p    -> `Fct   (fun scope -> process_realize    scope  p)
      | Gprover_info pi   -> `Fct   (fun scope -> process_proverinfo scope  pi)
      | Gsave        loc  -> `Fct   (fun scope -> process_save       scope  loc)
      | Gpragma      opt  -> `State (fun scope -> process_pragma     scope  opt)
      | Goption      opt  -> `Fct   (fun scope -> process_option     scope  opt)
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
  let scope   =
    if   boot
    then scope
    else
      List.fold_left
        (fun scope th -> process_th_require loader scope th)
        scope [prelude]
  in

  let scope = EcScope.Prover.set_wrapper scope wrapper in
  let scope = EcScope.Prover.set_default scope poptions in
  let scope = if checkall then EcScope.Prover.full_check scope else scope in

  scope

(* -------------------------------------------------------------------- *)
type context = {
  ct_level   : int;
  ct_current : EcScope.scope;
  ct_root    : EcScope.scope;
  ct_stack   : EcScope.scope list;
}

let context = ref (None : context option)

let rootctxt (scope : EcScope.scope) =
  { ct_level = 0; ct_current = scope; ct_root = scope; ct_stack = []; }

(* -------------------------------------------------------------------- *)
let pop_context context =
  assert (not (List.isempty context.ct_stack));

  { ct_level   = context.ct_level - 1;
    ct_root    = context.ct_root;
    ct_current = List.hd context.ct_stack;
    ct_stack   = List.tl context.ct_stack; }

(* -------------------------------------------------------------------- *)
let push_context scope context =
  { ct_level   = context.ct_level + 1;
    ct_root    = context.ct_root;
    ct_current = scope;
    ct_stack   = context.ct_current :: context.ct_stack; }

(* -------------------------------------------------------------------- *)
let initialize ~boot ~checkmode =
  assert (!context = None);
  context := Some (rootctxt (initial ~checkmode ~boot))

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
  | true  -> "check"
  | false -> "nocheck"

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

let pp_current_goal stream =
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
