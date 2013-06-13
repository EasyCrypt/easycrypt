(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcLocation
open EcParsetree
open EcTyping
open EcOptions
open EcLogic

(* -------------------------------------------------------------------- *)
type pragma = {
  pm_verbose : bool; (* true => display goal after each command *)
}

let pragma = ref { pm_verbose = true; }

(* -------------------------------------------------------------------- *)
exception TopError of EcLocation.t * exn

let rec toperror_of_exn ?gloc exn =
  match exn with
  | TyError  (loc, _, _) -> Some (loc, exn)
  | TacError _           -> Some (odfl _dummy gloc, exn)
  | ParseError (loc, _)  -> Some (loc, exn)

  | LocError (loc, e)    -> begin
      let gloc =
        if loc == EcLocation._dummy then gloc else Some loc
      in
      match toperror_of_exn ?gloc e with
      | None -> Some (loc, e)
      | Some (loc, e) -> Some (loc, e)
    end

  | TopError (loc, e) ->
      let gloc =  if loc == EcLocation._dummy then gloc else Some loc in
        Some (odfl _dummy gloc, e)

  | EcScope.HiScopeError (loc, msg) ->
      let gloc = odfl _dummy loc in
        Some (gloc, EcScope.HiScopeError (None, msg))

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
          EcPrinting.pp_typedecl ppe fmt (x, ty)
        
  | Pr_op qs | Pr_pr qs ->
      let (x, op) = EcEnv.Op.lookup qs.pl_desc env in
        EcPrinting.pp_opdecl ppe fmt (x, op)
        
  | Pr_th qs ->
      let (p, th) = EcEnv.Theory.lookup qs.pl_desc env in
        EcPrinting.pp_theory ppe fmt (p, th)

  | Pr_ax qs ->
      let (p, ax) = EcEnv.Ax.lookup qs.pl_desc env in
        EcPrinting.pp_axiom ppe fmt (p, ax)

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
    | None    -> EcScope.Ty.add    scope (mk_loc tyd.pl_loc tyname)
    | Some bd -> EcScope.Ty.define scope (mk_loc tyd.pl_loc tyname) bd
  in
    notify scope "added type: `%s'" (unloc tyd.pl_desc.pty_name);
    scope
  
(* -------------------------------------------------------------------- *)
and process_datatype (_scope : EcScope.scope) _ =
  failwith "not-implemented-yet"

(* -------------------------------------------------------------------- *)
and process_module (scope : EcScope.scope) (x, m) =
  EcScope.check_state `InTop "module" scope;
  EcScope.Mod.add scope x.pl_desc m

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
  let (name, scope) = EcScope.Ax.add scope ax in
    EcUtils.oiter name
      (fun x -> notify scope "added axiom: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_claim (scope : EcScope.scope) _ =
  scope

(* -------------------------------------------------------------------- *)
and process_th_open (scope : EcScope.scope) name =
  EcScope.check_state `InTop "theory" scope;
  EcScope.Theory.enter scope name

(* -------------------------------------------------------------------- *)
and process_th_close (scope : EcScope.scope) name =
  EcScope.check_state `InTop "theory closing" scope;
  if (EcScope.name scope) <> name then
    failwith "invalid theory name";     (* FIXME *)
  snd (EcScope.Theory.exit scope)

(* -------------------------------------------------------------------- *)
and process_th_require ld scope (x, io) = 
  EcScope.check_state `InTop "theory require" scope;

  let name  = x.pl_desc in
    match EcLoader.locate name ld with
    | None ->
        failwith ("cannot locate: " ^ name) (* FIXME *)

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
          | None       -> scope
          | Some true  -> process_th_export scope ([], name)
          | Some false -> process_th_import scope ([], name)

(* -------------------------------------------------------------------- *)
and process_th_import (scope : EcScope.scope) name =
  EcScope.check_state `InTop "theory import" scope;
  EcScope.Theory.import scope name

(* -------------------------------------------------------------------- *)
and process_th_export (scope : EcScope.scope) name =
  EcScope.check_state `InTop "theory export" scope;
  EcScope.Theory.export scope name

(* -------------------------------------------------------------------- *)
and process_th_clone (scope : EcScope.scope) thcl =
  EcScope.check_state `InTop "theory cloning" scope;
  EcScope.Theory.clone scope thcl

(* -------------------------------------------------------------------- *)
and process_w3_import (scope : EcScope.scope) (p, f, r) =
  EcScope.check_state `InTop "why3 import" scope;
  EcScope.Theory.import_w3 scope p f r

(* -------------------------------------------------------------------- *)
and process_tactics (scope : EcScope.scope) t = 
  match t with
  | `Actual t -> EcScope.Tactics.process scope t
  | `Proof    -> scope (* FIXME: check that we are at the beginning of proof script*)

(* -------------------------------------------------------------------- *)
and process_save (scope : EcScope.scope) loc =
  let (name, scope) = EcScope.Ax.save scope loc in
    EcUtils.oiter name
      (fun x -> notify scope "added axiom: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_proverinfo scope pi = 
  let scope = EcScope.Prover.process scope pi in
    scope

(* -------------------------------------------------------------------- *)
and process_checkproof scope b = 
  let scope = EcScope.Prover.check_proof scope b in
    scope

(* -------------------------------------------------------------------- *)
and process_pragma (scope : EcScope.scope) opt =
  begin
    match unloc opt with
    | "silent"  -> pragma := { !pragma with pm_verbose = false }
    | "verbose" -> pragma := { !pragma with pm_verbose = true  }
    | _         -> ()
  end; scope

(* -------------------------------------------------------------------- *)
and process (ld : EcLoader.ecloader) (scope : EcScope.scope) g =
  let loc = g.pl_loc in

  let scope =
    match g.pl_desc with
    | Gtype      t    -> process_type       scope  (mk_loc loc t)
    | Gdatatype  t    -> process_datatype   scope  (mk_loc loc t)
    | Gmodule    m    -> process_module     scope  m
    | Ginterface i    -> process_interface  scope  i
    | Goperator  o    -> process_operator   scope  (mk_loc loc o)
    | Gpredicate p    -> process_predicate  scope  (mk_loc loc p)
    | Gaxiom     a    -> process_axiom      scope  (mk_loc loc a)
    | Gclaim     c    -> process_claim      scope  c
    | GthOpen    name -> process_th_open    scope  name.pl_desc
    | GthClose   name -> process_th_close   scope  name.pl_desc
    | GthRequire name -> process_th_require ld scope name
    | GthImport  name -> process_th_import  scope  name.pl_desc
    | GthExport  name -> process_th_export  scope  name.pl_desc
    | GthClone   thcl -> process_th_clone   scope  thcl
    | GthW3      a    -> process_w3_import  scope  a
    | Gprint     p    -> process_print      scope  p; scope
    | Gtactics   t    -> process_tactics    scope  t
    | Gprover_info pi -> process_proverinfo scope  pi
    | Gcheckproof b   -> process_checkproof scope  b
    | Gsave      loc  -> process_save       scope  loc
    | Gpragma    opt  -> process_pragma     scope opt
  in
    begin
      try
        ignore (Sys.getenv "ECDEBUG");
        EcEnv.dump EcDebug.initial (EcScope.env scope)
      with Not_found -> ()
    end;
    scope

(* -------------------------------------------------------------------- *)
and process_internal ld scope g =
  process ld scope g

(* -------------------------------------------------------------------- *)
let loader  = EcLoader.create ()

let addidir (idir : string) =
  EcLoader.addidir idir loader

(* -------------------------------------------------------------------- *)
let context = ref (0, EcScope.empty, [])

(* -------------------------------------------------------------------- *)
let current () =
  let (_, scope, _) = !context in scope

(* -------------------------------------------------------------------- *)
let full_check b max_provers provers =
  let (idx,scope,l) = !context in
  assert (idx = 0 && l = []);  
  let scope = EcScope.Prover.set_default scope max_provers provers in
  let scope = 
    if b then EcScope.Prover.full_check scope 
    else scope in
  context := (idx, scope, l)

(* -------------------------------------------------------------------- *)
let uuid () : int =
  let (idx, _, _) = !context in idx

(* -------------------------------------------------------------------- *)
let undo (olduuid : int) =
  if olduuid < (uuid ()) then
    begin
      for i = (uuid ()) - 1 downto olduuid do
        let (_, _scope, stack) = !context in
        context := (i, List.hd stack, List.tl stack)
      done
    end

(* -------------------------------------------------------------------- *)
let process (g : global located) =
  let (idx, scope, stack) = !context in
  let newscope = process loader scope g in
    context := (idx+1, newscope, scope :: stack)

(* -------------------------------------------------------------------- *)
module S = EcScope
module L = EcBaseLogic

let pp_current_goal stream =
  let (_, scope, _) = !context in

  match S.goal scope with
  | None -> ()

  | Some goal -> begin
      let juc, ns = goal.S.puc_jdg in
      let ppe = EcPrinting.PPEnv.ofenv (S.env scope) in

      match List.ohead ns with
      | None   -> Format.fprintf stream "No more goals\n%!"
      | Some n -> EcPrinting.pp_goal ppe stream (List.length ns, get_goal (juc, n))
  end

let pp_maybe_current_goal stream =
  match (!pragma).pm_verbose with
  | true  -> pp_current_goal stream
  | false -> ()
