(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypedtree
open EcPrinting
open Pprint.Operators

(* -------------------------------------------------------------------- *)
let loader = EcLoader.create ()

(* -------------------------------------------------------------------- *)
let addidir (idir : string) =
  EcLoader.addidir idir loader

(* -------------------------------------------------------------------- *)
exception Interrupted

let process_pr scope p = 
  let env = EcScope.env scope in
  match p with 
  | Pr_ty qs ->
      let (x, ty) = EcEnv.Ty.lookup qs.pl_desc env in
      EcPP.pr_typedecl (EcPP.mono env) (x, ty)
        
  | Pr_op qs | Pr_pr qs ->
      let (x, op) = EcEnv.Op.lookup qs.pl_desc env in
      EcPP.pr_opdecl (EcPP.mono env) (x, op)
        
  | Pr_th qs ->
      let (p, th) = EcEnv.Theory.lookup qs.pl_desc env in
      EcPP.pr_theory (EcPP.mono env) (p, th)
  | Pr_ax qs ->
      let (p, ax) = EcEnv.Ax.lookup qs.pl_desc env in
      EcPP.pr_axiom (EcPP.mono env) (p, ax)

let process_print scope p = 
  let doc = process_pr scope p in
  EcPrinting.pretty (doc ^^ Pprint.hardline)

let out_added scope p = 
  let doc = process_pr scope p in
  EcPrinting.pretty (!^"add " ^^ doc ^^ Pprint.hardline)

let print_next scope = 
  EcPrinting.pretty (EcScope.Tactic.out_goal scope);
  EcPrinting.pretty (Pprint.empty ^/^ !^">") 
(* -------------------------------------------------------------------- *)
let rec process_type (scope : EcScope.scope) (tyd : ptydecl) =
  let tyname = (tyd.pty_tyvars, tyd.pty_name) in
  let scope = 
    match tyd.pty_body with
    | None    -> EcScope.Ty.add    scope tyname
    | Some bd -> EcScope.Ty.define scope tyname bd in
  out_added scope (Pr_ty (dummy_pqs_of_ps tyd.pty_name));
  scope
  
(* -------------------------------------------------------------------- *)
and process_module (scope : EcScope.scope) ((x, m) : _ * pmodule_expr) =
  EcScope.Mod.add scope x.pl_desc m

(* -------------------------------------------------------------------- *)
and process_interface (scope : EcScope.scope) ((x, i) : _ * pmodule_type) =
  EcScope.ModType.add scope x.pl_desc i

(* -------------------------------------------------------------------- *)
and process_operator (scope : EcScope.scope) (op : poperator) =
  let scope = EcScope.Op.add scope op in
  out_added scope (Pr_op (dummy_pqs_of_ps op.po_name));
  scope
  

(* -------------------------------------------------------------------- *)
and process_predicate (scope : EcScope.scope) (p : ppredicate) =
  let scope = EcScope.Pred.add scope p in
  out_added scope (Pr_pr (dummy_pqs_of_ps p.pp_name));
  scope

(* -------------------------------------------------------------------- *)
and process_axiom (scope : EcScope.scope) (ax : paxiom) =
  let name, scope = EcScope.Ax.add scope ax in
  begin match name with
  | None -> ()
  | Some name -> out_added scope (Pr_ax (dummy_pqs_of_ps (dummyloc name)))
  end;
  scope

(* -------------------------------------------------------------------- *)
and process_claim (scope : EcScope.scope) _ =
  scope

(* -------------------------------------------------------------------- *)
and process_th_open (scope : EcScope.scope) name =
  EcScope.Theory.enter scope name

(* -------------------------------------------------------------------- *)
and process_th_close (scope : EcScope.scope) name =
  if EcIdent.name (EcScope.name scope) <> name then
    failwith "invalid theory name";     (* FIXME *)
  snd (EcScope.Theory.exit scope)

(* -------------------------------------------------------------------- *)
and process_th_require (scope : EcScope.scope) (x,io) = 
  let name = x.pl_desc in
  match EcLoader.locate name loader with
  | None -> failwith ("cannot locate: " ^ name)
  | Some filename ->
      let loader iscope =
        let commands = EcIo.parseall (EcIo.from_file filename) in
          List.fold_left process iscope commands in 
      let scope = EcScope.Theory.require scope name loader in
      match io with
      | None -> scope
      | Some true -> process_th_export scope ([],name)
      | Some false -> process_th_import scope ([],name)

(* -------------------------------------------------------------------- *)
and process_th_import (scope : EcScope.scope) name =
  EcScope.Theory.import scope name

(* -------------------------------------------------------------------- *)
and process_th_export (scope : EcScope.scope) name =
  EcScope.Theory.export scope name

(* -------------------------------------------------------------------- *)
and process_th_clone (scope : EcScope.scope) thcl =
  EcScope.Theory.clone scope thcl

(* -------------------------------------------------------------------- *)
and process_w3_import (scope : EcScope.scope) (p, f, r) =
  EcScope.Theory.import_w3 scope p f r

(* -------------------------------------------------------------------- *)
and process_tactics (scope : EcScope.scope) t = 
  EcScope.Tactic.process scope t 

(* -------------------------------------------------------------------- *)
and process_save (scope : EcScope.scope) =
  let name, scope = EcScope.Ax.save scope in
  out_added scope (Pr_ax (dummy_pqs_of_ps (dummyloc name)));
  scope

(* -------------------------------------------------------------------- *)
and process (scope : EcScope.scope) (g : global) =
  let scope =
    match g with
    | Gtype      t    -> process_type       scope t
    | Gmodule    m    -> process_module     scope m
    | Ginterface i    -> process_interface  scope i
    | Goperator  o    -> process_operator   scope o
    | Gpredicate p    -> process_predicate  scope p
    | Gaxiom     a    -> process_axiom      scope a
    | Gclaim     c    -> process_claim      scope c
    | GthOpen    name -> process_th_open    scope name.pl_desc
    | GthClose   name -> process_th_close   scope name.pl_desc
    | GthRequire name -> process_th_require scope name
    | GthImport  name -> process_th_import  scope name.pl_desc
    | GthExport  name -> process_th_export  scope name.pl_desc
    | GthClone   thcl -> process_th_clone   scope thcl
    | GthW3      a    -> process_w3_import  scope a
    | Gprint     p    -> process_print      scope p; scope
    | Gtactics   t    -> process_tactics    scope t
    | Gsave           -> process_save       scope 
  in
  print_next scope;
(*   EcEnv.dump EcDebug.initial (EcScope.env scope);  *)
  scope

(* -------------------------------------------------------------------- *)
let scope = ref EcScope.empty

(* -------------------------------------------------------------------- *)
let process (g : global) =
  scope := process !scope g

(* -------------------------------------------------------------------- *)
let process (g : global) =
  try
    process g
  with
  | TyError (loc, exn) -> 
      EcFormat.pp_err
        (EcPrinting.pp_located loc EcPexception.pp_typerror)
        exn;
      raise Interrupted
  | e -> EcFormat.pp_err EcPexception.exn_printer e; raise e
