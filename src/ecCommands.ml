(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcTypedtree
open EcOptions
open EcPrinting
open Pprint.Operators

(* -------------------------------------------------------------------- *)
type info =
| GI_AddedType      of symbol
| GI_AddedAxiom     of symbol
| GI_AddedOperator  of symbol
| GI_AddedPredicate of symbol

(* -------------------------------------------------------------------- *)
let loader = EcLoader.create ()

(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
let addidir (idir : string) =
  EcLoader.addidir idir loader

(* -------------------------------------------------------------------- *)
let rec process_type (scope : EcScope.scope) (tyd : ptydecl) =
  let tyname = (tyd.pty_tyvars, tyd.pty_name) in
  let scope = 
    match tyd.pty_body with
    | None    -> EcScope.Ty.add    scope tyname
    | Some bd -> EcScope.Ty.define scope tyname bd
  in
    (scope, [GI_AddedType (unloc tyd.pty_name)])
  
(* -------------------------------------------------------------------- *)
and process_module (scope : EcScope.scope) (x, m) =
  (EcScope.Mod.add scope x.pl_desc m, [])

(* -------------------------------------------------------------------- *)
and process_interface (scope : EcScope.scope) (x, i) =
  (EcScope.ModType.add scope x.pl_desc i, [])

(* -------------------------------------------------------------------- *)
and process_operator (scope : EcScope.scope) (op : poperator) =
  let scope = EcScope.Op.add scope op in
    (scope, [GI_AddedOperator (unloc op.po_name)])

(* -------------------------------------------------------------------- *)
and process_predicate (scope : EcScope.scope) (p : ppredicate) =
  let scope = EcScope.Pred.add scope p in
    (scope, [GI_AddedPredicate (unloc p.pp_name)])

(* -------------------------------------------------------------------- *)
and process_axiom (scope : EcScope.scope) (ax : paxiom) =
  let (name, scope) = EcScope.Ax.add scope ax in
  let info = EcUtils.omap name (fun x -> GI_AddedAxiom x)
  in
    (scope, EcUtils.otolist info)

(* -------------------------------------------------------------------- *)
and process_claim (scope : EcScope.scope) _ =
  (scope, [])

(* -------------------------------------------------------------------- *)
and process_th_open (scope : EcScope.scope) name =
  (EcScope.Theory.enter scope name, [])

(* -------------------------------------------------------------------- *)
and process_th_close (scope : EcScope.scope) name =
  if EcIdent.name (EcScope.name scope) <> name then
    failwith "invalid theory name";     (* FIXME *)
  (snd (EcScope.Theory.exit scope), [])

(* -------------------------------------------------------------------- *)
and process_th_require (scope : EcScope.scope) (x,io) = 
  let name  = x.pl_desc in
    match EcLoader.locate name loader with
    | None ->
        failwith ("cannot locate: " ^ name) (* FIXME *)

    | Some filename ->
        let loader iscope =
          let commands = EcIo.parseall (EcIo.from_file filename) in
            List.fold_left process_internal iscope commands in 
        let scope = EcScope.Theory.require scope name loader in
          match io with
          | None       -> (scope, [])
          | Some true  -> process_th_export scope ([], name)
          | Some false -> process_th_import scope ([], name)

(* -------------------------------------------------------------------- *)
and process_th_import (scope : EcScope.scope) name =
  (EcScope.Theory.import scope name, [])

(* -------------------------------------------------------------------- *)
and process_th_export (scope : EcScope.scope) name =
  (EcScope.Theory.export scope name, [])

(* -------------------------------------------------------------------- *)
and process_th_clone (scope : EcScope.scope) thcl =
  (EcScope.Theory.clone scope thcl, [])

(* -------------------------------------------------------------------- *)
and process_w3_import (scope : EcScope.scope) (p, f, r) =
  (EcScope.Theory.import_w3 scope p f r, [])

(* -------------------------------------------------------------------- *)
and process_tactics (scope : EcScope.scope) t = 
  (EcScope.Tactic.process scope t, [])

(* -------------------------------------------------------------------- *)
and process_save (scope : EcScope.scope) loc =
  let name, scope = EcScope.Ax.save scope loc in
  let gi = EcUtils.odfl [] (EcUtils.omap name (fun n -> [GI_AddedAxiom n])) in
    (scope, gi)

(* -------------------------------------------------------------------- *)
and process_proverinfo scope pi = 
  let scope = EcScope.Prover.process scope pi in
  (scope, [])

(* -------------------------------------------------------------------- *)
and process_checkproof scope b = 
  let scope = EcScope.Prover.check_proof scope b in
  (scope, [])
(* -------------------------------------------------------------------- *)
and process (scope : EcScope.scope) (g : global) =
  let (scope, infos) =
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
    | Gprint     p    -> process_print      scope p; (scope, [])
    | Gtactics   t    -> process_tactics    scope t
    | Gprover_info pi -> process_proverinfo scope pi
    | Gcheckproof b   -> process_checkproof scope b
    | Gsave      loc  -> process_save       scope loc
  in
    (scope, infos)

(* -------------------------------------------------------------------- *)
and process_internal (scope : EcScope.scope) (g : global) =
  fst (process scope g)

(* -------------------------------------------------------------------- *)
let context = ref (0, EcScope.empty, [])

let full_check b = 
  let (idx,scope,l) = !context in
  assert (idx = 0 && l = []);  
  let scope = EcScope.Prover.set_default scope in
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
    for i = (uuid ()) - 1 downto olduuid do
      let (_, _scope, stack) = !context in
        context := (i, List.hd stack, List.tl stack)
    done

(* -------------------------------------------------------------------- *)
let process (g : global) =
  let (idx, scope, stack) = !context in
  let (newscope, infos) = process scope g in
    context := (idx+1, newscope, scope :: stack);
    infos

(* -------------------------------------------------------------------- *)


