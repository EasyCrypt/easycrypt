(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypedtree

(* -------------------------------------------------------------------- *)
let loader = EcLoader.create ()

(* -------------------------------------------------------------------- *)
let addidir (idir : string) =
  EcLoader.addidir idir loader

(* -------------------------------------------------------------------- *)
exception Interrupted

let process_print scope p = 
  let env = EcScope.env scope in
  match p with 
  | Pr_ty qs ->
      (try 
        let ptd = EcEnv.Ty.lookup qs.pl_desc env in
        Format.printf "%a@." (EcPrinting.pp_tydecl env) ptd
      with _ -> assert false (* FIXME *))
  | Pr_op qs ->
      (try 
        let ptd = EcEnv.Op.lookup qs.pl_desc env in
        Format.printf "%a@." EcPrinting.pp_opdecl ptd
      with _ -> assert false (* FIXME *))
  | Pr_th qs -> assert false
  | Pr_pr qs -> assert false
  | Pr_ax qs -> assert false

(* -------------------------------------------------------------------- *)
let rec process_type (scope : EcScope.scope) (tyd : ptydecl) =
  let tyname = (tyd.pty_tyvars, tyd.pty_name) in
    match tyd.pty_body with
    | None    -> EcScope.Ty.add    scope tyname
    | Some bd -> EcScope.Ty.define scope tyname bd

(* -------------------------------------------------------------------- *)
and process_module (scope : EcScope.scope) ((x, m) : _ * pmodule_expr) =
  EcScope.Mod.add scope x.pl_desc m

(* -------------------------------------------------------------------- *)
and process_interface (scope : EcScope.scope) ((x, i) : _ * pmodule_type) =
  EcScope.ModType.add scope x.pl_desc i

(* -------------------------------------------------------------------- *)
and process_operator (scope : EcScope.scope) (op : poperator) =
  EcScope.Op.add scope op

(* -------------------------------------------------------------------- *)
and process_predicate (scope : EcScope.scope) (p : ppredicate) =
  EcScope.Pred.add scope p

(* -------------------------------------------------------------------- *)
and process_axiom (scope : EcScope.scope) (ax : paxiom) =
  EcScope.Ax.add scope ax

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
and process_th_require (scope : EcScope.scope) name =
  match EcLoader.locate name loader with
  | None -> failwith ("Cannot locate: " ^ name)
  | Some filename ->
    (* FIXME: hackish *)
    let commands = EcIo.parseall (EcIo.from_file filename) in
    let scope =
      List.fold_left
        process (EcScope.Theory.enter scope name) commands
    in
      snd (EcScope.Theory.exit scope)

(* -------------------------------------------------------------------- *)
and process_th_import (scope : EcScope.scope) name =
  EcScope.Theory.import scope name

(* -------------------------------------------------------------------- *)
and process_th_export (scope : EcScope.scope) name =
  EcScope.Theory.export scope name

(* -------------------------------------------------------------------- *)
and process (scope : EcScope.scope) (g : global) =
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
  | GthRequire name -> process_th_require scope name.pl_desc
  | GthImport  name -> process_th_import  scope name.pl_desc
  | GthExport  name -> process_th_export  scope name.pl_desc
  | Gprint     p    -> process_print      scope p; scope


(* -------------------------------------------------------------------- *)
let scope = ref (EcScope.initial EcCoreLib.top)

(* -------------------------------------------------------------------- *)
let process (g : global) =
  scope := process !scope g;
  EcFormat.pp_err EcPrinting.pp_env (EcScope.env !scope)

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
  | e -> EcFormat.pp_err EcPexception.pp_exn e; raise e
