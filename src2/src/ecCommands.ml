(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypedtree

(* -------------------------------------------------------------------- *)
exception Interrupted

(* -------------------------------------------------------------------- *)
let process_type (scope : EcScope.scope) (tyd : ptydecl) =
  let tyname = (tyd.pty_tyvars, tyd.pty_name) in
    match tyd.pty_body with
    | None    -> EcScope.Ty.add    scope tyname
    | Some bd -> EcScope.Ty.define scope tyname bd

(* -------------------------------------------------------------------- *)
let process_module (scope : EcScope.scope) ((x, m) : _ * pmodule_expr) =
  EcScope.Mod.add scope x m

(* -------------------------------------------------------------------- *)
let process_interface (scope : EcScope.scope) ((x, i) : _ * pmodule_type) =
  EcScope.ModType.add scope x i

(* -------------------------------------------------------------------- *)
let process_operator (scope : EcScope.scope) (op : poperator) =
  EcScope.Op.add scope op

(* -------------------------------------------------------------------- *)
let process_axiom (scope : EcScope.scope) (ax : paxiom) =
  EcScope.Ax.add scope ax

(* -------------------------------------------------------------------- *)
let process_claim (scope : EcScope.scope) _ =
  scope

(* -------------------------------------------------------------------- *)
let process_th_open (scope : EcScope.scope) name =
  EcScope.Theory.enter scope name

(* -------------------------------------------------------------------- *)
let process_th_close (scope : EcScope.scope) name =
  if EcIdent.name (EcScope.name scope) <> name then
    failwith "invalid theory name";     (* FIXME *)
  snd (EcScope.Theory.exit scope)

(* -------------------------------------------------------------------- *)
let process_th_require (scope : EcScope.scope) name =
  scope

(* -------------------------------------------------------------------- *)
let process_th_import (scope : EcScope.scope) name =
  EcScope.Theory.import scope name

(* -------------------------------------------------------------------- *)
let scope = ref (EcScope.initial EcCoreLib.top)

let process (g : global) =
  match g with
  | Gtype      t    -> scope := (process_type       !scope t)
  | Gmodule    m    -> scope := (process_module     !scope m)
  | Ginterface i    -> scope := (process_interface  !scope i)
  | Goperator  o    -> scope := (process_operator   !scope o)
  | Gaxiom     a    -> scope := (process_axiom      !scope a)
  | Gclaim     c    -> scope := (process_claim      !scope c)
  | GthOpen    name -> scope := (process_th_open    !scope name)
  | GthClose   name -> scope := (process_th_close   !scope name)
  | GthRequire name -> scope := (process_th_require !scope name)
  | GthImport  name -> scope := (process_th_import  !scope name)

let process (g : global) =
  try
    process g
  with
  | TyError (loc, exn) -> begin
      EcPrinting.err
        (EcPrinting.pp_located loc EcPrinting.pp_typerror)
        exn;
      raise Interrupted
  end
    
