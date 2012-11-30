(* -------------------------------------------------------------------- *)
open EcParsetree

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
let process_axiom (scope : EcScope.scope) _ =
  scope

(* -------------------------------------------------------------------- *)
let process_claim (scope : EcScope.scope) _ =
  scope

(* -------------------------------------------------------------------- *)
let scope = ref None

let get_scope () =
  match !scope with
  | None       -> failwith "not in a theory"
  | Some scope -> scope

let process (g : global) =
  match g with
  | GthOpen name -> begin
      match !scope with
      | Some _ -> failwith "already in an opened theory"
      | None   -> scope := Some (EcScope.initial name)
  end

  | GthClose name -> begin
    if EcScope.name (get_scope ()) <> name then
      failwith "invalid theory name";
    scope := None
  end

  | Gtype      t -> scope := Some (process_type      (get_scope ()) t)
  | Gmodule    m -> scope := Some (process_module    (get_scope ()) m)
  | Ginterface i -> scope := Some (process_interface (get_scope ()) i)
  | Goperator  o -> scope := Some (process_operator  (get_scope ()) o)
  | Gaxiom     a -> scope := Some (process_axiom     (get_scope ()) a)
  | Gclaim     c -> scope := Some (process_claim     (get_scope ()) c)
