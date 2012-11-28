(* -------------------------------------------------------------------- *)
open Parsetree

(* -------------------------------------------------------------------- *)
let process_type (scope : Scope.scope) ((args, x), ty) =
  match args, ty with
  | [], None   -> Scope.Ty.add scope x
  | _ , _      -> assert false

(* -------------------------------------------------------------------- *)
let process_module (scope : Scope.scope) ((x, m) : _ * pmodule_expr) =
  scope

(* -------------------------------------------------------------------- *)
let process_interface (scope : Scope.scope) _ =
  scope

(* -------------------------------------------------------------------- *)
let process_operator (scope : Scope.scope) (op : poperator) =
  Scope.Op.add scope op

(* -------------------------------------------------------------------- *)
let process_axiom (scope : Scope.scope) _ =
  scope

(* -------------------------------------------------------------------- *)
let process_claim (scope : Scope.scope) _ =
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
      | Some _ -> failwith "already in a opened theory"
      | None   -> scope := Some (Scope.initial name)
  end

  | GthClose name -> begin
    if Scope.name (get_scope ()) <> name then
      failwith "invalid theory name";
    scope := None
  end

  | Gtype      t -> scope := Some (process_type      (get_scope ()) t)
  | Gmodule    m -> scope := Some (process_module    (get_scope ()) m)
  | Ginterface i -> scope := Some (process_interface (get_scope ()) i)
  | Goperator  o -> scope := Some (process_operator  (get_scope ()) o)
  | Gaxiom     a -> scope := Some (process_axiom     (get_scope ()) a)
  | Gclaim     c -> scope := Some (process_claim     (get_scope ()) c)
