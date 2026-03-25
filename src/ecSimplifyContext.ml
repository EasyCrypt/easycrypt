(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath

(* -------------------------------------------------------------------- *)
type entry = path * EcTheory.rule

(* A head filter restricts user-reduction rules to (or away from) those
   whose left-hand side is headed by one of the given symbols. *)
type head_mode = [`Include | `Exclude]
type head_filter = [`Include of Sp.t | `Exclude of Sp.t]

(* Canonical name of the default simplify database. A database is named
   by a [symbol]; the default one carries the empty name. This is the
   single source for that name, re-exported as [EcEnv.Reduction.dname]. *)
let dname : symbol = ""

(* -------------------------------------------------------------------- *)
type simplify_context = {
  (* Names of the databases currently active for a bare [simplify]/[cbv]
     (always contains [dname]). *)
  ls_active     : Ssym.t;
  (* Proof-local default databases consulted by later bare [simplify]/
     [cbv] calls: [None] = no local default (fall back to [ls_active]),
     [Some dbs] = use exactly [dbs]. *)
  ls_default_db : symbol list option;
  (* Proof-local default head filter, similarly overriding the absence of
     an explicit filter on [simplify]/[cbv]. *)
  ls_default_hd : head_filter option;
  (* Per-database overlay of locally added rules (add-only). *)
  ls_added      : entry list Msym.t;
}

(* -------------------------------------------------------------------- *)
let empty : simplify_context = {
  ls_active     = Ssym.singleton dname;
  ls_default_db = None;
  ls_default_hd = None;
  ls_added      = Msym.empty;
}

(* -------------------------------------------------------------------- *)
let active (ls : simplify_context) : Ssym.t =
  ls.ls_active

(* -------------------------------------------------------------------- *)
let default_db (ls : simplify_context) : symbol list option =
  ls.ls_default_db

(* -------------------------------------------------------------------- *)
let default_hd (ls : simplify_context) : head_filter option =
  ls.ls_default_hd

(* -------------------------------------------------------------------- *)
(* [None] denotes the default database. *)
let normbase (base : symbol option) : symbol =
  odfl dname base

(* -------------------------------------------------------------------- *)
let activate (bases : symbol list) (ls : simplify_context) : simplify_context =
  { ls with ls_active = List.fold_left (fun st b -> Ssym.add b st) ls.ls_active bases }

(* -------------------------------------------------------------------- *)
let deactivate (bases : symbol list) (ls : simplify_context) : simplify_context =
  { ls with ls_active = List.fold_left (fun st b -> Ssym.remove b st) ls.ls_active bases }

(* -------------------------------------------------------------------- *)
let set_default_db (bases : symbol list) (ls : simplify_context) : simplify_context =
  { ls with ls_default_db = Some bases }

(* -------------------------------------------------------------------- *)
let set_default_hd
  (hd : (head_mode * path list) option)
  (ls : simplify_context)
  : simplify_context
=
  let hd = hd |> omap (fun (mode, paths) ->
    match mode with
    | `Include -> `Include (Sp.of_list paths)
    | `Exclude -> `Exclude (Sp.of_list paths))
  in
  { ls with ls_default_hd = hd }

(* -------------------------------------------------------------------- *)
let clear_default (ls : simplify_context) : simplify_context =
  { ls with ls_default_db = None; ls_default_hd = None }

(* -------------------------------------------------------------------- *)
let added ?(base : symbol option) (ls : simplify_context) : entry list =
  Msym.find_def [] (normbase base) ls.ls_added

(* -------------------------------------------------------------------- *)
let add_rules
  ?(base  : symbol option)
   (rules : entry list)
   (ls    : simplify_context)
  : simplify_context
=
  let base = normbase base in
  let old = Msym.find_def [] base ls.ls_added in
  let old =
    List.filter (fun (p, _) ->
      not (List.exists (fun (p', _) -> EcPath.p_equal p p') rules))
      old
  in
  { ls with ls_added = Msym.add base (old @ rules) ls.ls_added }

(* -------------------------------------------------------------------- *)
let clear ?(base : symbol option) (ls : simplify_context) : simplify_context =
  let base = normbase base in
  { ls with ls_added = Msym.remove base ls.ls_added }
