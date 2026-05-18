(* -------------------------------------------------------------------- *)
(* Canonical form of [TCIAbstract] witnesses.

   For a [TCIAbstract { support; offset; lift }] there can be multiple
   path encodings reaching the same [(target_class, cumulative_renaming)]
   when the support's TC class has diamond inheritance. The framework
   relies on structural equality of [tcwitness] in many places, so two
   semantically-equivalent encodings being structurally distinct breaks
   downstream reasoning.

   This module builds, for any [tcs : typeclass list] (the TC bounds of
   a carrier), the table of canonical [(offset, lift)] paths reaching
   each [(target_class, renaming)]. The "canonical" path is the
   FIRST-IN-BFS-ORDER encounter, which gives a deterministic choice
   without needing to enumerate all paths.

   Phase A of Stage 2 turns this table into the single source of truth
   for path-encoded witnesses. Construction sites consult it; matching
   /  convertibility sites then need no canonicalisation since structural
   compare on canonical encodings is correct.                            *)

open EcAst
open EcUtils

(* -------------------------------------------------------------------- *)
(* Compose a parent-edge renaming [outer] with the cumulative
   ancestor-to-child renaming [inner]. *)
let compose_renaming
  ~(outer : (EcSymbols.symbol * EcSymbols.symbol) list)
  ~(inner : (EcSymbols.symbol * EcSymbols.symbol) list)
  : (EcSymbols.symbol * EcSymbols.symbol) list
=
  let inner_map = EcMaps.Mstr.of_list inner in
  let from_outer =
    List.map
      (fun (gp_name, p_name) ->
        let c_name = odfl p_name (EcMaps.Mstr.find_opt p_name inner_map) in
        (gp_name, c_name))
      outer in
  let outer_p_names =
    List.fold_left (fun s (_, p) -> EcMaps.Sstr.add p s) EcMaps.Sstr.empty outer in
  let outer_gp_names =
    List.fold_left (fun s (gp, _) -> EcMaps.Sstr.add gp s) EcMaps.Sstr.empty outer in
  let from_inner =
    List.filter_map
      (fun (p_name, c_name) ->
        if EcMaps.Sstr.mem p_name outer_p_names || EcMaps.Sstr.mem p_name outer_gp_names
        then None
        else Some (p_name, c_name))
      inner in
  from_outer @ from_inner

(* -------------------------------------------------------------------- *)
(* Renaming equality (set of pairs, order-insensitive). *)
let ren_equal
  (r1 : (EcSymbols.symbol * EcSymbols.symbol) list)
  (r2 : (EcSymbols.symbol * EcSymbols.symbol) list)
  : bool
=
     List.length r1 = List.length r2
  && List.for_all (fun (a, b) ->
       match List.assoc_opt a r2 with
       | Some b' -> b = b'
       | None -> false) r1

(* -------------------------------------------------------------------- *)
(* Walk a lift path from [start], composing renamings. Returns
   [Some (target_tc, cumulative_renaming)] iff every index in [lift]
   is in range. *)
let walk_path (env : EcEnv.env) (start : typeclass) (lift : int list)
  : (typeclass * (EcSymbols.symbol * EcSymbols.symbol) list) option
=
  let rec aux tc ren = function
    | [] -> Some (tc, ren)
    | i :: rest ->
      let decl = EcEnv.TypeClass.by_path tc.tc_name env in
      match List.nth_opt decl.tc_prts i with
      | None -> None
      | Some (parent, _p_lbl, p_ren) ->
        let subst =
          List.fold_left2
            (fun s (a, _) etyarg -> EcIdent.Mid.add a etyarg s)
            EcIdent.Mid.empty decl.tc_tparams tc.tc_args in
        let parent = EcCoreSubst.Tvar.subst_tc subst parent in
        let ren' = compose_renaming ~outer:p_ren ~inner:ren in
        aux parent ren' rest
  in aux start [] lift

(* -------------------------------------------------------------------- *)
(* Build the canonical-paths table: for each [(target_tc_name, ren)]
   reachable from [tcs], record the [(offset, lift)] of the FIRST
   path encountered in BFS order. Repeat encounters are skipped, so
   each [(target, ren)] gets exactly one canonical encoding.            *)
type canon_key = EcPath.path * (EcSymbols.symbol * EcSymbols.symbol) list
type canon_path = int * int list
type canon_table = (canon_key * canon_path) list

let canonical_table
  (env : EcEnv.env)
  (tcs : typeclass list)
  : canon_table
=
  let recorded = ref [] in
  let already ((target_path, ren) : canon_key) =
    List.exists
      (fun ((p, r), _) -> EcPath.p_equal p target_path && ren_equal r ren)
      !recorded in
  let record (target_path : EcPath.path) (ren : _) (offset : int) (lift : int list) =
    let key = (target_path, ren) in
    if not (already key) then
      recorded := (key, (offset, lift)) :: !recorded in
  let rec bfs frontier =
    match frontier with
    | [] -> ()
    | (tc, ren, offset, rev_lift) :: rest ->
      record tc.tc_name ren offset (List.rev rev_lift);
      let decl = EcEnv.TypeClass.by_path tc.tc_name env in
      let subst =
        List.fold_left2
          (fun s (a, _) etyarg -> EcIdent.Mid.add a etyarg s)
          EcIdent.Mid.empty decl.tc_tparams tc.tc_args in
      let next =
        List.mapi
          (fun i (parent, _p_lbl, p_ren) ->
            let parent = EcCoreSubst.Tvar.subst_tc subst parent in
            let ren' = compose_renaming ~outer:p_ren ~inner:ren in
            (parent, ren', offset, i :: rev_lift))
          decl.tc_prts in
      bfs (rest @ next) in
  let initial =
    List.mapi (fun i tc -> (tc, [], i, [])) tcs in
  bfs initial;
  List.rev !recorded

(* -------------------------------------------------------------------- *)
(* Canonical [(offset, lift)] reaching [(target_path, target_ren)] from
   [tcs], using the BFS-first table.                                    *)
let canonical_path
  (env        : EcEnv.env)
  (tcs        : typeclass list)
  (target     : EcPath.path)
  (target_ren : (EcSymbols.symbol * EcSymbols.symbol) list)
  : canon_path option
=
  let table = canonical_table env tcs in
  List.find_opt
    (fun ((p, r), _) -> EcPath.p_equal p target && ren_equal r target_ren)
    table
  |> Option.map snd

(* -------------------------------------------------------------------- *)
(* Look up the TC constraints of an abstract-witness support. *)
let support_tcs (env : EcEnv.env)
                (sup : [ `Var of EcIdent.t | `Abs of EcPath.path ])
  : typeclass list option
=
  match sup with
  | `Abs p -> begin
      match EcEnv.Ty.by_path_opt p env with
      | Some { tyd_type = `Abstract tcs; _ } -> Some tcs
      | _ -> None
    end
  | `Var _ ->
    (* [`Var v] supports require the surrounding context's tparam-to-TC
       map. Without it (only an [EcEnv.env] is available globally), we
       can't canonicalise; leave the witness untouched. *)
    None

(* -------------------------------------------------------------------- *)
(* Canonicalise a single tcwitness via the table. Only [TCIAbstract] is
   changed, only when its support's TC list is reachable from [env] and
   the path's target/renaming has a recorded canonical encoding.        *)
let rec canonicalise_witness (env : EcEnv.env) (tcw : tcwitness) : tcwitness =
  match tcw with
  | TCIUni _ -> tcw

  | TCIConcrete c ->
    let etyargs =
      List.map (fun (ty, ws) -> (ty, List.map (canonicalise_witness env) ws))
        c.etyargs in
    TCIConcrete { c with etyargs }

  | TCIAbstract { support; offset; lift } -> begin
    match support_tcs env support with
    | None -> tcw
    | Some tcs ->
      match walk_path env (List.nth tcs offset) lift with
      | None -> tcw
      | Some (target, ren) ->
        match canonical_path env tcs target.tc_name ren with
        | None -> tcw
        | Some (o', l') ->
          if o' = offset && l' = lift then tcw
          else TCIAbstract { support; offset = o'; lift = l' }
    end
