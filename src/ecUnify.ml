(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcMaps
open EcUtils
open EcAst
open EcTypes
open EcCoreSubst
open EcDecl
open EcTheory

module Sp = EcPath.Sp

(* ==================================================================== *)
type problem = [
  | `TyUni of ty * ty
  | `TcTw  of tcwitness * tcwitness
  | `TcCtt of tcuni * ty * typeclass
]

(* ==================================================================== *)
type uniflags = { tyvars: bool; tcvars: bool; }

exception UnificationFailure of problem
exception UninstanciateUni of uniflags
exception AmbiguousTcInstance of typeclass * EcPath.path list

(* ==================================================================== *)
module Unify = struct
  module UFArgs = struct
    module I = struct
      type t = tyuni

      let equal   = TyUni.uid_equal
      let compare = TyUni.uid_compare
    end

    module D = struct
      type data    = ty option
      type effects = problem list

      let default : data =
        None

      let isvoid (x : data) =
        Option.is_none x

      let noeffects : effects = []

      let union (ty1 : data) (ty2 : data) : data * effects =
        let ty, cts =
          match ty1, ty2 with
          | None, None ->
              (None, [])
          | Some ty1, Some ty2 ->
              Some ty1, [(ty1, ty2)]

          | None, Some ty | Some ty, None ->
              Some ty, [] in

        let cts = List.map (fun x -> `TyUni x) cts in

        ty, (cts :> effects)
    end
  end

  (* ------------------------------------------------------------------ *)
  module UF = EcUFind.Make(UFArgs.I)(UFArgs.D)

  (* ------------------------------------------------------------------ *)
  type ucore = {
    uf    : UF.t;
    tvtc  : typeclass list Mid.t;
    tcenv : tcenv;
  }

  and tcenv = {
    (* Map from UID to TC problems. The optional [symbol] is the
       op name when the problem was created at op-typing site, used
       to disambiguate parent-DAG paths whose cumulative renaming
       would clobber that name.                                       *)
    problems : (ty * typeclass * EcSymbols.symbol option) TcUni.Muid.t;

    (* Map from univars to TC problems that depend on them.         *)
    byunivar : TcUni.Suid.t TyUni.Muid.t;

    (* Map from problems UID to type-class instance witness         *)
    resolution : tcwitness TcUni.Muid.t
  }

  (* ------------------------------------------------------------------ *)
  let tcenv_empty : tcenv =
    { problems   = TcUni.Muid.empty
    ; byunivar   = TyUni.Muid.empty
    ; resolution = TcUni.Muid.empty }

  (* ------------------------------------------------------------------ *)
  let tcenv_closed (tcenv : tcenv) : bool =
      TcUni.Muid.cardinal tcenv.resolution
    = TcUni.Muid.cardinal tcenv.problems

  (* ------------------------------------------------------------------ *)
  let create_tcproblem
      ?(op_name : EcSymbols.symbol option)
      (tcenv : tcenv)
      (ty    : ty)
      (tcw   : typeclass * tcwitness option)
    : tcenv * tcwitness
  =
    let tc, tw = tcw in
    let uid = TcUni.unique () in
    let deps = Tuni.univars ty in

    let tcenv = {
      problems = TcUni.Muid.add uid (ty, tc, op_name) tcenv.problems;
      byunivar = TyUni.Suid.fold (fun duni byunivar ->
          TyUni.Muid.change (fun pbs ->
            Some (TcUni.Suid.add uid (Option.value ~default:TcUni.Suid.empty pbs))
          ) duni byunivar
        ) deps tcenv.byunivar;
      resolution =
        ofold
          (fun tw map -> TcUni.Muid.add uid tw map)
          tcenv.resolution tw;
    } in

    tcenv, TCIUni (uid, [])

  (* ------------------------------------------------------------------ *)
  let initial_ucore ?(tvtc = Mid.empty) () : ucore =
    { uf = UF.initial; tcenv = tcenv_empty; tvtc; }

  (* -------------------------------------------------------------------- *)
  type closed = { tyuni : ty -> ty; tcuni : tcwitness -> tcwitness; }

  (* -------------------------------------------------------------------- *)
  let close (uc : ucore) : closed =
    let tymap = Hint.create 0 in
    let tcmap = Hint.create 0 in

    let rec doit_ty t =
      match t.ty_node with
      | Tunivar i -> begin
          match Hint.find_opt tymap (i :> int) with
          | Some t -> t
          | None   -> begin
            let t =
              match UF.data i uc.uf with
              | None   -> tuni (UF.find i uc.uf)
              | Some t -> doit_ty t
            in
              Hint.add tymap (i :> int) t; t
          end
        end

      | _ -> ty_map doit_ty t
  
    and doit_tc (tw : tcwitness) =
      match tw with
      | TCIUni (uid, lift) -> begin
        match Hint.find_opt tcmap (uid :> int) with
        | Some tw -> bump_lift lift tw
        | None ->
          let resolved =
            match TcUni.Muid.find_opt uid uc.tcenv.resolution with
            | None -> TCIUni (uid, [])
            | Some (TCIUni (uid', _)) when TcUni.uid_equal uid uid' -> TCIUni (uid, [])
            | Some tw -> doit_tc tw
          in
            Hint.add tcmap (uid :> int) resolved;
            bump_lift lift resolved
      end

      | TCIConcrete ({ etyargs; _ } as c) ->
        let etyargs =
          List.map
            (fun (ty, tws) -> (doit_ty ty, List.map doit_tc tws))
            etyargs
        in TCIConcrete { c with etyargs }

      | TCIAbstract { support = (`Var _ | `Abs _) } ->
        tw

    in { tyuni = doit_ty; tcuni = doit_tc; }

  (* ------------------------------------------------------------------ *)
  let subst_of_uf (uc : ucore) : ty TyUni.Muid.t =
    let close = close uc in

    let dereference_tyuni (uid : tyuni) =
      match close.tyuni (tuni uid) with
      | { ty_node = Tunivar uid' } when TyUni.uid_equal uid uid' -> None
      | ty -> Some ty in

    let bindings =
      List.filter_map (fun uid ->
        Option.map (fun ty -> (uid, ty)) (dereference_tyuni uid)
      ) (UF.domain uc.uf) in
    TyUni.Muid.of_list bindings

  (* -------------------------------------------------------------------- *)
  let check_closed (uc : ucore) =
    let tyvars = not (UF.closed uc.uf) in
    let tcvars = not (tcenv_closed uc.tcenv) in

    if tyvars || tcvars then
      raise (UninstanciateUni { tyvars; tcvars })

  (* ------------------------------------------------------------------ *)
  let fresh
    ?(op_name : EcSymbols.symbol option)
    ?(tcs : (typeclass * tcwitness option) list option)
    ?(ty  : ty option)
    ({ uf; tcenv } as uc : ucore)
  =
    let uid = TyUni.unique () in

    let uf  =
      match ty with
      | Some { ty_node = Tunivar id } ->
          let uf = UF.set uid None uf in
          let ty, effects = UF.union uid id uf in
          assert (List.is_empty effects);
          ty

      | (None | Some _) as ty ->
          UF.set uid ty uf
    in

    let ty = Option.value ~default:(tuni uid) (UF.data uid uf) in

    let tcenv, tws =
      List.fold_left_map
        (fun tcenv tcw -> create_tcproblem ?op_name tcenv ty tcw)
        tcenv (Option.value ~default:[] tcs) in

    ({ uc with uf; tcenv; }, (tuni uid, tws))

  (* ------------------------------------------------------------------ *)
  let unify_core (env : EcEnv.env) (uc : ucore) (pb : problem) : ucore =
    let failure () = raise (UnificationFailure pb) in

    let uc = ref uc in
    let pb = let x = Queue.create () in Queue.push pb x; x in

    (* Seed the queue with every unresolved TC constraint. This catches
       problems whose carrier type had no univar deps at creation time
       (e.g. [Tvar 'a] for a TC-constrained type parameter), which would
       otherwise sit in [problems] forever, never triggered via
       [byunivar] eviction. Re-pushing already-deferred problems is
       idempotent: the [`TcCtt] arm just re-adds them to [byunivar]. *)
    TcUni.Muid.iter (fun uid (ty, tc, _op_name) ->
      if not (TcUni.Muid.mem uid (!uc).tcenv.resolution) then
        Queue.push (`TcCtt (uid, ty, tc)) pb
    ) (!uc).tcenv.problems;

    let ocheck i t =
      let i   = UF.find i (!uc).uf in
      let map = Hint.create 0 in

      let rec doit t =
        match t.ty_node with
        | Tunivar i' -> begin
            let i' = UF.find i' (!uc).uf in
            match i' with
            | _ when i = i' -> true
            | _ when Hint.mem map (i' :> int) -> false
            | _ ->
                match UF.data i' (!uc).uf with
                | None   -> Hint.add map (i' :> int) (); false
                | Some t ->
                  match doit t with
                  | true  -> true
                  | false -> Hint.add map (i' :> int) (); false
        end

        | _ -> ty_sub_exists doit t
      in
        doit t
    in

    let setvar (i : tyuni) (t : ty) =
      let (ti, effects) =
        UFArgs.D.union (UF.data i (!uc).uf) (Some t)
      in
        if odfl false (ti |> omap (ocheck i)) then failure ();
        List.iter (Queue.push^~ pb) effects;

        begin
          match TyUni.Muid.find i (!uc).tcenv.byunivar with
          | tcpbs ->
            uc := { !uc with tcenv = { (!uc).tcenv with
              byunivar = TyUni.Muid.remove i (!uc).tcenv.byunivar
            } };
            let tcpbs = TcUni.Suid.elements tcpbs in
            let tcpbs = List.map (fun uid ->
              let pb = TcUni.Muid.find uid (!uc).tcenv.problems in
              (uid, pb)
            ) tcpbs in
            List.iter (fun (uid, (ty, tc, _op)) -> Queue.push (`TcCtt (uid, ty, tc)) pb) tcpbs

          | exception Not_found -> ()
        end;

        uc := { !uc with uf = UF.set i ti (!uc).uf }

    and getvar t =
      match t.ty_node with
      | Tunivar i -> odfl t (UF.data i (!uc).uf)
      | _ -> t
    in

    let doit () =
      while not (Queue.is_empty pb) do
        match Queue.pop pb with
        | `TyUni (t1, t2) -> begin
          let (t1, t2) = (getvar t1, getvar t2) in

          match ty_equal t1 t2 with
          | true  -> ()
          | false -> begin
              match t1.ty_node, t2.ty_node with
              | Tunivar id1, Tunivar id2 -> begin
                  if not (TyUni.uid_equal id1 id2) then begin
                    let effects =
                        reffold (fun uc ->
                          let uf, effects = UF.union id1 id2 uc.uf in
                          effects, { uc with uf }
                        ) uc in
                    List.iter (Queue.push^~ pb) effects;
                    (* Merge byunivar entries onto the new representative. *)
                    let repr = UF.find id1 (!uc).uf in
                    let merge id =
                      if not (TyUni.uid_equal id repr) then
                        match TyUni.Muid.find_opt id (!uc).tcenv.byunivar with
                        | None -> ()
                        | Some pbs ->
                          uc := { !uc with tcenv = { (!uc).tcenv with byunivar =
                            let bv = TyUni.Muid.remove id (!uc).tcenv.byunivar in
                            TyUni.Muid.change (fun map ->
                              let map = Option.value ~default:TcUni.Suid.empty map in
                              Some (TcUni.Suid.union map pbs)
                            ) repr bv
                          } }
                    in merge id1; merge id2
                  end
              end

              | Tunivar id, _ -> setvar id t2
              | _, Tunivar id -> setvar id t1

              | Ttuple lt1, Ttuple lt2 ->
                  if List.length lt1 <> List.length lt2 then failure ();
                  List.iter2 (fun t1 t2 -> Queue.push (`TyUni (t1, t2)) pb) lt1 lt2

              | Tfun (t1, t2), Tfun (t1', t2') ->
                  Queue.push (`TyUni (t1, t1')) pb;
                  Queue.push (`TyUni (t2, t2')) pb

              | Tconstr (p1, lt1), Tconstr (p2, lt2) when EcPath.p_equal p1 p2 ->
                if List.length lt1 <> List.length lt2 then failure ();

                let ty1, tws1 = List.split lt1 in
                let ty2, tws2 = List.split lt2 in

                List.iter2 (fun t1 t2 -> Queue.push (`TyUni (t1, t2)) pb) ty1 ty2;

                List.iter2 (fun tw1 tw2 ->
                  if List.length tw1 <> List.length tw2 then failure ();
                  List.iter2 (fun w1 w2 -> Queue.push (`TcTw (w1, w2)) pb) tw1 tw2
                ) tws1 tws2

              | Tconstr (p, lt), _ when EcEnv.Ty.defined p env ->
                  Queue.push (`TyUni (EcEnv.Ty.unfold p lt env, t2)) pb

              | _, Tconstr (p, lt) when EcEnv.Ty.defined p env ->
                  Queue.push (`TyUni (t1, EcEnv.Ty.unfold p lt env)) pb

              | _, _ -> failure ()
          end
        end

        | `TcCtt (uid, ty, tc) when
            TcUni.Muid.mem uid (!uc).tcenv.resolution ->
          (* [uid] was already pinned (e.g. by a prior [TcTw] equation
             from the surrounding goal). Honor that binding rather than
             re-running strategies, which could produce a different
             witness on ambiguous instance lookups. *)
          ignore (ty, tc)

        | `TcCtt (uid, ty, tc) ->
          (* Op name attached to this problem at creation time, used
             below to filter parent-DAG paths whose cumulative renaming
             would clobber that name. None for TC problems not tied to
             a specific named op. *)
          let pb_op : EcSymbols.symbol option =
            match TcUni.Muid.find_opt uid (!uc).tcenv.problems with
            | Some (_, _, op) -> op
            | None -> None in
          (* See doc/typeclasses-inference.md for the strategy framework
             and the catalog of inference modes this resolver covers. *)
          let deps = ref TyUni.Suid.empty in

          let rec check_ty (ty : ty) : ty =
            match ty.ty_node with
            | Tunivar tyuvar -> begin
              match UF.data tyuvar (!uc).uf with
              | None ->
                deps := TyUni.Suid.add tyuvar !deps;
                ty
              | Some ty ->
                check_ty ty
              end
            | _ -> ty_map check_ty ty in

          let rec check_tcw (tcw : tcwitness) : tcwitness =
            match tcw with
            | TCIUni (tcuid, lift) -> begin
              match TcUni.Muid.find_opt tcuid (!uc).tcenv.resolution with
              | Some (TCIUni (tcuid', _)) when TcUni.uid_equal tcuid tcuid' -> tcw
              | Some tcw' -> bump_lift lift (check_tcw tcw')
              | None -> tcw
            end
            | TCIConcrete cw ->
              let etyargs = List.map check_etyarg cw.etyargs in
              TCIConcrete { cw with etyargs }
            | TCIAbstract _ -> tcw
          and check_etyarg ((ty, tcws) : etyarg) =
            (check_ty ty, List.map check_tcw tcws) in

          let tc =
            { tc with tc_args = List.map check_etyarg tc.tc_args } in

          let ty = check_ty ty in
          let deps = !deps in

          (* ---- Helpers shared across strategies ---- *)
          (* [tvtc] stores TC constraints as they were typed at tparam
             declaration; the args may still mention Tunivars that were
             since merged in [uf]. Dereference via [check_etyarg] before
             structural comparison. *)
          let deref_tc (tc' : typeclass) =
            { tc' with tc_args = List.map check_etyarg tc'.tc_args } in
          (* Compare on type arguments only; the corresponding tcwitnesses
             are determined by [(carrier, type args)] and may legitimately
             differ in form (e.g. unresolved TCIUni vs concrete) while
             still picking out the same TC. *)
          let eq_tc (tc' : typeclass) =
            let tc' = deref_tc tc' in
            EcPath.p_equal tc.tc_name tc'.tc_name
            && List.length tc.tc_args = List.length tc'.tc_args
            && List.for_all2
                 (fun (a, _) (b, _) -> EcCoreEqTest.for_type env a b)
                 tc.tc_args tc'.tc_args in

          (* Enumerate all parent-DAG paths from [tc'] to [tc]. Each
             returned entry is a list of parent-edge indices paired
             with the cumulative ancestor→child op renaming along the
             walk. [[]] means [tc' = tc] directly. With single-parent
             inheritance the path is always all-zeros; with
             multi-parent (factory) classes the path encodes which
             parent edge is taken at each step.

             The renaming is needed downstream to filter paths by
             op-name preservation: when querying op [n] via this TC,
             only paths whose cumulative renaming preserves [n] can
             expose it under the same name at the carrier site. *)
          let with_lift tc'
            : (int list * (EcSymbols.symbol * EcSymbols.symbol) list) list
          =
            let rec walk tc ren path acc =
              if eq_tc tc then (List.rev path, ren) :: acc
              else
                let decl = EcEnv.TypeClass.by_path tc.tc_name env in
                let subst =
                  List.fold_left2
                    (fun s (a, _) etyarg -> Mid.add a etyarg s)
                    Mid.empty decl.tc_tparams tc.tc_args in
                List.fold_lefti
                  (fun acc i (parent, _p_lbl, p_ren) ->
                    let parent = EcCoreSubst.Tvar.subst_tc subst parent in
                    let ren' =
                      EcTypeClass.compose_renaming ~outer:p_ren ~inner:ren in
                    walk parent ren' (i :: path) acc)
                  acc decl.tc_prts
            in walk tc' [] [] [] in
          (* Returns all valid [(offset, path, renaming)] matches
             across [tcs], one per (offset, parent-path) pair that
             reaches [tc]. The renaming is the cumulative
             ancestor→child op renaming for that path. *)
          let match_tc_offsets_all (tcs : typeclass list)
            : (int * int list * (EcSymbols.symbol * EcSymbols.symbol) list) list
          =
            List.concat (List.mapi
              (fun i tc' ->
                List.map (fun (p, ren) -> (i, p, ren)) (with_lift tc'))
              tcs) in
          (* Op-name-aware variant: when [pb_op] is set, drop paths
             whose cumulative renaming clobbers the op name. *)
          let match_tc_offsets (tcs : typeclass list) =
            let cands = match_tc_offsets_all tcs in
            match pb_op with
            | None -> cands
            | Some n ->
              List.filter
                (fun (_, _, ren) -> EcTypeClass.op_preserved ren n)
                cands in
          let rens_equal r1 r2 =
            List.length r1 = List.length r2
            && List.for_all (fun (a, b) ->
                 match List.assoc_opt a r2 with
                 | Some b' -> b = b'
                 | None -> false) r1 in
          let match_tc_offset (tcs : typeclass list)
            : (int * int list * (EcSymbols.symbol * EcSymbols.symbol) list) option
          =
            (* Multi-parent inheritance can yield several parent-DAG
               paths reaching the same target TC. When all such paths
               carry the same cumulative renaming, they're
               semantically interchangeable, so picking the canonical
               (BFS-first) encoding is safe. Only ambiguity-preserving
               (different renamings) genuinely blocks resolution. *)
            match match_tc_offsets tcs with
            | [] -> None
            | m :: rest ->
              let (_, _, ren_m) = m in
              if not (List.for_all (fun (_, _, r) -> rens_equal r ren_m) rest)
              then None
              else
                match EcTcCanonical.canonical_path env tcs tc.tc_name ren_m with
                | Some (off, lift) -> Some (off, lift, ren_m)
                | None -> Some m in

          (* ---- Strategies (catalog modes) ----
             Each strategy returns [Some witness] when it resolves, or
             [None] when it does not apply / cannot decide. The dispatcher
             below tries them in priority order. *)

          (* Mode #5: carrier is [Tvar a] with a in [tvtc]. *)
          let strat_tvar_via_tvtc () : tcwitness option =
            match ty.ty_node with
            | Tvar a ->
              let tcs = ofdfl failure (Mid.find_opt a (!uc).tvtc) in
              Option.map
                (fun (offset, lift, _ren) ->
                  TCIAbstract { support = `Var a; offset; lift })
                (match_tc_offset tcs)
            | _ -> None in

          (* Mode #6: carrier is [Tconstr p] with [p] an abstract decl. *)
          let strat_abs_via_decl () : tcwitness option =
            match ty.ty_node with
            | Tconstr (p, _) -> begin
              match EcEnv.Ty.by_path_opt p env with
              | Some { tyd_type = `Abstract tcs; _ } ->
                Option.map
                  (fun (offset, lift, _ren) ->
                    TCIAbstract { support = `Abs p; offset; lift })
                  (match_tc_offset tcs)
              | _ -> None
              end
            | _ -> None in

          (* Modes #1, #2: carrier is ground; query the instance
             database. Defined later (after [infer_all_op_preserving])
             so it can prefer an op-name-preserving candidate. *)
          let strat_infer_by_carrier_ref : (unit -> tcwitness option) ref =
            ref (fun () -> EcTypeClass.infer env ty tc) in
          let strat_infer_by_carrier () : tcwitness option =
            !strat_infer_by_carrier_ref () in
          (* Ambiguity check: when multiple resolutions match, defer
             so that later [TcTw] equations from the surrounding goal
             can pin the univar to the correct one.

             Two sources of ambiguity:
             - Concrete carriers: [infer_all] returns multiple
               synthesised instances (multi-flavor inheritance).
             - Tvar / abstract-type carriers: [match_tc_offsets]
               returns multiple (offset, path) pairs (multiple parent
               paths through the DAG to the same target TC).         *)
          (* Multiple paths with identical renamings are not
             genuinely ambiguous — [match_tc_offset] picks one. *)
          let paths_genuinely_ambiguous tcs =
            match match_tc_offsets tcs with
            | [] | [_] -> false
            | m :: rest ->
              let (_, _, ren_m) = m in
              not (List.for_all (fun (_, _, r) -> rens_equal r ren_m) rest) in
          (* Filter [infer_all] candidates by op-name preservation
             when [pb_op] is set. Each chain-synthesised candidate
             carries a [tci_chain_rename] tag recording the cumulative
             ancestor->leaf renaming; we drop candidates whose rename
             clobbers the queried op name. This collapses the spurious
             multiplicity at a comring/idomain/field carrier when the
             user writes a class op like [(+)<:zmod>]: only the
             addmonoid-path monoid view preserves [+], so the
             mulmonoid-renamed view (where [+] became [*]) is dropped.

             Manually-declared (non-chain) instances have
             [tci_chain_rename = None]; treat them as preserving
             every op (they're roots of their own chains).            *)
          let infer_all_op_preserving () =
            let cands = EcTypeClass.infer_all env ty tc in
            match pb_op with
            | None -> cands
            | Some _ when List.length cands < 2 -> cands
            | Some op_name ->
              let preserves (w : tcwitness) : bool =
                match w with
                | TCIConcrete { path; _ } -> begin
                    match (EcEnv.TcInstance.by_path path env).tci_chain_rename with
                    | None -> true
                    | Some ren -> EcTypeClass.op_preserved ren op_name
                  end
                | _ -> true in
              List.filter preserves cands in
          (* Rebind [strat_infer_by_carrier] to use the op-preserving
             filtered list: when [pb_op] is set, take the first
             candidate that preserves the op name. This makes the
             resolution step pick the addmonoid view of [+] (not the
             mulmonoid-renamed view) at a concrete comring carrier. *)
          strat_infer_by_carrier_ref :=
            (fun () ->
               match infer_all_op_preserving () with
               | w :: _ -> Some w
               | [] -> EcTypeClass.infer env ty tc);
          let strat_carrier_is_ambiguous () : bool =
            match ty.ty_node with
            | Tvar a -> begin
                match Mid.find_opt a (!uc).tvtc with
                | None -> false
                | Some tcs -> paths_genuinely_ambiguous tcs
              end
            | Tconstr (p, _) -> begin
                let by_decl =
                  match EcEnv.Ty.by_path_opt p env with
                  | Some { tyd_type = `Abstract tcs; _ } ->
                      paths_genuinely_ambiguous tcs
                  | _ -> false in
                by_decl
                || List.length (infer_all_op_preserving ()) > 1
              end
            | _ -> false in

          (* Univars appearing in [tc.tc_args] (types and witnesses).
             Used both for the Mode-#3 strategy gating and to register
             extra parking edges so the problem re-fires when one of
             them is resolved later. *)
          let etyarg_univars (a, ws) =
            let from_ty = Tuni.univars a in
            List.fold_left (fun s w ->
              TyUni.Suid.union s
                (tcw_fold
                   (fun s t -> TyUni.Suid.union s (Tuni.univars t))
                   TyUni.Suid.empty w))
              from_ty ws in
          let arg_deps =
            List.fold_left (fun s a -> TyUni.Suid.union s (etyarg_univars a))
              TyUni.Suid.empty tc.tc_args in

          (* Mode #3: carrier is a univar; identify a unique matching
             instance by [tc.tc_args] (Tunivars on the goal side act
             as wildcards), then push a [`TyUni (ty, tci_type)]
             equation. The carrier resolution will then re-fire this
             TcCtt under Mode #1 and produce the concrete witness.
             For TCs with no args (e.g. [addmonoid]), all instances
             match trivially, so by-args contributes no signal — skip. *)
          let strat_infer_by_args () : tcwitness option =
            if List.is_empty tc.tc_args then None else
            let cands = EcTypeClass.candidates_by_args env tc in
            (* Multiple matches: check whether they agree on the
               carrier ([tci_type]). If they do, any of them works; if
               they don't, the goal is genuinely ambiguous and no
               further unification can decide between them. *)
            if List.length cands >= 2 then begin
              let carriers =
                List.map (fun (_, tci, _) -> tci.tci_type) cands in
              let same =
                match carriers with
                | [] | [_] -> true
                | t :: rest ->
                  List.for_all (fun t' ->
                    EcCoreEqTest.for_type env t t') rest in
              if not same then begin
                let paths = List.filter_map (fun (p, _, _) -> p) cands in
                raise (AmbiguousTcInstance (tc, paths))
              end
            end;
            match cands with
            | [(Some _, tci, _map)] -> begin
              (* Recover the candidate's [tgp.tc_args] (the patterns). *)
              let tgargs =
                match tci.tci_instance with
                | `General (tgp, _) -> tgp.tc_args
                | _ -> assert false in
              (* Open the candidate's tparams as fresh univars. *)
              let inst_subst =
                List.fold_left (fun subst (a, _) ->
                  let (uc', (fresh_ty, _)) = fresh (!uc) in
                  uc := uc' ;
                  Mid.add a (fresh_ty, []) subst
                ) Mid.empty tci.tci_params in
              let tgargs =
                List.map (EcCoreSubst.Tvar.subst_etyarg inst_subst) tgargs in
              let inst_carrier =
                EcCoreSubst.Tvar.subst inst_subst tci.tci_type in
              (* Push TyUni equations: each goal arg unifies with the
                 candidate's substituted arg, and the carrier with
                 [tci_type]. The unifier binds goal Tunivars to the
                 corresponding patterns and triggers Mode #1 re-firing
                 once the carrier is concrete. *)
              List.iter2 (fun (gty, _) (pty, _) ->
                Queue.push (`TyUni (gty, pty)) pb)
                tc.tc_args tgargs;
              Queue.push (`TyUni (ty, inst_carrier)) pb;
              None  (* Defer witness construction; Mode #1 will fire. *)
              end
            | _ -> None in

          (* ---- Dispatch ---- *)
          if TyUni.Suid.is_empty deps then begin
            let ambiguous =
              match ty.ty_node with
              | Tvar _ | Tconstr _ -> strat_carrier_is_ambiguous ()
              | _ -> false in
            let resolution_opt =
              if ambiguous then None
              else
                match ty.ty_node with
                | Tvar _ ->
                  strat_tvar_via_tvtc ()
                | Tconstr _ when Option.is_some (strat_abs_via_decl ()) ->
                  strat_abs_via_decl ()
                | _ ->
                  strat_infer_by_carrier ()
            in
            match resolution_opt with
            | Some resolution ->
              uc := { !uc with tcenv = { (!uc).tcenv with resolution =
                TcUni.Muid.add uid resolution (!uc).tcenv.resolution
              } }
            | None when not (TyUni.Suid.is_empty arg_deps) ->
              (* Carrier is concrete but TC arg univars still pending;
                 park on those so we re-fire when they bind. *)
              TyUni.Suid.iter (fun tyvar ->
                uc := { !uc with tcenv = { (!uc).tcenv with byunivar =
                  TyUni.Muid.change (fun map ->
                    let map = Option.value ~default:TcUni.Suid.empty map in
                    Some (TcUni.Suid.add uid map)
                  ) tyvar (!uc).tcenv.byunivar
                } }
              ) arg_deps
            | None when ambiguous ->
              (* Defer: hold this TcCtt unresolved. A later [TcTw]
                 equation from the surrounding goal will pin [uid]
                 to the goal's specific witness via [bind_uni]. *)
              ()
            | None -> failure ()
          end else begin
            match strat_infer_by_args () with
            | Some witness ->
              uc := { !uc with tcenv = { (!uc).tcenv with resolution =
                TcUni.Muid.add uid witness (!uc).tcenv.resolution
              } }
            | None ->
              (* Mode #4: carrier still has univars; park on each.
                 Also park on [arg_deps] so a later binding of a
                 typeclass argument re-fires Mode #3. *)
              TyUni.Suid.iter (fun tyvar ->
                uc := { !uc with tcenv = { (!uc).tcenv with byunivar =
                  TyUni.Muid.change (fun map ->
                    let map = Option.value ~default:TcUni.Suid.empty map in
                    Some (TcUni.Suid.add uid map)
                  ) tyvar (!uc).tcenv.byunivar
                } }
              ) (TyUni.Suid.union deps arg_deps)
          end

        | `TcTw (w1, w2) ->
          (* Resolve a [TCIUni (u, l)] one level: if [u] has a known
             resolution [r], return [bump_lift l r]; otherwise leave the
             reference intact. This is local to the current unification
             attempt. *)
          let resolve_uni = function
            | TCIUni (uid, lift) -> begin
              match TcUni.Muid.find_opt uid (!uc).tcenv.resolution with
              | Some w -> bump_lift lift w
              | None   -> TCIUni (uid, lift)
            end
            | w -> w in

          let w1 = resolve_uni w1 in
          let w2 = resolve_uni w2 in

          let bind_uni uid lift target =
            (* We want [bump_lift lift R = target] where [R] is the
               resolution of [uid] (a witness for [uid]'s carrier-type
               at [uid]'s TC class). With canonical-encoded paths
               everywhere (Stage 2 Phase A/C), [target]'s path ends
               with [lift] when reachable via [uid], so structural
               suffix-strip recovers [R].                              *)
            let strip_suffix sfx l =
              match sfx, List.rev l with
              | [], _ -> Some l
              | _, [] -> None
              | _, _ ->
                let sfx_rev = List.rev sfx in
                let l_rev = List.rev l in
                let rec eq_pref a b =
                  match a, b with
                  | [], _ -> Some (List.rev b)
                  | _, [] -> None
                  | x :: xs, y :: ys when x = y -> eq_pref xs ys
                  | _ -> None
                in eq_pref sfx_rev l_rev in
            let strip_lift sfx w =
              match w with
              | TCIUni (u, l) ->
                Option.map (fun l' -> TCIUni (u, l')) (strip_suffix sfx l)
              | TCIConcrete c ->
                Option.map (fun l' -> TCIConcrete { c with lift = l' })
                  (strip_suffix sfx c.lift)
              | TCIAbstract a ->
                Option.map (fun l' -> TCIAbstract { a with lift = l' })
                  (strip_suffix sfx a.lift) in
            match strip_lift lift target with
            | None -> failure ()
            | Some r ->
              uc := { !uc with tcenv = { (!uc).tcenv with resolution =
                TcUni.Muid.add uid r (!uc).tcenv.resolution
              } } in

          begin match w1, w2 with
          | TCIUni (u1, l1), TCIUni (u2, l2) when TcUni.uid_equal u1 u2 ->
            if l1 <> l2 then failure ()

          | TCIUni (uid, lift), w
          | w, TCIUni (uid, lift) ->
            bind_uni uid lift w

          | _, _ ->
            let w1 = EcTcCanonical.canonicalise_witness env w1 in
            let w2 = EcTcCanonical.canonicalise_witness env w2 in
            if not (EcAst.tcw_equal w1 w2) then failure ()
          end
      done
    in
      doit (); !uc

end

(* -------------------------------------------------------------------- *)
type unienv_r = {
  ue_uc     : Unify.ucore;
  ue_named  : EcIdent.t Mstr.t;
  ue_decl   : EcIdent.t list;
  ue_closed : bool;
}

type unienv = unienv_r ref

(* Optional user-supplied witness selector for a tvi entry. Resolved
   against the tparam's bound class at [opentvi] time to construct a
   [tcwitness]. Empty when the user didn't write [/Lbl+] or [via P]. *)
type witness_selector = {
  ws_labels : EcSymbols.symbol list;
  ws_via    : EcPath.path option;
}

let ws_empty : witness_selector = { ws_labels = []; ws_via = None; }
let ws_is_empty (s : witness_selector) =
  List.is_empty s.ws_labels && Option.is_none s.ws_via

type petyarg = ty option * tcwitness option list option * witness_selector

type tvar_inst =
| TVIunamed of petyarg list
| TVInamed  of (EcSymbols.symbol * petyarg) list

type tvi = tvar_inst option

let tvi_unamed (ety : etyarg list) : tvar_inst =
  TVIunamed (List.map
    (fun (ty, tcw) ->
       (Some ty, Some (List.map Option.some tcw), ws_empty))
    ety
  )

module UniEnv = struct
  let copy (ue : unienv) : unienv =
    ref !ue

  let restore ~(dst:unienv) ~(src:unienv) =
    dst := !src

  let getnamed (ue : unienv) (x : symbol) =
      match Mstr.find_opt x (!ue).ue_named with
      | Some a -> a
      | None   -> begin
          if (!ue).ue_closed then raise Not_found;
          let id = EcIdent.create x in
            ue := { !ue with
              ue_named = Mstr.add x id (!ue).ue_named;
              ue_decl  = id :: (!ue).ue_decl;
            }; id
    end

  let create (vd : (EcIdent.t * typeclass list) list option) : unienv =
    let ue =
      match vd with
      | None ->
        { ue_uc     = Unify.initial_ucore ()
        ; ue_named  = Mstr.empty
        ; ue_decl   = []
        ; ue_closed = false
        }

      | Some vd ->
          let vdmap = List.map (fun (x, _) -> (EcIdent.name x, x)) vd in
          let tvtc  = Mid.of_list vd in
          { ue_uc     = Unify.initial_ucore ~tvtc ()
          ; ue_named  = Mstr.of_list vdmap
          ; ue_decl   = List.rev_map fst vd
          ; ue_closed = true;
          }
      in ref ue

  let push ((x, tc) : ident * typeclass list) (ue : unienv)  =
    assert (not (Mstr.mem (EcIdent.name x) (!ue).ue_named));
    assert  ((!ue).ue_closed);

     ue :=
      { ue_uc     = { (!ue).ue_uc with tvtc = Mid.add x tc (!ue).ue_uc.tvtc }
      ; ue_named  = Mstr.add (EcIdent.name x) x (!ue).ue_named
      ; ue_decl   = x :: (!ue).ue_decl
      ; ue_closed = true }

  let xfresh
    ?(op_name : EcSymbols.symbol option)
    ?(tcs : (typeclass * tcwitness option) list option)
    ?(ty : ty option)
    (ue : unienv)
  =
    let (uc, tytw) = Unify.fresh ?op_name ?tcs ?ty (!ue).ue_uc in
    ue := { !ue with ue_uc = uc }; tytw

  let fresh ?(ty : ty option) (ue : unienv) =
    let (uc, (ty, tw)) = Unify.fresh ?ty (!ue).ue_uc in
    assert (List.is_empty tw);
    ue := { !ue with ue_uc = uc }; ty

  type opened = {
    subst  : etyarg Mid.t;
    params : (ty * typeclass list) list;
    args   : etyarg list;
  }  

  let subst_tv (subst : etyarg Mid.t) (params : ty_params) =
    List.map (fun (tv, tcs) ->
      let tv = Tvar.subst subst (tvar tv) in
      let tcs =
        List.map
          (fun tc ->
            let tc_args =
              List.map (Tvar.subst_etyarg subst) tc.tc_args 
            in { tc with tc_args })
          tcs
      in (tv, tcs)) params

  (* Resolve a user-supplied [witness_selector] against a target type
     [ty] and a tparam bound [tc], producing a [tcwitness] when the
     selector identifies a unique instance. Returns [None] for empty
     selectors (let the resolver decide). Requires [env] to look up
     instances and walk class chains; if [env = None] and a non-empty
     selector is supplied, raises [InvalidSelector]. *)
  exception InvalidSelector of string

  let resolve_witness_selector
    (env : EcEnv.env option) (ue : unienv) (ty : ty) (tc : typeclass)
    (sel : witness_selector) : tcwitness option
  =
    if ws_is_empty sel then None
    else
      let env =
        match env with
        | Some e -> e
        | None ->
          raise (InvalidSelector
            "witness selector supplied but env is not available at this site") in
      (* Common: lookup an instance by path, validate its class and
         carrier match [tc] and [ty]. *)
      let validate_and_build (path : EcPath.path) : tcwitness =
        let tci =
          match EcEnv.TcInstance.by_path_opt path env with
          | Some t -> t
          | None ->
            raise (InvalidSelector
              (Printf.sprintf "no instance at path %s"
                 (EcPath.tostring path))) in
        let tci_class =
          match tci.EcTheory.tci_instance with
          | `General (tcp, _) -> tcp.tc_name
          | `Ring _ -> raise (InvalidSelector
            "via/labels on Ring instance not supported")
          | `Field _ -> raise (InvalidSelector
            "via/labels on Field instance not supported")
        in
        if not (EcPath.p_equal tci_class tc.tc_name) then
          raise (InvalidSelector
            (Printf.sprintf
               "instance %s is for class %s, but selector targets bound %s"
               (EcPath.tostring path)
               (EcPath.tostring tci_class)
               (EcPath.tostring tc.tc_name)));
        if not (EcAst.ty_equal tci.EcTheory.tci_type ty) then
          raise (InvalidSelector
            (Printf.sprintf
               "instance %s has carrier %s, target type does not match"
               (EcPath.tostring path)
               (EcTypes.dump_ty tci.EcTheory.tci_type)));
        let etyargs = EcDecl.etyargs_of_tparams tci.EcTheory.tci_params in
        TCIConcrete { path; etyargs; lift = [] }
      in

      (* Label-based search: enumerate all instances at [ty] of [tc],
         filter by label-path containing the user's labels as a
         contiguous subsequence. *)
      let label_search (labels : EcSymbols.symbol list) : EcPath.path =
        let labels_match (qual : string list) (path_lbls : string list) =
          let qlen = List.length qual in
          let llen = List.length path_lbls in
          let rec scan i =
            if i + qlen > llen then false
            else
              let slice =
                List.filteri (fun j _ -> j >= i && j < i + qlen) path_lbls in
              if slice = qual then true else scan (i + 1)
          in qlen = 0 || scan 0 in
        let candidates =
          List.filter_map (fun (path_opt, tci) ->
            match path_opt with
            | None -> None
            | Some p ->
              let class_ok =
                match tci.EcTheory.tci_instance with
                | `General (tcp, _) -> EcPath.p_equal tcp.tc_name tc.tc_name
                | _ -> false in
              let carrier_ok = EcAst.ty_equal tci.EcTheory.tci_type ty in
              let labels_ok =
                match tci.EcTheory.tci_chain_labels with
                | None -> List.is_empty labels  (* legacy instance, no labels *)
                | Some lbls -> labels_match labels lbls in
              if class_ok && carrier_ok && labels_ok then Some p else None)
            (EcEnv.TcInstance.get_all env) in
        match candidates with
        | [p] -> p
        | [] ->
          raise (InvalidSelector
            (Printf.sprintf
               "no instance of class %s at carrier %s matching label \
                path [%s]"
               (EcPath.tostring tc.tc_name)
               (EcTypes.dump_ty ty)
               (String.concat "/" labels)))
        | ps ->
          raise (InvalidSelector
            (Printf.sprintf
               "ambiguous label path [%s] for class %s at carrier %s: \
                %d candidates (%s)"
               (String.concat "/" labels)
               (EcPath.tostring tc.tc_name)
               (EcTypes.dump_ty ty)
               (List.length ps)
               (String.concat ", " (List.map EcPath.tostring ps))))
      in

      (* Parametric / abstract carrier branch: when [ty] is [Tvar id]
         or [Tconstr p] with [p] an abstract type carrying class
         bounds, the witness is [TCIAbstract { support = …; offset;
         lift }]. Walk the carrier's declared bounds via BFS,
         tracking (offset, lift_rev, label_path_rev). *)
      let abstract_search
          (support : [ `Var of EcIdent.t | `Abs of EcPath.path ])
          (bounds : typeclass list)
          (labels : EcSymbols.symbol list)
        : tcwitness =
        let labels_match (qual : string list) (path_lbls : string list) =
          let qlen = List.length qual in
          let llen = List.length path_lbls in
          let rec scan i =
            if i + qlen > llen then false
            else
              let slice =
                List.filteri (fun j _ -> j >= i && j < i + qlen) path_lbls in
              if slice = qual then true else scan (i + 1)
          in qlen = 0 || scan 0 in
        if bounds = [] then
          raise (InvalidSelector
            (Printf.sprintf
               "no bounds found for carrier `%s'"
               (match support with
                | `Var v -> EcIdent.name v
                | `Abs p -> EcPath.tostring p)));
        (* BFS: each frontier entry is (tc, label_path_rev, offset, lift_rev). *)
        let matches = ref [] in
        let visited = ref [] in
        let already (tcn, lpath) =
          List.exists
            (fun (p, l) -> EcPath.p_equal p tcn && l = lpath) !visited in
        let rec bfs frontier =
          match frontier with
          | [] -> ()
          | (cur, lpath_rev, offset, lift_rev) :: rest ->
            let lpath = List.rev lpath_rev in
            if already (cur.tc_name, lpath) then bfs rest
            else begin
              visited := (cur.tc_name, lpath) :: !visited;
              if EcPath.p_equal cur.tc_name tc.tc_name
                 && labels_match labels lpath
              then
                matches := (offset, List.rev lift_rev) :: !matches;
              let decl = EcEnv.TypeClass.by_path cur.tc_name env in
              let next =
                List.mapi (fun i (parent, p_lbl, _p_ren) ->
                  (parent, p_lbl :: lpath_rev, offset, i :: lift_rev))
                  decl.tc_prts in
              bfs (rest @ next)
            end in
        let initial =
          List.mapi (fun i tc -> (tc, [], i, [])) bounds in
        bfs initial;
        let support_name () =
          match support with
          | `Var v -> EcIdent.name v
          | `Abs p -> EcPath.tostring p in
        match !matches with
        | [(offset, lift)] ->
          TCIAbstract { support; offset; lift }
        | [] ->
          raise (InvalidSelector
            (Printf.sprintf
               "no bound of carrier `%s' reaches class %s via \
                label path [%s]"
               (support_name ())
               (EcPath.tostring tc.tc_name)
               (String.concat "/" labels)))
        | ms ->
          raise (InvalidSelector
            (Printf.sprintf
               "ambiguous label path [%s]: %d matches for class %s on \
                carrier `%s'"
               (String.concat "/" labels)
               (List.length ms)
               (EcPath.tostring tc.tc_name)
               (support_name ())))
      in

      (* Dispatch: identify whether the carrier is abstract (a type
         variable or a [`Abstract]-bounded type alias) or concrete
         (a fully-defined type). Abstract carriers want a
         [TCIAbstract] witness with [support] = `Var or `Abs;
         concrete carriers want a [TCIConcrete] witness derived
         from an env-level instance. *)
      let abstract_support () : (_ * typeclass list) option =
        match ty.ty_node with
        | Tvar id ->
          let bounds = odfl [] (Mid.find_opt id (!ue).ue_uc.tvtc) in
          Some (`Var id, bounds)
        | Tconstr (p, _) ->
          (match EcEnv.Ty.by_path_opt p env with
           | Some { tyd_type = `Abstract tcs; _ } -> Some (`Abs p, tcs)
           | _ -> None)
        | _ -> None
      in
      match abstract_support () with
      | Some (support, bounds) ->
        (match sel.ws_via, sel.ws_labels with
         | Some _, _ ->
           raise (InvalidSelector
             "`via` selector requires a concrete carrier; for type \
              variables or abstract types use [/Lbl+] only")
         | None, (_ :: _ as labels) ->
           Some (abstract_search support bounds labels)
         | None, [] -> None)
      | None ->
        match sel.ws_via, sel.ws_labels with
        | Some path, [] -> Some (validate_and_build path)
        | None, (_ :: _ as labels) ->
          let path = label_search labels in
          Some (validate_and_build path)
        | Some path, (_ :: _ as labels) ->
          (* Combined: the via-path must match the label-derived path. *)
          let lpath = label_search labels in
          if not (EcPath.p_equal path lpath) then
            raise (InvalidSelector
              (Printf.sprintf
                 "explicit `via %s' disagrees with label-derived path %s"
                 (EcPath.tostring path) (EcPath.tostring lpath)));
          Some (validate_and_build path)
        | None, [] -> None  (* unreachable: ws_is_empty caught this *)

  let opentvi
    ?(op_name : EcSymbols.symbol option)
    ?(env : EcEnv.env option)
    (ue : unienv) (params : ty_params) (tvi : tvi) : opened =
    let tvi =
      match tvi with
      | None ->
          List.map (fun (v, tcs) ->
            (v, (None, List.map (fun x -> (x, None)) tcs))
          ) params

      | Some (TVIunamed lt) ->
          (* Apply the user's [witness_selector] to construct a
             [tcwitness option list] for this tparam's bounds. V1:
             only handle single-bound tparams; multi-bound + selector
             requires per-bound syntax (future work). *)
          let apply_selector (tc : typeclass list) (ty : ty option)
              (sel : witness_selector)
            : tcwitness option list option =
            if ws_is_empty sel then None
            else
              match tc, ty with
              | [tc1], Some ty ->
                (match resolve_witness_selector env ue ty tc1 sel with
                 | None -> None
                 | Some w -> Some [Some w])
              | _ :: _ :: _, _ ->
                raise (InvalidSelector
                  "witness selector on a tparam with multiple bounds is \
                   not yet supported (per-bound syntax needed)")
              | _, None ->
                raise (InvalidSelector
                  "witness selector requires an explicit type")
              | [], _ ->
                raise (InvalidSelector
                  "witness selector on a tparam with no bounds")
          in
          let combine (v, tc) (ty, tcw, sel) =
            let tcw =
              match tcw with
              | Some _ -> tcw
              | None -> apply_selector tc ty sel in
            let tctcw =
              match tcw with
              | None ->
                List.map (fun tc -> (tc, None)) tc
              | Some tcw ->
                List.combine tc tcw
            in (v, (ty, tctcw)) in

          List.map2 combine params lt

      | Some (TVInamed lt) ->
          let apply_selector (tc : typeclass list) (ty : ty option)
              (sel : witness_selector)
            : tcwitness option list option =
            if ws_is_empty sel then None
            else
              match tc, ty with
              | [tc1], Some ty ->
                (match resolve_witness_selector env ue ty tc1 sel with
                 | None -> None
                 | Some w -> Some [Some w])
              | _ :: _ :: _, _ ->
                raise (InvalidSelector
                  "witness selector on a tparam with multiple bounds is \
                   not yet supported (per-bound syntax needed)")
              | _, None ->
                raise (InvalidSelector
                  "witness selector requires an explicit type")
              | [], _ ->
                raise (InvalidSelector
                  "witness selector on a tparam with no bounds")
          in
          List.map (fun (v, tc) ->
            let ty, tcw, sel =
                 List.assoc_opt (EcIdent.name v) lt
              |> Option.value ~default:(None, None, ws_empty) in

            let tcw =
              match tcw with
              | Some _ -> tcw
              | None -> apply_selector tc ty sel in
            let tcw =
              match tcw with
              | None ->
                List.map (fun _ -> None) tc
              | Some tcw ->
                tcw in

            (v, (ty, List.map2 (fun x y -> (x, y)) tc tcw))
          ) params
    in

    let subst =
      List.fold_left (fun s (v, (ty, tcws)) ->
        let tcs =
          let for1 (tc, tcw) =
            let tc =
              { tc_name = tc.tc_name;
                tc_args = List.map (Tvar.subst_etyarg s) tc.tc_args } in
            (tc, tcw)
          in List.map for1 tcws
        in Mid.add v (xfresh ?op_name ?ty ~tcs ue) s
      ) Mid.empty tvi in

    let args = List.map (fun (x, _) -> oget (Mid.find_opt x subst)) params in
    let params = subst_tv subst params in

    { subst; args; params; }

  let opentys (ue : unienv) (params : ty_params) (tvi : tvi) (tys : ty list) =
    let opened = opentvi ue params tvi in
    let tys = List.map (Tvar.subst opened.subst) tys in
    tys, opened

  let openty (ue : unienv) (params : ty_params) (tvi : tvi) (ty : ty) =
    let opened = opentvi ue params tvi in
    Tvar.subst opened.subst ty, opened

  let repr (ue : unienv) (t : ty) : ty =
    match t.ty_node with
    | Tunivar id -> odfl t (Unify.UF.data id (!ue).ue_uc.uf)
    | _ -> t

  let xclosed (ue : unienv) =
    try  Unify.check_closed (!ue).ue_uc; None
    with UninstanciateUni infos -> Some infos

  let closed (ue : unienv) =
    Option.is_none (xclosed ue)

  let assubst (ue : unienv) : ty TyUni.Muid.t =
    Unify.subst_of_uf (!ue).ue_uc

  let tw_assubst (ue : unienv) : tcwitness TcUni.Muid.t =
    (!ue).ue_uc.tcenv.resolution

  let close (ue : unienv) =
    Unify.check_closed (!ue).ue_uc;
    assubst ue

  (* Drain the pending TcCtt queue: invokes [Unify.unify_core] on a
     trivially-true [TyUni] problem, which causes the unifier to first
     re-process every parked [TcCtt] in [tcenv.problems]. After this,
     any constraint that the strategies (Mode #1 .. #6) can resolve is
     committed to [tcenv.resolution]. Constraints that defer (ambiguous
     or carrier-with-univars) stay parked.                              *)
  let flush_tc_problems (env : EcEnv.env) (ue : unienv) : unit =
    if not (TcUni.Muid.is_empty (!ue).ue_uc.tcenv.problems) then
      try
        let trig = tunit in
        let uc = Unify.unify_core env (!ue).ue_uc (`TyUni (trig, trig)) in
        ue := { !ue with ue_uc = uc }
      with UnificationFailure _ -> ()

  let tparams (ue : unienv) =
    let close = Unify.close (!ue).ue_uc in
    let deref_tc (tc : typeclass) : typeclass =
      let tc_args =
        List.map
          (fun (t, ws) -> (close.tyuni t, List.map close.tcuni ws))
          tc.tc_args
      in { tc with tc_args }
    in
    let fortv x =
      let tvtc = odfl [] (Mid.find_opt x (!ue).ue_uc.tvtc) in
      List.map deref_tc tvtc in
    List.map (fun x -> (x, fortv x)) (List.rev (!ue).ue_decl)
end

(* -------------------------------------------------------------------- *)
let unify_core (env : EcEnv.env) (ue : unienv) (pb : problem) =
  let uc = Unify.unify_core env (!ue).ue_uc pb in
  ue := { !ue with ue_uc = uc; }

(* -------------------------------------------------------------------- *)
let unify (env : EcEnv.env) (ue : unienv) (t1 : ty) (t2 : ty) =
  unify_core env ue (`TyUni (t1, t2))

(* -------------------------------------------------------------------- *)
let unify_tcw (env : EcEnv.env) (ue : unienv) (w1 : tcwitness) (w2 : tcwitness) =
  unify_core env ue (`TcTw (w1, w2))

(* -------------------------------------------------------------------- *)
let unify_etyarg (env : EcEnv.env) (ue : unienv) (e1 : etyarg) (e2 : etyarg) =
  let (t1, ws1) = e1 and (t2, ws2) = e2 in
  unify env ue t1 t2;
  if List.length ws1 <> List.length ws2 then
    raise (UnificationFailure (`TyUni (t1, t2)));
  List.iter2 (unify_tcw env ue) ws1 ws2

(* -------------------------------------------------------------------- *)
(* When typing an op application like [(+)<:comring>], the witness for
   the op's [<: monoid] tparam may be ambiguous: the carrier [comring]
   reaches [monoid] via two parent walks (via [addgroup] and via
   [mulmonoid]). The TC inference framework is op-name-agnostic, so
   it sees both paths as candidates.

   But the parent-edge renamings disambiguate: only paths whose
   cumulative ancestor→child renaming preserves the queried op name
   actually expose that op under the same name at the carrier site.

   This helper, called right after [opentvi] at op-typing sites, walks
   each fresh witness univar and binds it to the unique [TCIAbstract]
   for the op-name-preserving path, when one exists. If zero or
   multiple paths preserve the name, the witness is left as a univar
   and existing strategies handle it as before. *)
let disambiguate_op_witnesses
    (env     : EcEnv.env)
    (ue      : unienv)
    (op_name : EcSymbols.symbol)
    (params  : (ty * typeclass list) list)
    (args    : etyarg list)
  : unit
=
  let close = Unify.close (!ue).ue_uc in

  (* Path enumeration with renaming, top-level analogue of the
     [with_lift] inside [unify_core]. *)
  let with_lift_for (carrier_tcs : typeclass list) (target : typeclass)
    : (int * int list * (EcSymbols.symbol * EcSymbols.symbol) list) list
  =
    let target =
      let tc_args =
        List.map
          (fun (t, ws) -> (close.tyuni t, List.map close.tcuni ws))
          target.tc_args
      in { target with tc_args } in
    let eq_tc (tc' : typeclass) =
      let tc' =
        let tc_args =
          List.map
            (fun (t, ws) -> (close.tyuni t, List.map close.tcuni ws))
            tc'.tc_args
        in { tc' with tc_args } in
      EcPath.p_equal target.tc_name tc'.tc_name
      && List.length target.tc_args = List.length tc'.tc_args
      && List.for_all2
           (fun (a, _) (b, _) -> EcCoreEqTest.for_type env a b)
           target.tc_args tc'.tc_args in
    let rec walk tc ren path acc =
      if eq_tc tc then (List.rev path, ren) :: acc
      else
        let decl = EcEnv.TypeClass.by_path tc.tc_name env in
        let subst =
          List.fold_left2
            (fun s (a, _) etyarg -> Mid.add a etyarg s)
            Mid.empty decl.tc_tparams tc.tc_args in
        List.fold_lefti
          (fun acc i (parent, _p_lbl, p_ren) ->
            let parent = EcCoreSubst.Tvar.subst_tc subst parent in
            let ren' =
              EcTypeClass.compose_renaming ~outer:p_ren ~inner:ren in
            walk parent ren' (i :: path) acc)
          acc decl.tc_prts in
    List.concat (List.mapi
      (fun i tc' ->
        List.map (fun (p, ren) -> (i, p, ren)) (walk tc' [] [] []))
      carrier_tcs) in

  let try_pin
      ~(build : int -> int list -> tcwitness)
      (carrier_tcs : typeclass list)
      (target : typeclass)
      (w : tcwitness)
    : unit
  =
    match w with
    | TCIUni _ -> begin
        let candidates = with_lift_for carrier_tcs target in
        if List.length candidates < 2 then ()
        else
          let preserved =
            List.filter
              (fun (_, _, ren) -> EcTypeClass.op_preserved ren op_name)
              candidates in
          match preserved with
          | [(offset, lift, _)] ->
            (try unify_tcw env ue w (build offset lift)
             with UnificationFailure _ -> ())
          | _ -> ()
      end
    | _ -> () in

  List.iter2 (fun (carrier_ty, tcs) (_, ws) ->
    let carrier_ty = close.tyuni carrier_ty in
    if List.length tcs <> List.length ws then () else
    match carrier_ty.ty_node with
    | Tvar a -> begin
        match Mid.find_opt a (!ue).ue_uc.tvtc with
        | None -> ()
        | Some carrier_tcs ->
          let build offset lift =
            TCIAbstract { support = `Var a; offset; lift } in
          List.iter2 (try_pin ~build carrier_tcs) tcs ws
      end
    | Tconstr (p, _) -> begin
        match EcEnv.Ty.by_path_opt p env with
        | Some { tyd_type = `Abstract carrier_tcs; _ } ->
          let build offset lift =
            TCIAbstract { support = `Abs p; offset; lift } in
          List.iter2 (try_pin ~build carrier_tcs) tcs ws
        | _ -> ()
      end
    | _ -> ()
  ) params args

(* -------------------------------------------------------------------- *)
let tfun_expected (ue : unienv) ?retty (psig : ty list) =
  let ret = match retty with Some t -> t | None -> UniEnv.fresh ue in
  toarrow psig ret

(* -------------------------------------------------------------------- *)
type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

(* -------------------------------------------------------------------- *)
type select_filter_t = EcPath.path -> operator -> bool

type select_t =
  ((EcPath.path * etyarg list) * ty * unienv * sbody option) list

let select_op
  ?(hidden : bool = false)
  ?(filter : select_filter_t = fun _ _ -> true)
  ?(retty  : ty option)
   (tvi    : tvi)
   (env    : EcEnv.env)
   (name   : qsymbol)
   (ue     : unienv)
   (psig   : dom)
  : select_t
=
  ignore hidden;                (* FIXME *)

  let module D = EcDecl in

  let filter oppath op =
    (* Filter operator based on given type variables instanciation *)
    let filter_on_tvi =
      match tvi with
      | None -> fun _ -> true

      | Some (TVIunamed lt) ->
          let len = List.length lt in
            fun op ->
              let tparams = op.D.op_tparams in
              List.length tparams = len &&
              List.for_all2
                (fun (_, tcs) (_, tcw, _sel) ->
                  match tcw with
                  | None -> true
                  | Some tcw -> List.length tcs = List.length tcw)
                tparams lt

      | Some (TVInamed ls) -> fun op ->
          let tparams = List.map (fst_map EcIdent.name) op.D.op_tparams in
          let tparams = Msym.of_list tparams in
          List.for_all (fun (x, _) -> Msym.mem x tparams) ls

    in
      filter oppath op && filter_on_tvi op
  in

  let select (path, op) =
    let module E = struct exception Failure end in

    let subue = UniEnv.copy ue in

    try
      let UniEnv.{ subst = tip_full; args; params = oparams } =
        UniEnv.opentvi ~op_name:(EcPath.basename path) ~env
          subue op.D.op_tparams tvi in
      let tip = f_subst_init ~tv:(Mid.map fst tip_full) () in

      let top = EcCoreSubst.ty_subst tip op.D.op_ty in
      let texpected = tfun_expected subue ?retty psig in

      (try  unify env subue top texpected
       with UnificationFailure _ -> raise E.Failure);

      (* After type unification has pinned the carrier(s), try to
         disambiguate any TC witnesses by op-name preservation along
         parent walks. This is what lets [(+)<:comring>] pick the
         addgroup walk uniquely when [comring] inherits from both
         [addgroup] and [mulmonoid with (+) = ( * )]. *)
      disambiguate_op_witnesses env subue
        (EcPath.basename path) oparams args;

       let bd =
        match op.D.op_kind with
        | OB_nott nt ->
           let substnt () =
             (* Substitute tparams (both type and TC-witness univars
                bound during unification) into the abbrev body. We
                pass [~tw] alongside [~tv] so [TCIAbstract \`Var]
                witnesses captured at abbrev-definition time get
                rewritten through the tparam => etyarg map; without
                it the body keeps stale [\`Var] references to the
                abbrev's tparams. [~tw_uni] resolves [TCIUni]
                placeholders left over from [opentvi]; without it the
                body prints with uninferrable [#a[#b]] witnesses. *)
             let s =
               f_subst_init
                 ~tv:(Mid.map fst tip_full)
                 ~tw:(Mid.map snd tip_full)
                 ~tw_uni:(UniEnv.tw_assubst subue)
                 () in
             let xs = List.map (snd_map (ty_subst s)) nt.D.ont_args in
             let es = e_subst s in
             let bd = es nt.D.ont_body in
             (xs, bd)
           in Some (Lazy.from_fun substnt)

        | _ -> None
      in

      Some ((path, args), top, subue, bd)

    with E.Failure -> None

  in
    List.pmap select (EcEnv.Op.all ~check:filter ~name env)

(* -------------------------------------------------------------------- *)
(* Candidate-list filters shared between the elaborator (typing-time
   resolution of an ambiguous op name) and the printer (deciding the
   shortest unambiguous qualifier when displaying an op). The chain
   enforces a uniform "concrete iff reducible / non-abbrev wins" rule
   so that a goal printed by the system parses back to the same term.

   Each filter is monotone (drops candidates) and idempotent. Callers
   apply them in [canonicalize] order, with a [keep-all-on-empty]
   safeguard so a filter that would prune everything is skipped. *)

(* Drop a TC-op candidate when, for the resolved carrier, either
   (a) [tc_reduce] succeeds and yields a head op already among the
       non-TC candidates (the TC is just an indirection to it), or
   (b) the carrier is concrete but no instance applies (no chance of
       the TC ever firing on this carrier), and a non-TC candidate
       exists. *)
let drop_subsumed_tc (env : EcEnv.env) (ops : select_t) : select_t =
  let is_tc_op p =
    match EcEnv.Op.by_path_opt p env with
    | Some { op_kind = OB_oper (Some (OP_TC _)) } -> true
    | _ -> false in
  let concrete_paths =
    List.filter_map
      (fun ((p, _), _, _, _) -> if is_tc_op p then None else Some p)
      ops in
  if concrete_paths = [] then ops
  else
  let carrier_is_concrete (etyargs : etyarg list) (subue : unienv) =
    match List.rev etyargs with
    | [] -> false
    | (ty, _) :: _ ->
      let ty = ty_subst (Tuni.subst (UniEnv.assubst subue)) ty in
      match ty.ty_node with
      | Tconstr (p, _) -> begin
          match EcEnv.Ty.by_path_opt p env with
          | Some { tyd_type = `Abstract (_ :: _) } -> false
          | _ -> true
        end
      | _ -> false in
  List.filter (fun ((p, etyargs), _, subue, _) ->
    if not (is_tc_op p) then true
    else
      match EcEnv.Op.tc_reduce env p etyargs with
      | red -> begin
          let red_head =
            match red.f_node with
            | Fop (p', _) -> Some p'
            | Fapp ({ f_node = Fop (p', _) }, _) -> Some p'
            | _ -> None in
          match red_head with
          | None -> true
          | Some p' ->
            not (List.exists (EcPath.p_equal p') concrete_paths)
        end
      | exception EcEnv.NotReducible ->
        not (carrier_is_concrete etyargs subue)
  ) ops

(* Drop notation/abbrev candidates when a TC-op candidate sharing the
   same basename is also present. The [TcMonoid] family ships generic
   notation abbrevs like [abbrev ( * ) ['a <: mulmonoid] (x y) =
   (+)<:'a> x y] that, when applied at a [comring] carrier, expand to
   exactly the same [Fop] as comring's own [( * )] TC operator. The two
   are interchangeable but [select_op] returns both. *)
let drop_shadowed_notation (env : EcEnv.env) (ops : select_t) : select_t =
  let has_tc_op_with_name n =
    List.exists (fun ((p, _), _, _, _) ->
      match EcEnv.Op.by_path_opt p env with
      | Some { op_kind = OB_oper (Some (OP_TC _)) } ->
        EcPath.basename p = n
      | _ -> false) ops in
  List.filter (fun ((p, _), _, _, _) ->
    match EcEnv.Op.by_path_opt p env with
    | Some { op_kind = OB_nott _ } ->
      not (has_tc_op_with_name (EcPath.basename p))
    | _ -> true) ops

(* Catch the abbrev-to-TC-op case that [drop_subsumed_tc] misses:
   classify candidates by their post-inline body head, drop any whose
   body head is a TC op that [tc_reduce]s to a head already among the
   non-TC heads. *)
let drop_subsumed_by_post_inline_head (env : EcEnv.env) (ops : select_t)
    : select_t
=
  let is_tc_op p =
    match EcEnv.Op.by_path_opt p env with
    | Some { op_kind = OB_oper (Some (OP_TC _)) } -> true
    | _ -> false in
  let body_head ((path, etyargs), _, _, bd) =
    match bd with
    | None -> Some (path, etyargs)
    | Some bd_lazy ->
        let _, body = Lazy.force bd_lazy in
        let head, _ = EcTypes.destr_app body in
        (match head.e_node with
         | Eop (p, tys) -> Some (p, tys)
         | _ -> None) in
  let concrete_heads =
    List.filter_map (fun cand ->
      match body_head cand with
      | Some (p, _) when not (is_tc_op p) -> Some p
      | _ -> None) ops in
  if concrete_heads = [] then ops
  else
  List.filter (fun cand ->
    match body_head cand with
    | Some (p, etyargs) when is_tc_op p -> begin
        match EcEnv.Op.tc_reduce env p etyargs with
        | red ->
          let red_head =
            match red.f_node with
            | Fop (p', _) -> Some p'
            | Fapp ({ f_node = Fop (p', _) }, _) -> Some p'
            | _ -> None in
          (match red_head with
           | None -> true
           | Some p' -> not (List.exists (EcPath.p_equal p') concrete_heads))
        | exception EcEnv.NotReducible -> true
      end
    | _ -> true) ops

(* Drop a TC-bounded notation candidate (an abbrev whose tparams have
   non-empty TC bounds) when a same-basename candidate with no
   TC-bounded tparams is also present. *)
let drop_tc_bounded_notation (env : EcEnv.env) (ops : select_t) : select_t =
  let is_tc_bounded_nott p =
    match EcEnv.Op.by_path_opt p env with
    | Some { op_kind = OB_nott _; op_tparams = tparams } ->
      List.exists (fun (_, tcs) -> tcs <> []) tparams
    | _ -> false in
  let has_unbounded_with_name n =
    List.exists (fun ((p, _), _, _, _) ->
      EcPath.basename p = n
      && match EcEnv.Op.by_path_opt p env with
         | Some { op_tparams = tparams } ->
           not (List.exists (fun (_, tcs) -> tcs <> []) tparams)
         | None -> false) ops in
  List.filter (fun ((p, _), _, _, _) ->
    if is_tc_bounded_nott p
    then not (has_unbounded_with_name (EcPath.basename p))
    else true) ops

(* Run the candidate-deduplication chain. Each filter is followed by
   the [keep-all-on-empty] safeguard so a filter that would prune
   everything is treated as a no-op. *)
let canonicalize (env : EcEnv.env) (ops : select_t) : select_t =
  let step f ops =
    let pruned = f env ops in
    if pruned = [] then ops else pruned in
  ops
  |> step drop_subsumed_tc
  |> step drop_shadowed_notation
  |> step drop_tc_bounded_notation
  |> step drop_subsumed_by_post_inline_head
