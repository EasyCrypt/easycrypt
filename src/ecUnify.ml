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
    (* Map from UID to TC problems.                                 *)
    problems : (ty * typeclass) TcUni.Muid.t;

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
      (tcenv : tcenv)
      (ty    : ty)
      (tcw   : typeclass * tcwitness option)
    : tcenv * tcwitness
  =
    let tc, tw = tcw in
    let uid = TcUni.unique () in
    let deps = Tuni.univars ty in

    let tcenv = {
      problems = TcUni.Muid.add uid (ty, tc) tcenv.problems;
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

    tcenv, TCIUni (uid, 0)

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
            | None -> TCIUni (uid, 0)
            | Some (TCIUni (uid', _)) when TcUni.uid_equal uid uid' -> TCIUni (uid, 0)
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
  let subst_of_uf (uc : ucore) : unisubst =
    let close = close uc in

    let dereference_tyuni (uid : tyuni) =
      match close.tyuni (tuni uid) with
      | { ty_node = Tunivar uid' } when TyUni.uid_equal uid uid' -> None
      | ty -> Some ty in

    let dereference_tcuni (uid : tcuni) =
      match close.tcuni (TCIUni (uid, 0)) with
      | TCIUni (uid', _) when TcUni.uid_equal uid uid' -> None
      | tw -> Some tw in

    let uvars =
      let bindings =
        List.filter_map (fun uid ->
          Option.map (fun ty -> (uid, ty)) (dereference_tyuni uid)
        ) (UF.domain uc.uf) in
      TyUni.Muid.of_list bindings in

    let utcvars =
      let bindings =
        List.filter_map (fun uid ->
          Option.map (fun tw -> (uid, tw)) (dereference_tcuni uid)
        ) (TcUni.Muid.keys uc.tcenv.problems) in
      TcUni.Muid.of_list bindings in

    { uvars; utcvars; }

  (* -------------------------------------------------------------------- *)
  let check_closed (uc : ucore) =
    let tyvars = not (UF.closed uc.uf) in
    let tcvars = not (tcenv_closed uc.tcenv) in

    if tyvars || tcvars then
      raise (UninstanciateUni { tyvars; tcvars })

  (* ------------------------------------------------------------------ *)
  let fresh
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
        (fun tcenv tcw -> create_tcproblem tcenv ty tcw)
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
    TcUni.Muid.iter (fun uid (ty, tc) ->
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

        | _ -> EcTypes.ty_sub_exists doit t
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
            List.iter (fun (uid, (ty, tc)) -> Queue.push (`TcCtt (uid, ty, tc)) pb) tcpbs

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
                  if not (TyUni.uid_equal id1 id2) then
                    let effects =
                        reffold (fun uc ->
                          let uf, effects = UF.union id1 id2 uc.uf in
                          effects, { uc with uf }
                        ) uc in
                    List.iter (Queue.push^~ pb) effects
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

        | `TcCtt (uid, ty, tc) ->
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
          let eq_tc (tc' : typeclass) =
            let tc' = deref_tc tc' in
            EcPath.p_equal tc.tc_name tc'.tc_name
            && List.for_all2 (EcCoreEqTest.for_etyarg env) tc.tc_args tc'.tc_args in

          (* Find the offset of [tc] (or any of its ancestors) in [tcs];
             also return the number of [tc_prt] steps walked to reach
             [tc] from [tcs.(offset)]. [lift = 0] is a direct match. *)
          let match_tc_offset (tcs : typeclass list) : (int * int) option =
            let with_lift tc' =
              List.find_index eq_tc (EcTypeClass.ancestors env tc') in
            let rec scan i = function
              | [] -> None
              | tc' :: rest ->
                match with_lift tc' with
                | Some lift -> Some (i, lift)
                | None -> scan (i + 1) rest
            in scan 0 tcs in

          (* ---- Strategies (catalog modes) ----
             Each strategy returns [Some witness] when it resolves, or
             [None] when it does not apply / cannot decide. The dispatcher
             below tries them in priority order. *)

          (* Mode #5: carrier is [Tvar a] with a in [tvtc]. *)
          let strat_tvar_via_tvtc () : tcwitness option =
            match ty.ty_node with
            | Tvar a ->
              let tcs = ofdfl failure (Mid.find_opt a (!uc).tvtc) in
              let (offset, lift) = ofdfl failure (match_tc_offset tcs) in
              Some (TCIAbstract { support = `Var a; offset; lift })
            | _ -> None in

          (* Mode #6: carrier is [Tconstr p] with [p] an abstract decl. *)
          let strat_abs_via_decl () : tcwitness option =
            match ty.ty_node with
            | Tconstr (p, _) -> begin
              match EcEnv.Ty.by_path_opt p env with
              | Some { tyd_type = `Abstract tcs; _ } ->
                Option.map
                  (fun (offset, lift) ->
                    TCIAbstract { support = `Abs p; offset; lift })
                  (match_tc_offset tcs)
              | _ -> None
              end
            | _ -> None in

          (* Modes #1, #2: carrier is ground; query the instance database. *)
          let strat_infer_by_carrier () : tcwitness option =
            EcTypeClass.infer env ty tc in

          (* Univars appearing in [tc.tc_args] (types and witnesses).
             Used both for the Mode-#3 strategy gating and to register
             extra parking edges so the problem re-fires when one of
             them is resolved later. *)
          let etyarg_univars (a, ws) =
            let from_ty = Tuni.univars a in
            List.fold_left (fun s w ->
              TyUni.Suid.union s
                (EcTypes.tcw_fold
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
             TcCtt under Mode #1 and produce the concrete witness. *)
          let strat_infer_by_args () : tcwitness option =
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
            let resolution =
              match ty.ty_node with
              | Tvar _ ->
                ofdfl failure (strat_tvar_via_tvtc ())
              | Tconstr _ when Option.is_some (strat_abs_via_decl ()) ->
                Option.get (strat_abs_via_decl ())
              | _ ->
                ofdfl failure (strat_infer_by_carrier ())
            in
            uc := { !uc with tcenv = { (!uc).tcenv with resolution =
              TcUni.Muid.add uid resolution (!uc).tcenv.resolution
            } }
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
               resolution of [uid]. Hence [R = target] with [lift]
               removed from its lift count. *)
            let strip_lift n w =
              match w with
              | TCIUni (u, l) when l >= n ->
                Some (TCIUni (u, l - n))
              | TCIConcrete c when c.lift >= n ->
                Some (TCIConcrete { c with lift = c.lift - n })
              | TCIAbstract a when a.lift >= n ->
                Some (TCIAbstract { a with lift = a.lift - n })
              | _ -> None in
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

type petyarg = ty option * tcwitness option list option

type tvar_inst =
| TVIunamed of petyarg list
| TVInamed  of (EcSymbols.symbol * petyarg) list

type tvi = tvar_inst option

let tvi_unamed (ety : etyarg list) : tvar_inst =
  TVIunamed (List.map
    (fun (ty, tcw) -> Some ty, Some (List.map Option.some tcw))
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
    ?(tcs : (typeclass * tcwitness option) list option)
    ?(ty : ty option)
    (ue : unienv)
  =
    let (uc, tytw) = Unify.fresh ?tcs ?ty (!ue).ue_uc in
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

  let opentvi (ue : unienv) (params : ty_params) (tvi : tvi) : opened =
    let tvi =
      match tvi with
      | None ->
          List.map (fun (v, tcs) ->
            (v, (None, List.map (fun x -> (x, None)) tcs))
          ) params

      | Some (TVIunamed lt) ->
          let combine (v, tc) (ty, tcw) =
            let tctcw =
              match tcw with
              | None ->
                List.map (fun tc -> (tc, None)) tc
              | Some tcw ->
                List.combine tc tcw
            in (v, (ty, tctcw)) in

          List.map2 combine params lt

      | Some (TVInamed lt) ->
          List.map (fun (v, tc) ->
            let ty, tcw =
                 List.assoc_opt (EcIdent.name v) lt
              |> Option.value ~default:(None, None) in

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
        in Mid.add v (xfresh ?ty ~tcs ue) s
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

  let assubst (ue : unienv) : unisubst =
    Unify.subst_of_uf (!ue).ue_uc

  let close (ue : unienv) =
    Unify.check_closed (!ue).ue_uc;
    assubst ue

  let tparams (ue : unienv) =
    let subst = EcCoreSubst.f_subst_init ~tu:(assubst ue) () in
    let fortv x =
      let tvtc = odfl [] (Mid.find_opt x (!ue).ue_uc.tvtc) in
      List.map (EcCoreSubst.tc_subst subst) tvtc in
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
let tfun_expected (ue : unienv) (psig : ty list) =
  EcTypes.toarrow psig (UniEnv.fresh ue)

(* -------------------------------------------------------------------- *)
type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

(* -------------------------------------------------------------------- *)
type select_filter_t = EcPath.path -> operator -> bool

type select_t =
  ((EcPath.path * etyarg list) * ty * unienv * sbody option) list

let select_op
  ?(hidden : bool = false)
  ?(filter : select_filter_t = fun _ _ -> true)
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
              List.length tparams = len

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
      let UniEnv.{ subst = tip; args } =
        UniEnv.opentvi subue op.D.op_tparams tvi in
      let tip = f_subst_init ~tv:tip () in

      (*
      List.iter
        (fun (tv, tcs) ->
          try  hastcs_r env subue tv tcs
          with UnificationFailure _ -> raise E.Failure)
        tvtcs;
      *)

      let top = EcCoreSubst.ty_subst tip op.D.op_ty in
      let texpected = tfun_expected subue psig in

      (try  unify env subue top texpected
       with UnificationFailure _ -> raise E.Failure);

       let bd =
        match op.D.op_kind with
        | OB_nott nt ->
           let substnt () =
             let xs = List.map (snd_map (ty_subst tip)) nt.D.ont_args in
             let es = e_subst tip in
             let bd = es nt.D.ont_body in
             (xs, bd)
           in Some (Lazy.from_fun substnt)

        | _ -> None
      in

      Some ((path, args), top, subue, bd)

    with E.Failure -> None

  in
    List.pmap select (EcEnv.Op.all ~check:filter ~name env)
