(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* Expressions / formulas matching for tactics                          *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcIdent
open EcParsetree
open EcEnv
open EcTypes
open EcModules
open EcFol
open EcBaseLogic

(* -------------------------------------------------------------------- *)
module Zipper = struct
  exception InvalidCPos

  module P = EcPath

  type ('a, 'state) folder =
    'a -> 'state -> instr -> 'state * instr list

  type ipath =
  | ZTop
  | ZWhile  of expr * spath
  | ZIfThen of expr * spath * stmt
  | ZIfElse of expr * stmt  * spath

  and spath = (instr list * instr list) * ipath

  type zipper = {
    z_head : instr list;                (* instructions on my left (rev)       *)
    z_tail : instr list;                (* instructions on my right (me incl.) *)
    z_path : ipath ;                    (* path (zipper) leading to me         *)
  }

  let zipper hd tl zpr = { z_head = hd; z_tail = tl; z_path = zpr; }

  let rec zipper_of_cpos ((i, sub) : codepos) zpr s =
    let (s1, i, s2) =
      try  List.pivot_at (i-1) s.s_node
      with Invalid_argument _ -> raise InvalidCPos
    in
    match sub with
    | None -> zipper s1 (i::s2) zpr
    | Some (b, sub) -> begin
      match i.i_node, b with
      | Swhile (e, sw), 0 ->
          zipper_of_cpos sub (ZWhile (e, ((s1, s2), zpr))) sw
      | Sif (e, ifs1, ifs2), 0 ->
          zipper_of_cpos sub (ZIfThen (e, ((s1, s2), zpr), ifs2)) ifs1
      | Sif (e, ifs1, ifs2), 1 ->
          zipper_of_cpos sub (ZIfElse (e, ifs1, ((s1, s2), zpr))) ifs2
      | _ -> raise InvalidCPos
    end

  let zipper_of_cpos cpos s = zipper_of_cpos cpos ZTop s

  let rec zip i ((hd, tl), ip) =
    let s = stmt (List.rev_append hd (List.ocons i tl)) in

    match ip with
    | ZTop -> s
    | ZWhile  (e, sp)     -> zip (Some (i_while (e, s))) sp
    | ZIfThen (e, sp, se) -> zip (Some (i_if (e, s, se))) sp
    | ZIfElse (e, se, sp) -> zip (Some (i_if (e, se, s))) sp

  let zip zpr = zip None ((zpr.z_head, zpr.z_tail), zpr.z_path)

  let after ~strict zpr =
    let rec doit acc ip =
      match ip with
      | ZTop                          -> acc
      | ZWhile  (_, ((_, is), ip))    -> doit (is :: acc) ip
      | ZIfThen (_, ((_, is), ip), _) -> doit (is :: acc) ip
      | ZIfElse (_, _, ((_, is), ip)) -> doit (is :: acc) ip
    in

    let after =
      match zpr.z_tail, strict with
      | []     , _     -> doit [[]] zpr.z_path
      | is     , false -> doit [is] zpr.z_path
      | _ :: is, true  -> doit [is] zpr.z_path
    in
      List.rev after

  let rec fold env cpos f state s =
    let zpr = zipper_of_cpos cpos s in

      match zpr.z_tail with
      | []      -> raise InvalidCPos
      | i :: tl -> begin
          match f env state i with
          | (state', [i']) when i == i' && state == state' -> (state, s)
          | (state', si  ) -> (state', zip { zpr with z_tail = si @ tl })
      end
end

(* -------------------------------------------------------------------- *)
type 'a evmap = {
  ev_map   : ('a option) Mid.t;
  ev_unset : int;
}

module EV = struct
  let empty : 'a evmap = {
    ev_map   = Mid.empty;
    ev_unset = 0;
  }

  let add (x : ident) (m : 'a evmap) =
    let chg = function Some _ -> assert false | None -> Some None in
    let map = Mid.change chg x m.ev_map in
    { ev_map = map; ev_unset = m.ev_unset + 1; }

  let set (x : ident) (v : 'a) (m : 'a evmap) =
    let chg = function
      | None | Some (Some _) -> assert false
      | Some None -> Some (Some v)
    in
      { ev_map = Mid.change chg x m.ev_map; ev_unset = m.ev_unset - 1; }

  let get (x : ident) (m : 'a evmap) =
    match Mid.find_opt x m.ev_map with
    | None          -> None
    | Some None     -> Some `Unset
    | Some (Some a) -> Some (`Set a)

  let doget (x : ident) (m : 'a evmap) =
    match get x m with
    | Some (`Set a) -> a
    | _ -> assert false

  let of_idents (ids : ident list) : 'a evmap =
    List.fold_left ((^~) add) empty ids

  let fold (f : ident -> 'a -> 'b -> 'b) ev state =
    Mid.fold
      (fun x t s -> match t with Some t -> f x t s | None -> s)
      ev.ev_map state

  let filled (m : 'a evmap) = (m.ev_unset = 0)
end

(* -------------------------------------------------------------------- *)
type mevmap = {
  evm_form : form            evmap;
  evm_mem  : EcMemory.memory evmap;
  evm_mod  : EcPath.mpath    evmap;
}

(* -------------------------------------------------------------------- *)
module MEV = struct
  type item = [
    | `Form of form
    | `Mem  of EcMemory.memory
    | `Mod  of EcPath.mpath
  ]

  type kind = [ `Form | `Mem | `Mod ]

  let empty : mevmap = {
    evm_form = EV.empty;
    evm_mem  = EV.empty;
    evm_mod  = EV.empty;
  }

  let of_idents ids k =
    match k with
    | `Form -> { empty with evm_form = EV.of_idents ids; }
    | `Mem  -> { empty with evm_mem  = EV.of_idents ids; }
    | `Mod  -> { empty with evm_mod  = EV.of_idents ids; }

  let add x k m =
    match k with
    | `Form -> { m with evm_form = EV.add x m.evm_form }
    | `Mem  -> { m with evm_mem  = EV.add x m.evm_mem  }
    | `Mod  -> { m with evm_mod  = EV.add x m.evm_mod  }

  let filled m =
       EV.filled m.evm_form
    && EV.filled m.evm_mem
    && EV.filled m.evm_mod

  let fold (f : _ -> item -> _ -> _) m v =
    let v = EV.fold (fun x k v -> f x (`Form k) v) m.evm_form v in
    let v = EV.fold (fun x k v -> f x (`Mem  k) v) m.evm_mem  v in
    let v = EV.fold (fun x k v -> f x (`Mod  k) v) m.evm_mod  v in
    v
end

(* -------------------------------------------------------------------- *)
exception MatchFailure

type fmoptions = {
  fm_delta : bool;
}

let fmrigid = { fm_delta = false; }
let fmdelta = { fm_delta = true ; }

(* Rigid unification *)
let f_match_core opts hyps (ue, ev) ~ptn subject =
  let ue  = EcUnify.UniEnv.copy ue in
  let ev  = ref ev in

  let rec doit env ((subst, mxs) as ilc) ptn subject =
    try
      match ptn.f_node, subject.f_node with
      | Flocal x1, Flocal x2 when Mid.mem x1 mxs -> begin
          if not (id_equal (oget (Mid.find_opt x1 mxs)) x2) then
            raise MatchFailure;
          try  EcUnify.unify env ue ptn.f_ty subject.f_ty
          with EcUnify.UnificationFailure _ -> raise MatchFailure
      end

      | Flocal x1, Flocal x2 when id_equal x1 x2 -> begin
          try  EcUnify.unify env ue ptn.f_ty subject.f_ty
          with EcUnify.UnificationFailure _ -> raise MatchFailure
      end

      | Flocal x, _ -> begin
          match EV.get x !ev.evm_form with
          | None ->
              raise MatchFailure

          | Some `Unset ->
              let ssbj = Fsubst.f_subst subst subject in
              if not (Mid.set_disjoint mxs ssbj.f_fv) then
                raise MatchFailure;
              begin
                try  EcUnify.unify env ue ptn.f_ty subject.f_ty
                with EcUnify.UnificationFailure _ -> raise MatchFailure;
              end;
              ev := { !ev with evm_form = EV.set x ssbj !ev.evm_form }

          | Some (`Set a) -> begin
              let ssbj = Fsubst.f_subst subst subject in
              if not (EcReduction.is_conv hyps ssbj a) then
                raise MatchFailure;
              try  EcUnify.unify env ue ptn.f_ty subject.f_ty
              with EcUnify.UnificationFailure _ -> raise MatchFailure
          end
      end

      | Fquant (b1, q1, f1), Fquant (b2, q2, f2)
          when b1 = b2 && List.length q1 = List.length q2
        ->
        let (env, subst, mxs) = doit_bindings env (subst, mxs) q1 q2 in
          doit env (subst, mxs) f1 f2

      | Fquant _, Fquant _ ->
          raise MatchFailure

      | Fpvar (pv1, m1), Fpvar (pv2, m2) ->
          let pv1 = EcEnv.NormMp.norm_pvar env pv1 in
          let pv2 = EcEnv.NormMp.norm_pvar env pv2 in
            if not (EcTypes.pv_equal pv1 pv2) then
              raise MatchFailure;
            doit_mem env mxs m1 m2

      | Fif (c1, t1, e1), Fif (c2, t2, e2) ->
          List.iter2 (doit env ilc) [c1; t1; e1] [c2; t2; e2]

      | Fint i1, Fint i2 ->
          if i1 <> i2 then raise MatchFailure

      | Fapp (f1, fs1), Fapp (f2, fs2) ->
          doit_args env ilc (f1::fs1) (f2::fs2)

      | Fglob (mp1, me1), Fglob (mp2, me2) ->
          let mp1 = EcEnv.NormMp.norm_mpath env mp1 in
          let mp2 = EcEnv.NormMp.norm_mpath env mp2 in
            if not (EcPath.m_equal mp1 mp2) then
              raise MatchFailure;
            doit_mem env mxs me1 me2

      | Ftuple fs1, Ftuple fs2 ->
          if List.length fs1 <> List.length fs2 then
            raise MatchFailure;
          List.iter2 (doit env ilc) fs1 fs2

      | Fop (op1, tys1), Fop (op2, tys2) -> begin
          if not (EcPath.p_equal op1 op2) then
            raise MatchFailure;
          try  List.iter2 (EcUnify.unify env ue) tys1 tys2
          with EcUnify.UnificationFailure _ -> raise MatchFailure
      end

      | _, _ ->
        let subject = Fsubst.f_subst subst subject in
          if not (EcReduction.is_conv hyps ptn subject) then
            raise MatchFailure

    with MatchFailure when opts.fm_delta ->
      match fst_map f_node (destr_app ptn),
            fst_map f_node (destr_app subject)
      with
      | (Fop (op1, tys1), args1), (Fop (op2, tys2), args2) -> begin
          try
            if not (EcPath.p_equal op1 op2) then
              raise MatchFailure;
            try
              List.iter2 (EcUnify.unify env ue) tys1 tys2;
              doit_args env ilc args1 args2
            with EcUnify.UnificationFailure _ -> raise MatchFailure
          with MatchFailure ->
            if EcEnv.Op.reducible env op1 then
              doit_reduce env ((doit env ilc)^~ subject) ptn.f_ty op1 tys1 args1
            else if EcEnv.Op.reducible env op2 then
              doit_reduce env (doit env ilc ptn) subject.f_ty op2 tys2 args2
            else
              raise MatchFailure
      end

      | (Fop (op1, tys1), args1), _ when EcEnv.Op.reducible env op1 ->
          doit_reduce env ((doit env ilc)^~ subject) ptn.f_ty op1 tys1 args1

      | _, (Fop (op2, tys2), args2) when EcEnv.Op.reducible env op2 ->
          doit_reduce env (doit env ilc ptn) subject.f_ty op2 tys2 args2

      | _, _ -> raise MatchFailure

  and doit_args env ilc fs1 fs2 =
    if List.length fs1 <> List.length fs2 then
      raise MatchFailure;
    List.iter2 (doit env ilc) fs1 fs2

  and doit_reduce env cb ty op tys f =
    let reduced =
      try  f_app (EcEnv.Op.reduce env op tys) f ty
      with NotReducible -> raise MatchFailure
    in
      cb (odfl reduced (EcReduction.h_red_opt EcReduction.beta_red hyps reduced))

  and doit_mem _env mxs m1 m2 =
    match EV.get m1 !ev.evm_mem with
    | None ->
        if not (EcMemory.mem_equal m1 m2) then
          raise MatchFailure

    | Some `Unset ->
        if Mid.mem m2 mxs then
          raise MatchFailure;
        ev := { !ev with evm_mem = EV.set m1 m2 !ev.evm_mem }

    | Some (`Set m1) ->
        if not (EcMemory.mem_equal m1 m2) then
          raise MatchFailure

  and doit_bindings env (subst, mxs) q1 q2 =
    let doit_binding (env, subst, mxs) (x1, gty1) (x2, gty2) =
      let gty2 = Fsubst.gty_subst subst gty2 in

      assert (not (Mid.mem x1 mxs) && not (Mid.mem x2 mxs));

      let env, subst =
        match gty1, gty2 with
        | GTty ty1, GTty ty2 ->
            begin
              try  EcUnify.unify env ue ty1 ty2
              with EcUnify.UnificationFailure _ -> raise MatchFailure
            end;

            let subst =
              if   id_equal x1 x2
              then subst
              else Fsubst.f_bind_local subst x2 (f_local x1 ty2)

            and env = EcEnv.Var.bind_local x1 ty1 env in

            (env, subst)

        | GTmem None, GTmem None ->
            (env, subst)

        | GTmem (Some m1), GTmem (Some m2) ->
            let xp1 = EcMemory.lmt_xpath m1 in
            let xp2 = EcMemory.lmt_xpath m2 in
            let m1  = EcMemory.lmt_bindings m1 in
            let m2  = EcMemory.lmt_bindings m2 in

            if not (EcPath.x_equal xp1 xp2) then
              raise MatchFailure;
            if not (
              try
                EcSymbols.Msym.equal
                  (fun (p1,ty1) (p2,ty2) ->
                    if p1 <> p2 then raise MatchFailure;
                    EcUnify.unify env ue ty1 ty2; true)
                  m1 m2
              with EcUnify.UnificationFailure _ -> raise MatchFailure)
            then
              raise MatchFailure;

            let subst =
              if   id_equal x1 x2
              then subst
              else Fsubst.f_bind_mem subst x2 x1
            in (env, subst)

        | GTmodty (p1, r1), GTmodty (p2, r2) ->
            if not (ModTy.mod_type_equiv env p1 p2) then
              raise MatchFailure;
            if not (NormMp.equal_restr env r1 r2) then
              raise MatchFailure;

            let subst =
              if   id_equal x1 x2
              then subst
              else Fsubst.f_bind_mod subst x2 (EcPath.mident x1)

            and env = EcEnv.Mod.bind_local x1 p1 r1 env in

            (env, subst)

        | _, _ -> raise MatchFailure
      in
        (env, subst, Mid.add x1 x2 mxs)
    in
      List.fold_left2 doit_binding (env, subst, mxs) q1 q2

  in
    doit (EcEnv.LDecl.toenv hyps) (Fsubst.f_subst_id, Mid.empty) ptn subject;
    (ue, !ev)

let f_match opts hyps (ue, ev) ~ptn subject =
  let (ue, ev) = f_match_core opts hyps (ue, ev) ~ptn subject in
    if not (MEV.filled ev) then
      raise MatchFailure;
    let clue =
      try  EcUnify.UniEnv.close ue
      with EcUnify.UninstanciateUni -> raise MatchFailure
    in
      (ue, clue, ev)

(* -------------------------------------------------------------------- *)
type ptnpos = [`Select of int | `Sub of ptnpos] Mint.t
type occ    = [`Inclusive | `Exclusive] * Sint.t

exception InvalidPosition
exception InvalidOccurence

module FPosition = struct
  type select = [`Accept of int | `Continue]

  (* ------------------------------------------------------------------ *)
  let empty : ptnpos = Mint.empty

  (* ------------------------------------------------------------------ *)
  let is_empty (p : ptnpos) = Mint.is_empty p

  (* ------------------------------------------------------------------ *)
  let rec tostring (p : ptnpos) =
    let items = Mint.bindings p in
    let items =
      List.map
        (fun (i, p) -> Printf.sprintf "%d[%s]" i (tostring1 p))
        items
    in
      String.concat ", " items

  (* ------------------------------------------------------------------ *)
  and tostring1 = function
    | `Select i when i < 0 -> "-"
    | `Select i -> Printf.sprintf "-(%d)" i
    | `Sub p -> tostring p

  (* ------------------------------------------------------------------ *)
  let occurences =
    let rec doit1 n p =
      match p with
      | `Select _ -> n+1
      | `Sub p    -> doit n p

    and doit n (ps : ptnpos) =
      Mint.fold (fun _ p n -> doit1 n p) ps n

    in
      fun p -> doit 0 p

  (* ------------------------------------------------------------------ *)
  let filter ((mode, s) : occ) =
    let rec doit1 n p =
      match p with
      | `Select _ -> begin
        match mode with
        | `Inclusive -> (n+1, if Sint.mem n s then Some p else None  )
        | `Exclusive -> (n+1, if Sint.mem n s then None   else Some p)
      end

      | `Sub p  -> begin
          match doit n p with
          | (n, sub) when Mint.is_empty sub -> (n, None)
          | (n, sub) -> (n, Some (`Sub sub))
      end

    and doit n (ps : ptnpos) =
      Mint.mapi_filter_fold (fun _ p n -> doit1 n p) ps n

    in
      fun p -> snd (doit 1 p)

  (* ------------------------------------------------------------------ *)
  let is_occurences_valid o cpos =
    let (min, max) = (Sint.min_elt o, Sint.max_elt o) in
      not (min < 1 || max > occurences cpos)

  (* ------------------------------------------------------------------ *)
  let select ?o test =
    let rec doit1 ctxt pos fp =
      match test ctxt fp with
      | `Accept i -> Some (`Select i)
      | `Continue -> begin
        let subp =
          match fp.f_node with
          | Fif    (c, f1, f2) -> doit pos (`WithCtxt (ctxt, [c; f1; f2]))
          | Fapp   (f, fs)     -> doit pos (`WithCtxt (ctxt, f :: fs))
          | Ftuple fs          -> doit pos (`WithCtxt (ctxt, fs))

          | Fquant (_, b, f) ->
              let xs   = List.pmap (function (x, GTty _) -> Some x | _ -> None) b in
              let ctxt = List.fold_left ((^~) Sid.add) ctxt xs in
              doit pos (`WithCtxt (ctxt, [f]))

          | Flet (lp, f1, f2) ->
              let subctxt = List.fold_left ((^~) Sid.add) ctxt (lp_ids lp) in
              doit pos (`WithSubCtxt [(ctxt, f1); (subctxt, f2)])

          | Fproj (f, _) ->
              doit pos (`WithCtxt (ctxt, [f]))

          | Fpr pr ->
              let subctxt = Sid.add pr.pr_mem ctxt in
              doit pos (`WithSubCtxt [(ctxt, pr.pr_args); (subctxt, pr.pr_event)])

          | FhoareF hs ->
              doit pos (`WithCtxt (Sid.add EcFol.mhr ctxt, [hs.hf_pr; hs.hf_po]))

          | FbdHoareF hs ->
              let subctxt = Sid.add EcFol.mhr ctxt in
              doit pos (`WithSubCtxt ([(subctxt, hs.bhf_pr);
                                       (subctxt, hs.bhf_po);
                                       (   ctxt, hs.bhf_bd)]))

          | FequivF es ->
              let ctxt = Sid.add EcFol.mleft  ctxt in
              let ctxt = Sid.add EcFol.mright ctxt in
              doit pos (`WithCtxt (ctxt, [es.ef_pr; es.ef_po]))

          | _ -> None
        in
          omap (fun p -> `Sub p) subp
      end

    and doit pos fps =
      let fps =
        match fps with
        | `WithCtxt (ctxt, fps) ->
            List.mapi
              (fun i fp ->
                doit1 ctxt (i::pos) fp |> omap (fun p -> (i, p)))
              fps

        | `WithSubCtxt fps ->
            List.mapi
              (fun i (ctxt, fp) ->
                doit1 ctxt (i::pos) fp |> omap (fun p -> (i, p)))
              fps
      in

      let fps = List.pmap identity fps in
        match fps with
        | [] -> None
        | _  -> Some (Mint.of_list fps)

    in
      fun fp ->
        let cpos =
          match doit [] (`WithCtxt (Sid.empty, [fp])) with
          | None   -> Mint.empty
          | Some p -> p
        in
          match o with
          | None   -> cpos
          | Some o ->
            if not (is_occurences_valid (snd o) cpos) then
              raise InvalidOccurence;
            filter o cpos

  (* ------------------------------------------------------------------ *)
  let select_form hyps o p target =
    let na = List.length (snd (EcFol.destr_app p)) in
    let test _ tp =
      let (tp, ti) =
        match tp.f_node with
        | Fapp (h, hargs) when List.length hargs > na ->
            let (a1, a2) = List.takedrop na hargs in
              (f_app h a1 (toarrow (List.map f_ty a2) tp.f_ty), na)
        | _ -> (tp, -1)
      in
      if EcReduction.is_conv hyps p tp then `Accept ti else `Continue

    in select ?o test target

  (* ------------------------------------------------------------------ *)
  let map (p : ptnpos) (tx : form -> form) (f : form) =
    let rec doit1 p fp =
      match p with
      | `Select i when i < 0 -> tx fp

      | `Select i -> begin
          let (f, fs) = EcFol.destr_app fp in
            if List.length fs < i then raise InvalidPosition;
            let (fs1, fs2) = List.takedrop i fs in
            let f' = f_app f fs1 (toarrow (List.map f_ty fs2) fp.f_ty) in
              f_app (tx f') fs2 fp.f_ty
        end

      | `Sub p    -> begin
          match fp.f_node with
          | Flocal _ -> raise InvalidPosition
          | Fpvar  _ -> raise InvalidPosition
          | Fglob  _ -> raise InvalidPosition
          | Fop    _ -> raise InvalidPosition
          | Fint   _ -> raise InvalidPosition

          | Fquant (q, b, f) ->
              let f' = as_seq1 (doit p [f]) in
                FSmart.f_quant (fp, (q, b, f)) (q, b, f')

          | Fif (c, f1, f2)  ->
              let (c', f1', f2') = as_seq3 (doit p [c; f1; f2]) in
                FSmart.f_if (fp, (c, f1, f2)) (c', f1', f2')

          | Fapp (f, fs) -> begin
              match doit p (f :: fs) with
              | [] -> assert false
              | f' :: fs' ->
                  FSmart.f_app (fp, (f, fs, fp.f_ty)) (f', fs', fp.f_ty)
          end

          | Ftuple fs ->
              let fs' = doit p fs in
                FSmart.f_tuple (fp, fs) fs'

          | Fproj (f, i) ->
              FSmart.f_proj (fp, (f, fp.f_ty)) (as_seq1 (doit p [f]), fp.f_ty) i

          | Flet (lv, f1, f2) ->
              let (f1', f2') = as_seq2 (doit p [f1; f2]) in
                FSmart.f_let (fp, (lv, f1, f2)) (lv, f1', f2')

          | Fpr pr ->
              let (args', event') = as_seq2 (doit p [pr.pr_args; pr.pr_event]) in
              f_pr pr.pr_mem pr.pr_fun args' event'

          | FhoareF hf ->
              let (hf_pr, hf_po) = as_seq2 (doit p [hf.hf_pr; hf.hf_po]) in
              f_hoareF_r { hf with hf_pr; hf_po; }

          | FbdHoareF hf ->
              let sub = doit p [hf.bhf_pr; hf.bhf_po; hf.bhf_bd] in
              let (bhf_pr, bhf_po, bhf_bd) = as_seq3 sub in
              f_bdHoareF_r { hf with bhf_pr; bhf_po; bhf_bd; }

          | FequivF ef ->
              let (ef_pr, ef_po) = as_seq2 (doit p [ef.ef_pr; ef.ef_po]) in
              f_equivF_r { ef with ef_pr; ef_po; }

          | FhoareS   _ -> raise InvalidPosition
          | FbdHoareS _ -> raise InvalidPosition
          | FequivS   _ -> raise InvalidPosition
          | FeagerF   _ -> raise InvalidPosition
      end

    and doit ps fps =
      match Mint.is_empty ps with
      | true  -> fps
      | false ->
          let imin = fst (Mint.min_binding ps)
          and imax = fst (Mint.max_binding ps) in
          if imin < 0 || imax >= List.length fps then
            raise InvalidPosition;
          let fps = List.mapi (fun i x -> (x, Mint.find_opt i ps)) fps in
          let fps = List.map (function (f, None) -> f | (f, Some p) -> doit1 p f) fps in
            fps

    in
      as_seq1 (doit p [f])

  (* ------------------------------------------------------------------ *)
  let topattern ?x (p : ptnpos) (f : form) =
    let x = match x with None -> EcIdent.create "_p" | Some x -> x in
    let tx fp = f_local x fp.f_ty in

      (x, map p tx f)
end
