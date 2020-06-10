(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
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
open EcGenRegexp

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
    z_path : ipath;                     (* path (zipper) leading to me         *)
  }

  let cpos (i : int) : codepos1 = (0, `ByPos i)

  let zipper hd tl zpr = { z_head = hd; z_tail = tl; z_path = zpr; }

  let find_by_cp_match ((i, cm) : int option * cp_match) (s : stmt) =
    let rec progress (acc : instr list) (s : instr list) (i : int) =
      if i <= 0 then
        let shd = oget (List.Exceptionless.hd acc) in
        let stl = oget (List.Exceptionless.tl acc) in
        (stl, shd, s)
      else

      let ir, s =
        match s with [] -> raise InvalidCPos | ir :: s -> (ir, s)
      in

      let i =
        match ir.i_node, cm with
        | Swhile _, `While  -> i-1
        | Sif    _, `If     -> i-1
        | Sasgn  _, `Assign -> i-1
        | Srnd   _, `Sample -> i-1
        | Scall  _, `Call   -> i-1
        | _       , _       -> i

      in progress (ir :: acc) s i

    in

    let i = odfl 1 i in if i = 0 then raise InvalidCPos;
    let rev, i = (i < 0), abs i in

    let s1, ir, s2 =
      progress [] (if rev then List.rev s.s_node else s.s_node) i in

    match rev with
    | false -> (s1, ir, s2)
    | true  -> (s2, ir, s1)

  let split_at_cp_base ~after (cb : cp_base) (s : stmt) =
    match cb with
    | `ByPos i -> begin
        let i = if i < 0 then List.length s.s_node + i else i in
        try  List.takedrop (i - if after then 0 else 1) s.s_node
        with (Invalid_argument _ | Not_found) -> raise InvalidCPos
      end

    | `ByMatch (i, cm) ->
        let (s1, i, s2) = find_by_cp_match (i, cm) s in

        match after with
        | false -> (List.rev s1, i :: s2)
        | true  -> (List.rev_append s1 [i], s2)

  let split_at_cpos1 ~after ((ipos, cb) : codepos1) s =
    let (s1, s2) = split_at_cp_base ~after cb s in

    let (s1, s2) =
      match ipos with
      | off when off > 0 ->
          let (ss1, ss2) =
            try  List.takedrop off s2
            with (Invalid_argument _ | Not_found) -> raise InvalidCPos in
          (s1 @ ss1, ss2)

      | off when off < 0 ->
          let (ss1, ss2) =
            try  List.takedrop (List.length s1 + off) s1
            with (Invalid_argument _ | Not_found) -> raise InvalidCPos in
          (ss1, ss2 @ s2)

      | _ -> (s1, s2)

    in (s1, s2)

  let find_by_cpos1 ?(rev = true) (cpos1 : codepos1) s =
    match split_at_cpos1 ~after:false cpos1 s with
    | (s1, i :: s2) -> ((if rev then List.rev s1 else s1), i, s2)
    | _ -> raise InvalidCPos

  let zipper_at_nm_cpos1 ((cp1, sub) : codepos1 * int) s zpr =
    let (s1, i, s2) = find_by_cpos1 cp1 s in

    match i.i_node, sub with
    | Swhile (e, sw), 0 ->
        (ZWhile (e, ((s1, s2), zpr)), sw)

    | Sif (e, ifs1, ifs2), 0 ->
        (ZIfThen (e, ((s1, s2), zpr), ifs2), ifs1)

    | Sif (e, ifs1, ifs2), 1 ->
        (ZIfElse (e, ifs1, ((s1, s2), zpr)), ifs2)

    | _ -> raise InvalidCPos

  let zipper_of_cpos ((nm, cp1) : codepos) s =
    let zpr, s =
      List.fold_left
        (fun (zpr, s) nm1 -> zipper_at_nm_cpos1 nm1 s zpr)
        (ZTop, s) nm in

    let s1, i, s2 = find_by_cpos1 cp1 s in

    zipper s1 (i :: s2) zpr

  let split_at_cpos1 cpos1 s =
    split_at_cpos1 ~after:true cpos1 s

  let may_split_at_cpos1 ?(rev = false) cpos1 s =
    ofdfl
      (fun () -> if rev then (s.s_node, []) else ([], s.s_node))
      (omap (split_at_cpos1^~ s) cpos1)

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

  let mem (x : ident) (m : 'a evmap) =
    EcUtils.is_some (Mid.find_opt x m.ev_map)

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

  let isset (x : ident) (m : 'a evmap) =
    match get x m with
    | Some (`Set _) -> true
    | _ -> false

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
    | `Form -> { empty with evm_form = EV.of_idents ids }
    | `Mem  -> { empty with evm_mem  = EV.of_idents ids }
    | `Mod  -> { empty with evm_mod  = EV.of_idents ids }

  let add x k m =
    match k with
    | `Form -> { m with evm_form = EV.add x m.evm_form }
    | `Mem  -> { m with evm_mem  = EV.add x m.evm_mem  }
    | `Mod  -> { m with evm_mod  = EV.add x m.evm_mod  }

  let mem x k m =
    match k with
    | `Form -> EV.mem x m.evm_form
    | `Mem  -> EV.mem x m.evm_mem
    | `Mod  -> EV.mem x m.evm_mod

  let set x v m =
    match v with
    | `Form v -> { m with evm_form = EV.set x v m.evm_form }
    | `Mem  v -> { m with evm_mem  = EV.set x v m.evm_mem  }
    | `Mod  v -> { m with evm_mod  = EV.set x v m.evm_mod  }

  let get x k m =
    let tx f = function `Unset -> `Unset | `Set x -> `Set (f x) in

    match k with
    | `Form -> omap (tx (fun x -> `Form x)) (EV.get x m.evm_form)
    | `Mem  -> omap (tx (fun x -> `Mem  x)) (EV.get x m.evm_mem )
    | `Mod  -> omap (tx (fun x -> `Mod  x)) (EV.get x m.evm_mod )

  let isset x k m =
    match k with
    | `Form -> EV.isset x m.evm_form
    | `Mem  -> EV.isset x m.evm_mem
    | `Mod  -> EV.isset x m.evm_mod

  let filled m =
       EV.filled m.evm_form
    && EV.filled m.evm_mem
    && EV.filled m.evm_mod

  let fold (f : _ -> item -> _ -> _) m v =
    let v = EV.fold (fun x k v -> f x (`Form k) v) m.evm_form v in
    let v = EV.fold (fun x k v -> f x (`Mem  k) v) m.evm_mem  v in
    let v = EV.fold (fun x k v -> f x (`Mod  k) v) m.evm_mod  v in
    v

  let assubst ue ev =
    let tysubst = { ty_subst_id with ts_u = EcUnify.UniEnv.assubst ue } in
    let subst = Fsubst.f_subst_init ~sty:tysubst () in
    let subst = EV.fold (fun x m s -> Fsubst.f_bind_mem s x m) ev.evm_mem subst in
    let subst = EV.fold (fun x m s -> Fsubst.f_bind_mod s x m) ev.evm_mod subst in
    let seen  = ref Sid.empty in

    let rec for_ident x binding subst =
      if Sid.mem x !seen then subst else begin
        seen := Sid.add x !seen;
        match binding with None -> subst | Some f ->
          let subst =
            Mid.fold2_inter (fun x bdx _ -> for_ident x bdx)
            ev.evm_form.ev_map f.f_fv subst in
          Fsubst.f_bind_local subst x (Fsubst.f_subst subst f)
        end
    in

    Mid.fold_left
      (fun acc x bd -> for_ident x bd acc)
      subst ev.evm_form.ev_map
end

(* -------------------------------------------------------------------- *)
exception MatchFailure

type fmoptions = {
  fm_delta  : bool;
  fm_conv   : bool;
  fm_horder : bool;
}

let fmsearch =
  { fm_delta  = false;
    fm_conv   = false;
    fm_horder = true ; }

let fmrigid = {
    fm_delta  = false;
    fm_conv   = true ;
    fm_horder = true ; }

let fmdelta = {
    fm_delta  = true ;
    fm_conv   = true ;
    fm_horder = true ; }

let fmnotation = {
    fm_delta  = false;
    fm_conv   = false;
    fm_horder = false; }

(* -------------------------------------------------------------------- *)
(* Rigid unification *)
let f_match_core opts hyps (ue, ev) ~ptn subject =
  let ue  = EcUnify.UniEnv.copy ue in
  let ev  = ref ev in

  let iscvar = function
    | { f_node = Flocal x } -> is_none (EV.get x !ev.evm_form)
    | _ -> false
  in

  let conv =
    match opts.fm_conv with
    | true  -> EcReduction.is_conv hyps
    | false -> EcReduction.is_alpha_eq hyps
  in

  let rec doit env ((subst, mxs) as ilc) ptn subject =
    let failure =
      let oue, oev = (EcUnify.UniEnv.copy ue, !ev) in
      fun () ->
        EcUnify.UniEnv.restore ~dst:ue ~src:oue; ev := oev;
        raise MatchFailure
    in

    let default () =
      if opts.fm_conv then begin
        let subject = Fsubst.f_subst subst subject in
        let ptn = Fsubst.f_subst (MEV.assubst ue !ev) ptn in
          if not (conv ptn subject) then
            failure ()
      end else failure ()
    in

    try
      match ptn.f_node, subject.f_node with
      | Flocal x1, Flocal x2 when Mid.mem x1 mxs -> begin
          if not (id_equal (oget (Mid.find_opt x1 mxs)) x2) then
            failure ();
          try  EcUnify.unify env ue ptn.f_ty subject.f_ty
          with EcUnify.UnificationFailure _ -> failure ()
      end

      | Flocal x1, Flocal x2 when id_equal x1 x2 -> begin
          try  EcUnify.unify env ue ptn.f_ty subject.f_ty
          with EcUnify.UnificationFailure _ -> failure ()
      end

      | Flocal x, _ -> begin
          match EV.get x !ev.evm_form with
          | None ->
              raise MatchFailure

          | Some `Unset ->
              let ssbj = Fsubst.f_subst subst subject in
              let ssbj = Fsubst.f_subst (MEV.assubst ue !ev) ssbj in
              if not (Mid.set_disjoint mxs ssbj.f_fv) then
                raise MatchFailure;
              begin
                try  EcUnify.unify env ue ptn.f_ty subject.f_ty
                with EcUnify.UnificationFailure _ -> failure ();
              end;
              ev := { !ev with evm_form = EV.set x ssbj !ev.evm_form }

          | Some (`Set a) -> begin
              let ssbj = Fsubst.f_subst subst subject in

              if not (conv ssbj a) then
                let ssbj = Fsubst.f_subst (MEV.assubst ue !ev) subject in
                if not (conv ssbj a) then
                  doit env ilc a ssbj
                else
                  try  EcUnify.unify env ue ptn.f_ty subject.f_ty
                  with EcUnify.UnificationFailure _ -> failure ()
              else
                try  EcUnify.unify env ue ptn.f_ty subject.f_ty
                with EcUnify.UnificationFailure _ -> failure ()
          end
      end

      | Fapp (f1, fs1), _ -> begin
        try
          match subject.f_node with
          | Fapp (f2, fs2) -> begin
              try  doit_args env ilc (f1::fs1) (f2::fs2)
              with MatchFailure when opts.fm_conv  ->
                let rptn = f_betared ptn in
                if   (ptn.f_tag <> rptn.f_tag)
                then doit env ilc rptn subject
                else failure ()
          end
          | _ -> failure ()

        with MatchFailure when opts.fm_horder ->
          match f1.f_node with
          | Flocal f when
                  not (Mid.mem f mxs)
               && (EV.get f !ev.evm_form = Some `Unset)
               && List.for_all iscvar fs1
            ->

            let oargs = List.map destr_local fs1 in

            if not (List.is_unique ~eq:id_equal oargs) then
              failure ();

            let xsubst, bindings =
              List.map_fold
                (fun xsubst x ->
                   let x, xty = (destr_local x, x.f_ty) in
                   let nx = EcIdent.fresh x in
                   let xsubst =
                     Mid.find_opt x mxs
                       |> omap (fun y -> Fsubst.f_bind_rename xsubst y nx xty)
                       |> odfl xsubst
                   in (xsubst, (nx, GTty xty)))
                Fsubst.f_subst_id fs1 in

            let ssbj = Fsubst.f_subst xsubst subject in
            let ssbj = Fsubst.f_subst  subst ssbj in

            if not (Mid.set_disjoint mxs ssbj.f_fv) then
              failure ();

            begin
              let fty = toarrow (List.map f_ty fs1) ssbj.f_ty in

              try  EcUnify.unify env ue f1.f_ty fty
              with EcUnify.UnificationFailure _ -> failure ();
            end;

            let ssbj = f_lambda bindings ssbj in

            ev := { !ev with evm_form = EV.set f ssbj !ev.evm_form }

          | _ -> default ()
      end

      | Fquant (b1, q1, f1), Fquant (b2, q2, f2) when b1 = b2 ->
          let n1, n2 = List.length q1, List.length q2 in
          let q1, r1 = List.split_at (min n1 n2) q1 in
          let q2, r2 = List.split_at (min n1 n2) q2 in
          let (env, subst, mxs) = doit_bindings env (subst, mxs) q1 q2 in
          doit env (subst, mxs) (f_quant b1 r1 f1) (f_quant b2 r2 f2)

      | Fquant _, Fquant _ ->
          failure ();

      | Fpvar (pv1, m1), Fpvar (pv2, m2) ->
          let pv1 = EcEnv.NormMp.norm_pvar env pv1 in
          let pv2 = EcEnv.NormMp.norm_pvar env pv2 in
            if not (EcTypes.pv_equal pv1 pv2) then
              failure ();
            doit_mem env mxs m1 m2

      | Fif (c1, t1, e1), Fif (c2, t2, e2) ->
          List.iter2 (doit env ilc) [c1; t1; e1] [c2; t2; e2]

      | Fmatch (b1, fs1, ty1), Fmatch (b2, fs2, ty2) -> begin
          (try  EcUnify.unify env ue ty1 ty2
           with EcUnify.UnificationFailure _ -> failure ());
          if List.length fs1 <> List.length fs2 then
            failure ();
          List.iter2 (doit env ilc) (b1 :: fs1) (b2 :: fs2)
        end

      | Fint i1, Fint i2 ->
          if not (EcBigInt.equal i1 i2) then failure ();

      | Fglob (mp1, me1), Fglob (mp2, me2) ->
          let mp1 = EcEnv.NormMp.norm_mpath env mp1 in
          let mp2 = EcEnv.NormMp.norm_mpath env mp2 in
            if not (EcPath.m_equal mp1 mp2) then
              failure ();
            doit_mem env mxs me1 me2

      | Ftuple fs1, Ftuple fs2 ->
          if List.length fs1 <> List.length fs2 then
            failure ();
          List.iter2 (doit env ilc) fs1 fs2

      | Fproj (f1, i), Fproj (f2, j) ->
          if i <> j then failure () else doit env ilc f1 f2

      | Fop (op1, tys1), Fop (op2, tys2) -> begin
          if not (EcPath.p_equal op1 op2) then
            failure ();
          try  List.iter2 (EcUnify.unify env ue) tys1 tys2
          with EcUnify.UnificationFailure _ -> failure ()
      end

      | FhoareF hf1, FhoareF hf2 -> begin
          if not (EcReduction.EqTest.for_xp env hf1.hf_f hf2.hf_f) then
            failure ();
          let mxs = Mid.add EcFol.mhr EcFol.mhr mxs in
          List.iter2 (doit env (subst, mxs))
            [hf1.hf_pr; hf1.hf_po] [hf2.hf_pr; hf2.hf_po]
      end

      | FbdHoareF hf1, FbdHoareF hf2 -> begin
          if not (EcReduction.EqTest.for_xp env hf1.bhf_f hf2.bhf_f) then
            failure ();
          if hf1.bhf_cmp <> hf2.bhf_cmp then
            failure ();
          let mxs = Mid.add EcFol.mhr EcFol.mhr mxs in
          List.iter2 (doit env (subst, mxs))
            [hf1.bhf_pr; hf1.bhf_po; hf1.bhf_bd]
            [hf2.bhf_pr; hf2.bhf_po; hf2.bhf_bd]
      end

      | FequivF hf1, FequivF hf2 -> begin
          if not (EcReduction.EqTest.for_xp env hf1.ef_fl hf2.ef_fl) then
            failure ();
          if not (EcReduction.EqTest.for_xp env hf1.ef_fr hf2.ef_fr) then
            failure();
          let mxs = Mid.add EcFol.mleft  EcFol.mleft  mxs in
          let mxs = Mid.add EcFol.mright EcFol.mright mxs in
          List.iter2
            (doit env (subst, mxs))
            [hf1.ef_pr; hf1.ef_po] [hf2.ef_pr; hf2.ef_po]
      end

      | Fpr pr1, Fpr pr2 -> begin
          if not (EcReduction.EqTest.for_xp env pr1.pr_fun pr2.pr_fun) then
            failure ();
          doit_mem env mxs pr1.pr_mem pr2.pr_mem;
          let mxs = Mid.add EcFol.mhr EcFol.mhr mxs in
          List.iter2
            (doit env (subst, mxs))
            [pr1.pr_args; pr1.pr_event] [pr2.pr_args; pr2.pr_event]
      end

      | _, _ -> default ()

    with MatchFailure when opts.fm_delta ->
      match fst_map f_node (destr_app ptn),
            fst_map f_node (destr_app subject)
      with
      | (Fop (op1, tys1), args1), (Fop (op2, tys2), args2) -> begin
(*          try
            if not (EcPath.p_equal op1 op2) then
              failure ();
            try
              List.iter2 (EcUnify.unify env ue) tys1 tys2;
              doit_args env ilc args1 args2
            with EcUnify.UnificationFailure _ -> failure ()
          with MatchFailure -> *)
(* Benj: Fixme user reduction ... *)
            if EcEnv.Op.reducible env op1 then
              doit_reduce env ((doit env ilc)^~ subject) ptn.f_ty op1 tys1 args1
            else if EcEnv.Op.reducible env op2 then
              doit_reduce env (doit env ilc ptn) subject.f_ty op2 tys2 args2
            else
              failure ()
      end

      | (Flocal x1, args1), _ when LDecl.can_unfold x1 hyps ->
          doit_lreduce env ((doit env ilc)^~ subject) ptn.f_ty x1 args1

      | _, (Flocal x2, args2) when LDecl.can_unfold x2 hyps ->
          doit_lreduce env (doit env ilc ptn) subject.f_ty x2 args2

      | (Fop (op1, tys1), args1), _ when EcEnv.Op.reducible env op1 ->
          doit_reduce env ((doit env ilc)^~ subject) ptn.f_ty op1 tys1 args1

      | _, (Fop (op2, tys2), args2) when EcEnv.Op.reducible env op2 ->
          doit_reduce env (doit env ilc ptn) subject.f_ty op2 tys2 args2

      | _, _ -> failure ()

  and doit_args env ilc fs1 fs2 =
    if List.length fs1 <> List.length fs2 then
      raise MatchFailure;
    List.iter2 (doit env ilc) fs1 fs2

  and doit_reduce env cb ty op tys args =
    let reduced =
      try  f_app (EcEnv.Op.reduce env op tys) args ty
      with NotReducible -> raise MatchFailure in
    cb (odfl reduced (EcReduction.h_red_opt EcReduction.beta_red hyps reduced))

  and doit_lreduce _env cb ty x args =
    let reduced =
      try  f_app (LDecl.unfold x hyps) args ty
      with LookupFailure _ -> raise MatchFailure in
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
              else Fsubst.f_bind_rename subst x2 x1 ty2

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

          | Fmatch (b, fs, _) ->
               doit pos (`WithCtxt (ctxt, b :: fs))

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
  let select_form ?(xconv = `Conv) ?(keyed = false) hyps o p target =
    let na = List.length (snd (EcFol.destr_app p)) in

    let kmatch key tp =
      match key, (fst (destr_app tp)).f_node with
      | `NoKey , _           -> true
      | `Path p, Fop (p', _) -> EcPath.p_equal p p'
      | `Path _, _           -> false
      | `Var  x, Flocal x'   -> id_equal x x'
      | `Var  _, _           -> false
    in

    let keycheck tp key = not keyed || kmatch key tp in

    let key =
      match (fst (destr_app p)).f_node with
      | Fop (p, _) -> `Path p
      | Flocal x   -> `Var x
      | _          -> `NoKey
    in

    let test xconv _ tp =
      if not (keycheck tp key) then `Continue else begin
        let (tp, ti) =
          match tp.f_node with
          | Fapp (h, hargs) when List.length hargs > na ->
              let (a1, a2) = List.takedrop na hargs in
                (f_app h a1 (toarrow (List.map f_ty a2) tp.f_ty), na)
          | _ -> (tp, -1)
        in
        if EcReduction.xconv xconv hyps p tp then `Accept ti else `Continue
      end

    in select ?o (test xconv) target

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

          | Fmatch (b, fs, ty) ->
              let bfs = doit p (b :: fs) in
              FSmart.f_match (fp, (b, fs, ty)) (List.hd bfs, List.tl bfs, ty)

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
    let tx fp = f_local x fp.f_ty in (x, map p tx f)
end

(* -------------------------------------------------------------------- *)
type cptenv = CPTEnv of f_subst

let can_concretize ev ue =
  EcUnify.UniEnv.closed ue && MEV.filled ev

(* -------------------------------------------------------------------------- *)
type regexp_instr = regexp1_instr gen_regexp

and regexp1_instr =
  | RAssign    (*of lvalue * expr*)
  | RSample    (*of lvalue * expr*)
  | RCall      (*of lvalue option * EcPath.xpath * expr list*)
  | RIf        of (*expr *) regexp_instr * regexp_instr
  | RWhile     of (*expr *) regexp_instr


module RegexpBaseInstr = struct
  open Zipper

  type regexp = regexp_instr
  type regexp1 = regexp1_instr

  type pos  = int
  type path = int list

  type subject = instr list

  type engine  = {
    e_zipper : zipper;
    e_pos    : pos;
    e_path   : pos list;
  }

  let mkengine (s : subject) = {
    e_zipper = zipper [] s ZTop;
    e_pos    = 0;
    e_path   = [];
  }

  let position (e : engine) =
    e.e_pos

  let at_start (e : engine) =
    List.is_empty e.e_zipper.z_head

  let at_end (e : engine) =
    List.is_empty e.e_zipper.z_tail

  let path (e : engine) =
    e.e_pos :: e.e_path

  let eat_option (f : 'a -> 'a -> unit) (x : 'a option) (xn : 'a option) =
    match x, xn with
    | None  , Some _ -> raise NoMatch
    | Some _, None   -> raise NoMatch
    | None  , None   -> ()
    | Some x, Some y -> f x y

  let eat_list (f : 'a -> 'a -> unit) (x : 'a list) (xn : 'a list) =
    try  List.iter2 f x xn
    with Invalid_argument _ -> raise NoMatch (* FIXME *)

  let eat_lvalue (lv : lvalue) (lvn : lvalue) =
    if not (lv_equal lv lvn) then raise NoMatch

  let eat_expr (e : expr) (en : expr) =
    if not (e_equal e en) then raise NoMatch

  let eat_xpath (f : EcPath.xpath) (fn : EcPath.xpath) =
    if not (EcPath.x_equal f fn) then raise NoMatch

  let rec eat_base (eng : engine) (r : regexp1) =
    let z = eng.e_zipper in

    match z.z_tail with
    | [] -> raise NoMatch

    | i :: tail -> begin
       match (i.i_node,r) with
       | Sasgn _, RAssign
       | Srnd  _, RSample
       | Scall _, RCall   -> (eat eng, [])

       | Sif (e, st, sf), RIf (stn, sfn) -> begin
           let e_t = mkengine st.s_node in
           let e_t =
             let zp = ZIfThen (e, ((z.z_head, tail), z.z_path), sf) in
             let zp = { e_t.e_zipper with z_path = zp; } in
             { e_t with e_path = 0 :: eng.e_pos :: eng.e_path; e_zipper = zp; } in

           let e_f = mkengine sf.s_node in
           let e_f =
             let zp = ZIfElse (e, st, ((z.z_head, tail), z.z_path)) in
             let zp = { e_f.e_zipper with z_path = zp; } in
             { e_f with e_path = 1 :: eng.e_pos :: eng.e_path; e_zipper = zp; } in

           (eat eng, [(e_t, stn); (e_f, sfn)])
         end

       | Swhile (e, s), RWhile sn -> begin
            let es = mkengine s.s_node in
            let es =
              let zp = ZWhile (e, ((z.z_head, tail), z.z_path)) in
              let zp = { es.e_zipper with z_path = zp; } in
              { es with e_path = 0 :: eng.e_pos :: eng.e_path; e_zipper = zp; }  in

            (eat eng, [(es, sn)])
         end

       | _, _ -> raise NoMatch
     end

  and eat (e : engine) = {
    e with e_zipper = zip_eat e.e_zipper;
           e_pos    = e.e_pos + 1;
  }

  and zip_eat (z : zipper) =
    match z.z_tail with
    | []        -> raise NoMatch
    | i :: tail -> zipper (i :: z.z_head) tail z.z_path

  let extract (e : engine) ((lo, hi) : pos * pos) =
    if hi <= lo then [] else

    let s = List.rev_append e.e_zipper.z_head e.e_zipper.z_tail in
    List.of_enum (List.enum s |> Enum.skip lo |> Enum.take (hi-lo))

  let rec next_zipper (z : zipper) =
    match z.z_tail with
    | i :: tail ->
       begin match i.i_node with
       | Sif (e, stmttrue, stmtfalse) ->
          let z = (i::z.z_head, tail), z.z_path in
          let path = ZIfThen (e, z, stmtfalse) in
          let z' = zipper [] stmttrue.s_node path in
          Some z'

       | Swhile (e, block) ->
          let z = (i::z.z_head, tail), z.z_path in
          let path = ZWhile (e, z) in
          let z' = zipper [] block.s_node path in
          Some z'

       | Sasgn _ | Srnd _ | Scall _ | _ ->
          Some { z with z_head = i :: z.z_head ; z_tail = tail }
       end

    | [] ->
       match z.z_path with
       | ZTop -> None

       | ZWhile (_e, ((head, tail), path)) ->
          let z' = zipper head tail path in
          next_zipper z'

       | ZIfThen (e, father, stmtfalse) ->
          let stmttrue = stmt (List.rev z.z_head) in
          let z' = zipper [] stmtfalse.s_node (ZIfElse (e, stmttrue, father)) in
          next_zipper z'

       | ZIfElse (_e, _stmttrue, ((head, tail), path)) ->
          let z' = zipper head tail path in
          next_zipper z'

  let next (e : engine) =
    next_zipper e.e_zipper |> omap (fun z ->
      { e with e_zipper = z; e_pos = List.length z.z_head })
end

module RegexpStmt = EcGenRegexp.Regexp(RegexpBaseInstr)
