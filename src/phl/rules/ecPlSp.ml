(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Strongest-postcondition calculus, shared by the [sp] rules of every
   logic (it is part of their trusted subgoal builders).

   SP carries three elements,
     - bds: a set of existential binders
     - assoc: a set of pairs (x,e) such that x=e holds
              for instance after an assignment x <- e
     - pre: the actual precondition (progressively weakened)

   After an assignment of the form x <- e the three elements are updated:
     1) a new fresh local x' is added to the list of existential binders
     2) (x, e) is added to the assoc list, and every other (y,d) is replaced
        by (y[x->x'], d[x->x'])
     3) pre is replaced by pre[x->x']

   The simplification of this version comes from one trick: the
   replacement of (y[x->x']) introduces a simplification opportunity.
   There is no need to keep (x', d[x->x']) as a conjuction
   x' = d[x->x']: it is enough to perform the substitution of d[x->x']
   for x' in place (it is a mess however to implement this idea with
   simultaneous assigns). *)

(* -------------------------------------------------------------------- *)
exception No_sp

(* -------------------------------------------------------------------- *)
type assignable =
| APVar  of (prog_var  * ty)
| ALocal of (EcIdent.t * ty)

and assignables = assignable list

(* -------------------------------------------------------------------- *)
let sp_asgn ?mc (memenv : EcMemory.memenv) env lv e (bds, assoc, pre) =
  let m = fst memenv in
  let subst_in_assoc lv new_id_exp new_ids ((ass : assignables), f) =
    let replace_assignable var =
      match var with
      | APVar (pv', ty) ->  begin
        match lv,new_ids with
        | LvVar (pv ,_), [new_id,_] when NormMp.pv_equal env pv pv' ->
            ALocal (new_id,ty)

        | LvVar _, _ ->
            var

        | LvTuple vs, _ -> begin
            let aux = List.map2 (fun x y -> (fst x, fst y)) vs new_ids in
            try
              let new_id = snd (List.find (NormMp.pv_equal env pv' -| fst) aux) in
              ALocal (new_id, ty)
            with Not_found -> var
          end
      end
      | _ -> var

    in let ass = List.map replace_assignable ass in
       let f   = (subst_form_lv ?mc env lv {m;inv=new_id_exp} {m;inv=f}).inv in
       (ass, f)
  in

  let rec simplify_assoc (assoc, bds, pre) =
    match assoc with
    | [] ->
        ([], bds, pre)

    | (ass, f) :: assoc ->
        let assoc, bds, pre = simplify_assoc (assoc, bds, pre) in

        let destr_ass =
          try  List.combine (List.map in_seq1 ass) (destr_tuple f)
          with Invalid_argument _ | DestrError _ -> [(ass, f)]
        in

        let do_subst_or_accum (assoc, bds, pre) (a, f) =
        match a with
        | [ALocal (id, _)] ->
            let subst = EcFol.Fsubst.f_subst_id in
            let subst = EcFol.Fsubst.f_bind_local subst id f in
            (List.map (snd_map (EcFol.Fsubst.f_subst subst)) assoc,
             List.filter ((<>) id -| fst) bds,
             EcFol.Fsubst.f_subst subst pre)

        | _ -> ((a, f) :: assoc, bds, pre)
      in
      List.fold_left do_subst_or_accum (assoc, bds, pre) destr_ass
  in

  let for_lvars vs =
      let m = EcMemory.memory memenv in
      let fresh pv = EcIdent.create (EcIdent.name (id_of_pv ?mc pv m)) in

      let newids  = List.map (fst_map fresh) vs in
      let bds     = newids @ bds in
      let astuple = f_tuple (List.map (curry f_local) newids) in
      let pre     = (subst_form_lv ?mc env lv {m;inv=astuple} {m;inv=pre}).inv in
      let e_form  = EcFol.ss_inv_of_expr m e in
      let e_form  = (subst_form_lv ?mc env lv {m;inv=astuple} e_form).inv in

      let assoc =
           (List.map (fun x -> APVar x) vs, e_form)
        :: (List.map (subst_in_assoc lv astuple newids) assoc) in

      let assoc, bds, pre = simplify_assoc (List.rev assoc, bds, pre) in

      (bds, List.rev assoc, pre)
  in

  match lv with
  | LvVar   v  -> for_lvars [v]
  | LvTuple vs -> for_lvars vs

(* -------------------------------------------------------------------- *)
let build_sp (memenv : EcMemory.memenv) bds assoc pre =
  let f_assoc = function
    | APVar  (pv, pv_ty) -> (f_pvar pv pv_ty (EcMemory.memory memenv)).inv
    | ALocal (lv, lv_ty) -> f_local lv lv_ty
  in

  let rem_ex (assoc, f) (x_id, x_ty) =
    try
      let rec partition_on_x = function
        | [] ->
            raise Not_found
        | (a, e) :: assoc when f_equal e (f_local x_id x_ty) ->
            (a, assoc)
        | x :: assoc ->
            let a, assoc = partition_on_x assoc in (a, x::assoc)
      in
      let a,assoc = partition_on_x assoc in
      let a       = f_tuple (List.map f_assoc a) in
      let subst   = EcFol.Fsubst.f_subst_id in
      let subst   = EcFol.Fsubst.f_bind_local subst x_id a in
      let f       = EcFol.Fsubst.f_subst subst f in
      let assoc   = List.map (snd_map (EcFol.Fsubst.f_subst subst)) assoc in
      (assoc, f)

    with Not_found -> (assoc, f)
  in

  let assoc, pre = List.fold_left rem_ex (assoc, pre) bds in
  let pre =
    let merge_assoc f (a, e) =
      f_and_simpl (f_eq_simpl (f_tuple (List.map f_assoc a)) e) f
    in List.fold_left merge_assoc pre assoc in

  EcFol.f_exists_simpl (List.map (snd_map (fun t -> GTty t)) bds) pre

(* -------------------------------------------------------------------- *)
let rec sp_stmt_r ?mc (memenv : EcMemory.memenv) env (bds, assoc, pre) stmt =
  match stmt with
  | [] ->
      ([], (bds, assoc, pre))

  | i :: is ->
      try
        let bds, assoc, pre =
          sp_instr ?mc memenv env (bds, assoc, pre) i in
        sp_stmt_r ?mc memenv env (bds, assoc, pre) is
      with No_sp ->
        (stmt, (bds, assoc, pre))

and sp_instr ?mc (memenv : EcMemory.memenv) env (bds,assoc,pre) instr =
  match instr.i_node with
  | Sasgn (lv, e) ->
    let bds, assoc, pre = sp_asgn ?mc memenv env lv e (bds, assoc, pre) in

    bds, assoc, pre

  | Sif (e, s1, s2) ->
    let e_form = (EcFol.ss_inv_of_expr (EcMemory.memory memenv) e).inv in
    let pre_t  =
      build_sp memenv bds assoc (f_and_simpl e_form pre) in
    let pre_f  =
      build_sp memenv bds assoc (f_and_simpl (f_not e_form) pre) in
    let stmt_t, (bds_t, assoc_t, pre_t) =
      sp_stmt_r ?mc memenv env (bds, assoc, pre_t) s1.s_node in
    let stmt_f, (bds_f, assoc_f, pre_f) =
      sp_stmt_r ?mc memenv env (bds, assoc, pre_f) s2.s_node in
    if not (List.is_empty stmt_t && List.is_empty stmt_f) then raise No_sp;
    let sp_t = build_sp memenv bds_t assoc_t pre_t in
    let sp_f = build_sp memenv bds_f assoc_f pre_f in
    ([], [], f_or_simpl sp_t sp_f)

  | _ -> raise No_sp

(* -------------------------------------------------------------------- *)
let sp_stmt ?mc (memenv : EcMemory.memenv) env (s : instr list) (pre : form) =
  let rest, (bds, assoc, pre) = sp_stmt_r ?mc memenv env ([], [], pre) s in
  rest, build_sp memenv bds assoc pre

(* -------------------------------------------------------------------- *)
let check_sp_progress ?side (tc : tcenv1) (bounded : bool) (rest : instr list) =
  if bounded && not (List.is_empty rest) then
    tc_error_lazy !!tc (fun fmt ->
      let side = side |> (function
        | None          -> "remaining"
        | Some (`Left ) -> "remaining on the left"
        | Some (`Right) -> "remaining on the right")
      in

      Format.fprintf fmt
        "%d instruction(s) %s, change your [sp] bound"
        (List.length rest) side)

(* -------------------------------------------------------------------- *)
let gap_at (k : int) : EcMatching.Position.codegap1 =
  EcMatching.Position.(gap_before_pos (cpos1 k))
