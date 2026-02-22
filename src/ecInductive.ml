(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcAst
open EcTypes
open EcDecl
open EcCoreFol

module EP = EcPath
module FL = EcCoreFol

(* -------------------------------------------------------------------- *)
type field  = symbol * EcTypes.ty
type fields = field list

type record = {
  rc_path    : EcPath.path;
  rc_tparams : ty_params;
  rc_fields  : fields;
}

(* -------------------------------------------------------------------- *)
let record_ctor_name   (x : symbol) = Printf.sprintf "mk_%s"  x
let record_ind_name    (x : symbol) = Printf.sprintf "%s_ind" x
let datatype_proj_name (x : symbol) = Printf.sprintf "get_as_%s" x

(* -------------------------------------------------------------------- *)
let record_ctor_path (p : EP.path) =
  EcPath.pqoname (EcPath.prefix p) (record_ctor_name (EcPath.basename p))

(* -------------------------------------------------------------------- *)
let record_ind_path (p : EP.path) =
  EcPath.pqoname (EcPath.prefix p) (record_ind_name (EcPath.basename p))

(* -------------------------------------------------------------------- *)
let datatype_proj_path (p : EP.path) (x : symbol) =
  EcPath.pqoname (EcPath.prefix p) (datatype_proj_name x)

(* -------------------------------------------------------------------- *)
let indsc_of_record (rc : record) =
  let targs  = List.map tvar rc.rc_tparams in
  let recty  = tconstr rc.rc_path targs in
  let recx   = fresh_id_of_ty recty in
  let recfm  = FL.f_local recx recty in
  let predty = tfun recty tbool in
  let predx  = EcIdent.create "P" in
  let pred   = FL.f_local predx predty in
  let ctor   = record_ctor_path rc.rc_path in
  let ctor   = FL.f_op ctor targs (toarrow (List.map snd rc.rc_fields) recty) in
  let prem   =
    let ids  = List.map (fun (_, fty) -> (fresh_id_of_ty fty, fty)) rc.rc_fields in
    let vars = List.map (fun (x, xty) -> FL.f_local x xty) ids in
    let bds  = List.map (fun (x, xty) -> (x, GTty xty)) ids in
    let recv = FL.f_app ctor vars recty in
    FL.f_forall bds (FL.f_app pred [recv] tbool) in
  let form   = FL.f_app pred [recfm] tbool in
  let form   = FL.f_forall [recx, GTty recty] form in
  let form   = FL.f_imp prem form in
  let form   = FL.f_forall [predx, GTty predty] form in

  form

(* -------------------------------------------------------------------- *)
type ctor  = symbol * (EcTypes.ty list)
type ctors = ctor list

type datatype = {
  dt_path    : EcPath.path;
  dt_tparams : ty_params;
  dt_ctors   : ctors
}

(* -------------------------------------------------------------------- *)
type indmode = [`Elim | `Case]

let datatype_ind_name (mode : indmode) (x : symbol) =
  match mode with
  | `Elim -> Printf.sprintf "%s_ind"  x
  | `Case -> Printf.sprintf "%s_case" x

let datatype_ind_path (mode : indmode) (p : EcPath.path) =
  let name = datatype_ind_name mode (EcPath.basename p) in
  EcPath.pqoname (EcPath.prefix p) name

(* -------------------------------------------------------------------- *)
type non_positive_intype = Concrete | Record of symbol | Variant of symbol

type non_positive_description =
  | InType of EcIdent.ident option * non_positive_intype
  | NonPositiveOcc of ty
  | AbstractTypeRestriction
  | TypePositionRestriction of ty

type non_positive_context = (symbol * non_positive_description) list

exception NonPositive of non_positive_context

let with_context ?ident p ctx f =
  try f () with NonPositive l -> raise (NonPositive ((EP.basename p, InType (ident, ctx)) :: l))

let non_positive (p : EP.path) ctx = raise (NonPositive [(EP.basename p, ctx)])
let non_positive' (s : EcIdent.ident) ctx = raise (NonPositive [(s.id_symb, ctx)])

(** below, [fct] designates the function that takes a path to a type constructor
    and returns the corresponding type declaration *)

(** Strict positivity enforces the following, for every variant of the datatype p:
    - for each subterm (a → b), p ∉ fv(a);
    - inductive occurences a₁ a₂ .. aₙ p are such that ∀i. p ∉ fv(aᵢ)

    Crucially, this has to be checked whenever p occurs in an instance of
    another type constructor.

    FIXME: The current implementation prohibits the use of a type which changes
    its type arguments like e.g.
    {v
      type ('a, 'b) t = [
        | Elt of 'a
        | Swap of ('b, 'a) t
      ].
    v}
    to be used in some places while defining another inductive type. *)

let rec occurs ?(normty = identity) p t =
  match (normty t).ty_node with
  | Tconstr (p', _) when EcPath.p_equal p p' -> true
  | _ -> EcTypes.ty_sub_exists (occurs p) t

(** Tests whether the first list is a list of type variables, matching the
    identifiers of the second list. *)
let ty_params_compat =
  List.for_all2 (fun ty param_id ->
      match ty.ty_node with
      | Tvar id -> EcIdent.id_equal id param_id
      | _ -> false)

(** Ensures all occurrences of type variable [ident] are positive in type
    declaration [decl] (with name [p]).
    This function provide error context in case the check fails. *)
let rec check_positivity_in_decl fct p decl ident =
  let check x () = check_positivity_ident fct p decl.tyd_params ident x
  and iter l f = List.iter f l in

  match decl.tyd_type with
  | Concrete ty -> with_context ~ident p Concrete (check ty)
  | Abstract -> non_positive p AbstractTypeRestriction
  | Datatype { tydt_ctors } ->
      iter tydt_ctors @@ fun (name, argty) ->
      iter argty @@ fun ty ->
      with_context ~ident p (Variant name) (check ty)
  | Record (_, tys) ->
      iter tys @@ fun (name, ty) ->
      with_context ~ident p (Record name) (check ty)

(** Ensures all occurrences of type variable [ident] are positive in type [ty] *)
and check_positivity_ident fct p params ident ty =
  match ty.ty_node with
  | Tglob _ | Tunivar _ | Tvar _ -> ()
  | Ttuple tys -> List.iter (check_positivity_ident fct p params ident) tys
  | Tconstr (q, args) when EcPath.p_equal q p ->
      if not (ty_params_compat args params) then
        non_positive p (TypePositionRestriction ty)
  | Tconstr (q, args) ->
      let decl = fct q in
      List.iter (check_positivity_ident fct p params ident) args;
      List.combine args decl.tyd_params
      |> List.filter_map (fun (arg, ident') ->
             if EcTypes.var_mem ident arg then Some ident' else None)
      |> List.iter (check_positivity_in_decl fct q decl)
  | Tfun (from, to_) ->
      if EcTypes.var_mem ident from then non_positive' ident (NonPositiveOcc ty);
      check_positivity_ident fct p params ident to_

(** Ensures all occurrences of path [p] are positive in type [ty] *)
let rec check_positivity_path fct p ty =
  match ty.ty_node with
  | Tglob _ | Tunivar _ | Tvar _ -> ()
  | Ttuple tys -> List.iter (check_positivity_path fct p) tys
  | Tconstr (q, args) when EcPath.p_equal q p ->
      if List.exists (occurs p) args then non_positive p (NonPositiveOcc ty)
  | Tconstr (q, args) ->
      let decl = fct q in
      List.iter (check_positivity_path fct p) args;
      List.combine args decl.tyd_params
      |> List.filter_map (fun (arg, ident) ->
             if occurs p arg then Some ident else None)
      |> List.iter (check_positivity_in_decl fct q decl)
  | Tfun (from, to_) ->
      if occurs p from then non_positive p (NonPositiveOcc ty);
      check_positivity_path fct p to_

let check_positivity fct dt =
  let check ty () = check_positivity_path fct dt.dt_path ty
  and iter l f = List.iter f l in
  iter dt.dt_ctors @@ fun (name, argty) ->
  iter argty @@ fun ty ->
  with_context dt.dt_path (Variant name) (check ty)

let indsc_of_datatype ?(normty = identity) (mode : indmode) (dt : datatype) =
  let tpath  = dt.dt_path in

  let rec scheme1 p (pred, fac) ty =
    match (normty ty).ty_node with
    | Tglob   _ -> assert false
    | Tunivar _ -> assert false
    | Tvar    _ -> None

    | Ttuple tys -> begin
        let xs  = List.map (fun xty -> (fresh_id_of_ty xty, xty)) tys in
        let sc1 = fun (x, xty) -> scheme1 p (pred, FL.f_local x xty) xty in
          match List.pmap sc1 xs with
          | []  -> None
          | scs -> Some (FL.f_let (LTuple xs) fac (FL.f_ands scs))
    end

    | Tconstr (p', _)  ->
        if not (EcPath.p_equal p p') then None else
          Some (FL.f_app pred [fac] tbool)

    | Tfun (ty1, ty2) ->
        let x = fresh_id_of_ty ty1 in
          scheme1 p (pred, FL.f_app fac [FL.f_local x ty1] ty2) ty2
            |> omap (FL.f_forall [x, GTty ty1])

  and schemec mode (targs, p) pred (ctor, tys) =
    let indty = tconstr p (List.map tvar targs) in
    let xs    = List.map (fun xty -> (fresh_id_of_ty xty, xty)) tys in
    let cargs = List.map (fun (x, xty) -> FL.f_local x xty) xs in
    let ctor  = EcPath.pqoname (EcPath.prefix tpath) ctor in
    let ctor  = FL.f_op ctor (List.map tvar targs) (toarrow tys indty) in
    let form  = FL.f_app pred [FL.f_app ctor cargs indty] tbool in
    let form  =
      match mode with
      | `Case -> form

      | `Elim ->
          let sc1 = fun (x, xty) -> scheme1 p (pred, FL.f_local x xty) xty in
          let scs = List.pmap sc1 xs in
            (FL.f_imps scs form)
    in

    let form  =
      let bds = List.map (fun (x, xty) -> (x, GTty xty)) xs in
        FL.f_forall bds form

    in
      form

  and scheme mode (targs, p) ctors =
    let indty  = tconstr p (List.map tvar targs) in
    let indx   = fresh_id_of_ty indty in
    let indfm  = FL.f_local indx indty in
    let predty = tfun indty tbool in
    let predx  = EcIdent.create "P" in
    let pred   = FL.f_local predx predty in
    let scs    = List.map (schemec mode (targs, p) pred) ctors in
    let form   = FL.f_app pred [indfm] tbool in
    let form   = FL.f_forall [indx, GTty indty] form in
    let form   = FL.f_imps scs form in
    let form   = FL.f_forall [predx, GTty predty] form in
      form

  in scheme mode (dt.dt_tparams, tpath) dt.dt_ctors

(* -------------------------------------------------------------------- *)
let datatype_projectors (tpath, tparams, { tydt_ctors = ctors }) =
  let thety = tconstr tpath (List.map tvar tparams) in

  let do1 i (cname, cty) =
    let thv = EcIdent.create "the" in
    let the = f_local thv thety in
    let rty = ttuple cty in

    let do1 j (_, cty2) =
      let lvars =
        List.map
          (fun ty -> (EcIdent.create (symbol_of_ty ty), ty))
          cty2 in

      f_lambda
        (List.map (fun (x, ty) -> (x, GTty ty)) lvars)
        (if   i = j
         then f_some (f_tuple (List.map (curry f_local) lvars))
         else f_none rty) in

    let body = f_match the (List.mapi do1 ctors) (toption rty) in
    let body = f_lambda [thv, GTty thety] body in

    let op = Some (OP_Plain body) in
    let op = mk_op ~opaque:optransparent tparams body.f_ty op `Global in (* FIXME *)

    (cname, op) in

  List.mapi do1 ctors

(* -------------------------------------------------------------------- *)
let datatype_as_ty_dtype datatype =
  let indsc    = indsc_of_datatype `Elim datatype in
  let casesc   = indsc_of_datatype `Case datatype in
  datatype.dt_tparams,
    { tydt_ctors   = datatype.dt_ctors ;
      tydt_schcase = casesc;
      tydt_schelim = indsc ; }

(* -------------------------------------------------------------------- *)
type case1 = {
  cs1_ctor : EcPath.path;
  cs1_vars : (EcIdent.t * EcTypes.ty) list;
}

type branch1 = {
  br1_target : EcIdent.t;
  br1_case   : case1;
}

type branch = {
  br_branches : branch1 list;
  br_body     : expr;
}

type opfix = branch list

(* -------------------------------------------------------------------- *)
let collate_matchfix (fix : EcDecl.opfix) : opfix =
  let names = List.map
    (fun i -> fst (List.nth fix.opf_args i))
    (fst fix.opf_struct) in

  let rec collate ctors branches =
    match branches with
    | OPB_Leaf (vars, body) ->
        let branches =
          List.map2
            (fun br1_case br1_target -> { br1_target; br1_case; })
            (List.map2
               (fun cs1_ctor cs1_vars -> { cs1_ctor; cs1_vars; })
               ctors vars)
            names
        in [{ br_branches = branches; br_body = body }]

    | OPB_Branch br ->
        let aout =
          List.map
            (fun br1 -> collate (fst br1.opb_ctor :: ctors) br1.opb_sub)
            (Parray.to_list br)
        in List.flatten aout

  in collate [] fix.opf_branches

(*-------------------------------------------------------------------- *)
type prind = {
  ip_path    : EcPath.path;
  ip_tparams : ty_params;
  ip_prind   : EcDecl.prind;
}

(* -------------------------------------------------------------------- *)
let prind_indsc_name (s : symbol) =
  Printf.sprintf "%s_ind" s

let prind_indsc_path (p : EcPath.path) =
  EcPath.pqoname
    (EcPath.prefix p) (prind_indsc_name (EcPath.basename p))

let prind_introsc_path (p : EcPath.path) (x : symbol) =
  EcPath.pqoname (EcPath.prefix p) x

(* -------------------------------------------------------------------- *)
let indsc_of_prind ({ ip_path = p; ip_prind = pri } as pr) =
  let bds   = List.map (snd_map FL.gtty) pri.pri_args in
  let prty  = toarrow (List.map snd pri.pri_args) tbool in
  let prag  = (List.map (curry FL.f_local) pri.pri_args) in
  let predx = EcIdent.create "P" in
  let pred  = FL.f_local predx tbool in

  let for1 ctor =
    let px = FL.f_imps ctor.prc_spec pred in
    FL.f_forall ctor.prc_bds px
  in

  let sc = FL.f_op p (List.map tvar pr.ip_tparams) prty in
  let sc = FL.f_imp (FL.f_app sc prag tbool) pred in
  let sc = FL.f_imps (List.map for1 pri.pri_ctors) sc in
  let sc = FL.f_forall [predx, FL.gtty tbool] sc in
  let sc = FL.f_forall bds sc in

  (pr.ip_tparams, sc)

(* -------------------------------------------------------------------- *)
let introsc_of_prind ({ ip_path = p; ip_prind = pri } as pr) =
  let bds  = List.map (snd_map FL.gtty) pri.pri_args in
  let clty = toarrow (List.map snd pri.pri_args) tbool in
  let clag = (List.map (curry FL.f_local) pri.pri_args) in
  let cl   = FL.f_op p (List.map tvar pr.ip_tparams) clty in
  let cl   = FL.f_app cl clag tbool in

  let for1 ctor =
    let cl = FL.f_imps ctor.prc_spec cl in
    let cl = FL.f_forall (bds @ ctor.prc_bds) cl in
    (pr.ip_tparams, cl)

  in List.map (fun c -> (c.prc_ctor, for1 c)) pri.pri_ctors

(* --------------------------------------------------------------------- *)
let prind_schemes (pr : prind) =
  let iname = prind_indsc_name (EcPath.basename pr.ip_path) in
  (iname, indsc_of_prind pr) :: (introsc_of_prind pr)

(* -------------------------------------------------------------------- *)
let prind_is_iso_ands (pr : EcDecl.prind) =
  match pr.pri_ctors with
  | [ { prc_ctor = x; prc_bds = []; prc_spec = sp; } ] ->
     Some (x, List.length sp)
  | _ -> None

(* -------------------------------------------------------------------- *)
let prind_is_iso_ors (pr : EcDecl.prind) =
  match pr.pri_ctors with
  | [ { prc_ctor = x1; prc_bds = []; prc_spec = sp1; } ;
      { prc_ctor = x2; prc_bds = []; prc_spec = sp2; } ] ->
     Some (t2_map (snd_map List.length) ((x1, sp1), (x2, sp2)))
  | _ -> None
