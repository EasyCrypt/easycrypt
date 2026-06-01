(* -------------------------------------------------------------------- *)
(* Hash-table over formulas whose key equality is alpha-equivalence (and
   conversion) in a fixed hypotheses context. The companion [hash] is
   invariant under the renaming of bound variables: when descending under
   a binder, each bound variable is substituted by a canonical de-Bruijn
   level identifier before being hashed, so that alpha-equivalent
   formulas hash equal (a requirement for [Hashtbl.Make]). *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcCoreFol
open EcIdent
open EcEnv.LDecl

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map

(* -------------------------------------------------------------------- *)
module Make (Ctxt : sig val hyps : hyps end) = struct
    type state = {
      level: int;
      subst: EcSubst.subst;
    }

    let empty_state : state = {level = 0; subst = EcSubst.empty}

    let bruijn_idents : (int, ident) Map.t ref = ref Map.empty

    let clean_bruijn_idents : unit -> unit =
      fun () -> bruijn_idents := Map.empty

    let ident_of_debruijn_level (i: int) : ident =
      match Map.find_opt i !bruijn_idents with
      | Some id -> id
      | None -> let id = create (string_of_int i) in
        bruijn_idents := Map.add i id !bruijn_idents;
        id

    let add_to_state (id: ident) (ty: ty) (st: state) =
      let new_id = ident_of_debruijn_level st.level in
      let level = st.level + 1 in
      let subst = EcSubst.add_flocal st.subst id (f_local new_id ty) in
      { level; subst }, new_id

    let rec hash (st:state) (f: form) : int =
      let hnode = match f.f_node with
      | Fquant (qnt, bnds, f)  ->
        let st, bnds =
          List.fold_left_map (fun st (orig_id, gty) ->
            match gty with
            | GTty ty ->
              let st, new_id = add_to_state orig_id ty st in
              st, (new_id, gty)
            | _ ->
              st, (orig_id, gty)
          ) st bnds
        in Why3.Hashcons.combine2 (qt_hash qnt) (b_hash bnds) (hash st (EcSubst.subst_form st.subst f))
      | Fif (cond, tb, fb)  ->
          let hash = hash st in
          Why3.Hashcons.combine2 (hash cond) (hash tb) (hash fb)
      | Fmatch (_, _, _)  -> assert false
      | Flet (lp, value, body)  ->
          begin match lp with
          | LSymbol (orig_id, ty) ->
            let hval = hash st value in
            let st, new_id = add_to_state orig_id ty st in
            let hbody = hash st (EcSubst.subst_form st.subst body) in
            let hlp = lp_hash (LSymbol (new_id, ty)) in
            Why3.Hashcons.combine2 hlp hval hbody
          | LTuple bnds ->
            let hval = hash st value in
            let st, new_ids = List.fold_left_map (fun st (id, ty) -> add_to_state id ty st) st bnds in
            let hbody = hash st (EcSubst.subst_form st.subst body) in
            let hbinds = lp_hash @@ LTuple (List.combine new_ids (List.snd bnds)) in
            Why3.Hashcons.combine2 hbinds hval hbody
          | LRecord (_, _) -> assert false
          end
      | Fapp (op, args)  ->
        let hop = hash st op in
        Why3.Hashcons.combine_list (hash st) hop args
      | Ftuple comps  ->
        Why3.Hashcons.combine_list (hash st) 0 comps
      | Fproj (tp, i)  ->
        Why3.Hashcons.combine (hash st tp) i
      | FhoareF _hF ->
          assert false
(*      FIXME: do we want this case and the one below?
        let hpre = doit st (hf_pr hF).inv in
        let hpo = doit st (hf_po hF).inv in
        let hf = x_hash hF.hf_f in
        let hm = id_hash hF.hf_m in
        Why3.Hashcons.combine3 hpre hpo hf hm
*)
      | FhoareS _hS ->
          assert false
(*
        let hme = me_hash hS.hs_m in
        let hpre = doit st (hs_pr hS).inv in
        let hpo = doit st (hs_po hS).inv in
        let hs = s_hash
        f_hoareS me {inv=npre;m} hs.hs_s {inv=npo;m}
*)
      | FbdHoareF _  -> assert false
      | FbdHoareS _  -> assert false
      | FeHoareF _  -> assert false
      | FeHoareS _  -> assert false
      | FequivF _ef ->
        assert false
(*      FIXME: do we want these cases?
        let npre = doit st (ef_pr ef).inv in
        let npo = doit st (ef_po ef).inv in
        f_equivF {inv=npre;ml=ef.ef_ml;mr=ef.ef_mr} ef.ef_fl ef.ef_fr {inv=npo;ml=ef.ef_ml;mr=ef.ef_mr}
*)
      | FequivS _es  ->
        assert false
(*
        let ml, mel = es.es_ml in
        let mr, mer = es.es_mr in
        let npre = doit st (es_pr es).inv in
        let npo = doit st (es_po es).inv in
        f_equivS mel mer {inv=npre;ml;mr} es.es_sl es.es_sr {inv=npo;ml;mr}
*)
      | FeagerF _  -> assert false
      | Fpr _ ->  assert false
      | Fint _
      | Flocal _
      | Fpvar (_, _)
      | Fglob (_, _)
      | Fop (_, _) -> f_hash f (* FIXME: maybe do these cases as well? *)
      in Why3.Hashcons.combine hnode (ty_hash f.f_ty)

    module Htbl = Batteries.Hashtbl.Make(struct
    type t = form

    let equal f1 f2 = EcReduction.is_alpha_eq Ctxt.hyps f1 f2

    let hash f = hash empty_state f

    end)

  let clear htbl =
    clean_bruijn_idents ();
    Htbl.clear htbl
end
