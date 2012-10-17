(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Why3
open Util
open Ident
open Ty
open Theory
open Term
open Decl

(* model type symbols *)

type mtsymbol = {
  mt_impure   : tysymbol;
  mt_effect   : tysymbol;
  mt_pure     : tysymbol;
  mt_regions  : int;
  mt_singleton: bool;
}

let mt_equal mt1 mt2 = ts_equal mt1.mt_impure mt2.mt_impure

let mtypes = Hts.create 17

let () =
  let add ts =
    let mt =
      { mt_impure = ts; mt_effect = ts; mt_pure = ts;
        mt_regions = 0; mt_singleton = false }
    in
    Hts.add mtypes ts mt
  in
  add Ty.ts_int;
  add Ty.ts_real

let create_mtsymbol ~impure ~effect ~pure ~singleton =
  let mt =
    { mt_impure  = impure;
      mt_effect  = effect;
      mt_pure    = pure;
      mt_regions = List.length impure.ts_args - List.length pure.ts_args;
      mt_singleton = singleton; }
  in
  Hts.add mtypes impure mt;
  Hts.add mtypes effect mt;
  Hts.add mtypes pure   mt;
  mt

let is_mutable_ts ts =
  try (Hts.find mtypes ts).mt_regions > 0 with Not_found -> false

let is_mutable_ty ty = match ty.ty_node with
  | Ty.Tyapp (ts, _) -> is_mutable_ts ts
  | Ty.Tyvar _ -> false

let is_singleton_ts ts =
  try (Hts.find mtypes ts).mt_singleton with Not_found -> false

let is_singleton_ty ty = match ty.ty_node with
  | Ty.Tyapp (ts, _) -> is_singleton_ts ts
  | Ty.Tyvar _ -> false

let get_mtsymbol ts =
  (* TODO: typles? *)
  try
    Hts.find mtypes ts
  with Not_found ->
    (* Format.eprintf "get_mtsymbol: %a@." Pretty.print_ts ts; *)
    let mt =
      { mt_impure = ts; mt_effect = ts; mt_pure = ts;
        mt_regions = 0; mt_singleton = false }
    in
    Hts.add mtypes ts mt;
    mt

let print_mt_symbol fmt mt =
  Format.fprintf fmt
    "@[impure: %a;@\npure  : %a;@\neffect: %a;@\nregions: %d;@]"
    Pretty.print_ts mt.mt_impure Pretty.print_ts mt.mt_pure
    Pretty.print_ts mt.mt_effect mt.mt_regions

(* model type *************************************************************)

let rec purify ty = match ty.ty_node with
  | Tyapp (ts, tyl) ->
      let tyl = List.map purify tyl in
      begin try
        let mt = Hts.find mtypes ts in
        ty_app mt.mt_pure (Util.chop mt.mt_regions tyl)
      with Not_found ->
        ty_app ts tyl
      end
  | Tyvar _ ->
      ty

let rec effectify ty = match ty.ty_node with
  | Tyapp (ts, tyl) ->
      let tyl = List.map effectify tyl in
      begin try
        let mt = Hts.find mtypes ts in
        ty_app mt.mt_effect tyl
      with Not_found ->
        ty_app ts tyl
      end
  | Tyvar _ ->
      ty

(* builtin logic symbols ************************************************)

let ts_exn = Ty.create_tysymbol (id_fresh "exn") [] None
let ty_exn = Ty.ty_app ts_exn []

(* let ts_label = Ty.create_tysymbol (id_fresh "label") [] None *)

let ts_arrow =
  let v = List.map (fun s -> create_tvsymbol (Ident.id_fresh s)) ["a"; "b"] in
  Ty.create_tysymbol (Ident.id_fresh "arrow") v None

let make_arrow_type tyl ty =
  let arrow ty1 ty2 = Ty.ty_app ts_arrow [ty1; ty2] in
  List.fold_right arrow tyl ty

module Sexn = Term.Sls

module R : sig

  type t = private {
    r_tv : tvsymbol;
    r_ty : Ty.ty;
  }

  val compare : t -> t -> int

  val create : tvsymbol -> Ty.ty -> t

  val occurs_ty : t -> ty -> bool

  val print : Format.formatter -> t -> unit

end = struct

  type t = {
    r_tv : tvsymbol;
    r_ty : Ty.ty;
  }

  let compare r1 r2 =
    Pervasives.compare (id_hash r1.r_tv.tv_name) (id_hash r2.r_tv.tv_name)

  let create tv ty = {
    r_tv = tv;
    r_ty = ty;
  }

  (* FIXME: optimize *)
  let occurs_ty r ty = Stv.mem r.r_tv (Ty.ty_freevars Stv.empty ty)

  let print fmt r =
    Format.fprintf fmt "%a(%a)" Pretty.print_tv r.r_tv Pretty.print_ty r.r_ty

end

module Mreg = Stdlib.Map.Make(R)

module Sreg = Mreg.Set

module rec T : sig

  type pre = Term.term

  type post_fmla = Term.vsymbol (* result *) * Term.term
  type exn_post_fmla = Term.vsymbol (* result *) option * Term.term

  type esymbol = lsymbol

  type post = post_fmla * (esymbol * exn_post_fmla) list

  type type_v = private
  | Tpure    of ty
  | Tarrow   of pvsymbol list * type_c

  and type_c = {
    c_result_type : type_v;
    c_effect      : E.t;
    c_pre         : pre;
    c_post        : post;
  }

  and pvsymbol = private {
    pv_name : ident;
    pv_tv   : type_v;
    pv_effect : vsymbol;
    pv_pure   : vsymbol;
    pv_regions: Sreg.t;
  }

  val tpure  : ty -> type_v
  val tarrow : pvsymbol list -> type_c -> type_v

  val create_pvsymbol :
    preid -> type_v ->
    effect:vsymbol -> pure:vsymbol -> regions:Sreg.t -> pvsymbol

  val compare_pvsymbol : pvsymbol -> pvsymbol -> int

  (* program symbols *)

  type psymbol_kind =
    | PSvar   of pvsymbol
    | PSfun   of type_v
    | PSlogic

  type psymbol = {
    ps_effect : lsymbol;
    ps_pure   : lsymbol;
    ps_kind   : psymbol_kind;
  }

  val create_psymbol:
    ?impure:lsymbol -> effect:lsymbol -> pure:lsymbol -> kind:psymbol_kind ->
    psymbol
  val create_psymbol_fun: preid -> type_v -> lsymbol * psymbol
  val create_psymbol_var: pvsymbol -> lsymbol * psymbol

  val get_psymbol: lsymbol -> psymbol

  val ps_name : psymbol -> ident
  val ps_equal : psymbol -> psymbol -> bool

  (* program types -> logic types *)

  val purify : ty -> ty
  val effectify : ty -> ty

  val trans_type_v : ?effect:bool -> ?pure:bool -> type_v -> ty

  (* operations on program types *)

  val apply_type_v_var : type_v -> pvsymbol -> type_c

  val subst_type_v : ty Mtv.t -> term Mvs.t -> type_v -> type_v

  val occur_type_v : R.t -> type_v -> bool

  val v_result : ty -> vsymbol
  val exn_v_result : Why3.Term.lsymbol -> Why3.Term.vsymbol option

  val post_map : (term -> term) -> post -> post

  val eq_type_v : type_v -> type_v -> bool

  (* pretty-printers *)

  val print_pvsymbol : Format.formatter -> pvsymbol -> unit
  val print_type_v : Format.formatter -> type_v -> unit
  val print_type_c : Format.formatter -> type_c -> unit
  val print_pre    : Format.formatter -> pre    -> unit
  val print_post   : Format.formatter -> post   -> unit

end = struct

  type pre = Term.term

  type post_fmla = Term.vsymbol (* result *) * Term.term
  type exn_post_fmla = Term.vsymbol (* result *) option * Term.term

  type esymbol = lsymbol

  type post = post_fmla * (esymbol * exn_post_fmla) list

  type type_v =
    | Tpure    of Ty.ty
    | Tarrow   of pvsymbol list * type_c

  and type_c = {
    c_result_type : type_v;
    c_effect      : E.t;
    c_pre         : pre;
    c_post        : post;
  }

  and pvsymbol = {
    pv_name : ident;
    pv_tv   : type_v;
    pv_effect : vsymbol;
    pv_pure   : vsymbol; (* for use in the logic *)
    pv_regions: Sreg.t;
  }

  let create_pvsymbol name v ~effect ~pure ~regions =
    { pv_name = id_register name;
      pv_tv   = v;
      pv_effect = effect;
      pv_pure   = pure;
      pv_regions = regions; }

  let compare_pvsymbol v1 v2 =
    compare (id_hash v1.pv_name) (id_hash v2.pv_name)
  let equal_pvsymbol v1 v2 =
    compare_pvsymbol v1 v2 = 0

  (* purify: turns program types into logic types *)

  let purify = purify
  let effectify = effectify

  let rec uncurry_type ?(effect=false) ?(pure=false) = function
    | Tpure ty ->
        [], if pure then purify ty else if effect then effectify ty else ty
    | Tarrow (bl, c) ->
        let tyl1 =
          List.map
            (fun v ->
               if pure then v.pv_pure.vs_ty
               else if effect then v.pv_effect.vs_ty
               else trans_type_v ~effect ~pure v.pv_tv)
            bl
        in
        let tyl2, ty = uncurry_type ~effect ~pure c.c_result_type in
        tyl1 @ tyl2, ty (* TODO: improve efficiency? *)

  and trans_type_v ?(effect=false) ?(pure=false) v =
    if effect && pure then invalid_arg "trans_type_v";
    let tyl, ty = uncurry_type ~effect ~pure v in
    make_arrow_type tyl ty

  (* symbols *)

  type psymbol_kind =
    | PSvar   of pvsymbol
    | PSfun   of type_v
    | PSlogic

  type psymbol = {
    ps_effect : lsymbol;
    ps_pure   : lsymbol;
    ps_kind   : psymbol_kind;
  }

  let psymbols = Hls.create 17

  let create_psymbol ?impure ~effect ~pure ~kind =
    let ps = {
      ps_effect = effect;
      ps_pure   = pure;
      ps_kind   = kind;
    }
    in
    begin match impure with Some ls -> Hls.add psymbols ls ps | None -> () end;
    Hls.add psymbols effect ps;
    Hls.add psymbols pure   ps;
    ps

  let create_psymbol_fun id v =
    let create ?effect ?pure v =
      let tyl, ty = uncurry_type ?effect ?pure v in
      create_lsymbol id tyl (Some ty)
    in
    let impure = create              v in
    let effect = create ~effect:true v in
    let pure   = create ~pure:  true v in
    impure, create_psymbol ~impure ~effect ~pure ~kind:(PSfun v)

  let create_psymbol_var pv =
    let name = pv.pv_name in
    let tv = trans_type_v pv.pv_tv in
    let impure = create_lsymbol (id_clone name) [] (Some tv) in
    let effect = create_lsymbol (id_clone name) [] (Some pv.pv_effect.vs_ty) in
    let pure   = create_lsymbol (id_clone name) [] (Some pv.pv_pure.vs_ty) in
    impure, create_psymbol ~impure ~effect ~pure ~kind:(PSvar pv)

  let get_psymbol ls =
    try
      Hls.find psymbols ls
    with Not_found ->
      (* Format.eprintf "get_psymbol: ls = %a@." Pretty.print_ls ls; *)
      let ps = { ps_effect = ls;
                 ps_pure = ls; ps_kind = PSlogic }
      in
      Hls.add psymbols ls ps;
      ps

  let ps_name ps = ps.ps_pure.ls_name

  let ps_equal ps1 ps2 = ls_equal ps1.ps_pure ps2.ps_pure

  let subst_var ?(effect=false) ?(pure=false) ts s vs =
    if effect && pure then invalid_arg "subst_var";
    let ts =
      if effect then Mtv.map effectify ts
      else if pure then Mtv.map purify ts
      else ts
    in
    let ty' = ty_inst ts vs.vs_ty in
    if ty_equal ty' vs.vs_ty then
      s, vs
    else
      let vs' = create_vsymbol (id_clone vs.vs_name) ty' in
      Mvs.add vs (t_var vs') s, vs'

  let subst_post ts s ((v, q), ql) =
    let ts = Mtv.map purify ts in
    let vq = let s, v = subst_var ts s v in v, t_ty_subst ts s q in
    let handler (e, (v, q)) = match v with
      | None ->
          e, (v, t_ty_subst ts s q)
      | Some v ->
          let s, v = subst_var ts s v in
          e, (Some v, t_ty_subst ts s q)
    in
    vq, List.map handler ql

  let rec subst_type_c ts s c =
    { c_result_type = subst_type_v ts s c.c_result_type;
      c_effect      = E.subst ts c.c_effect;
      c_pre         = (let ts = Mtv.map purify ts in t_ty_subst ts s c.c_pre);
      c_post        = subst_post ts s c.c_post; }

  and subst_type_v ts s = function
    | Tpure ty ->
        Tpure (ty_inst ts ty)
    | Tarrow (bl, c) ->
        let s, bl = Util.map_fold_left (subst_binder ts) s bl in
        Tarrow (bl, subst_type_c ts s c)

  and subst_binder ts s pv =
    let v' = subst_type_v ts s pv.pv_tv in
    let s, effect = subst_var ~effect:true ts s pv.pv_effect in
    let s, pure   = subst_var ~pure:true   ts s pv.pv_pure in
    let regions = E.subst_set ts pv.pv_regions in
    let pv' = create_pvsymbol (id_clone pv.pv_name) v' ~effect ~pure ~regions in
    s, pv'

  let tpure ty = Tpure ty

  let tarrow bl c = match bl with
    | [] ->
        invalid_arg "tarrow"
    | _ ->
        let rename s v =
          let tv' = subst_type_v Mtv.empty s v.pv_tv in
          let effect =
            create_vsymbol (id_clone v.pv_effect.vs_name) v.pv_effect.vs_ty in
          let pure =
            create_vsymbol (id_clone v.pv_pure.vs_name) v.pv_pure.vs_ty in
          let regions = v.pv_regions in
          let v' =
            create_pvsymbol (id_clone v.pv_name) tv' ~effect ~pure ~regions
          in
          let s' = Mvs.add v.pv_pure (t_var pure) s in
          s', v'
        in
        let s, bl' = Util.map_fold_left rename Mvs.empty bl in
        Tarrow (bl', subst_type_c Mtv.empty s c)

  let v_result ty = create_vsymbol (id_fresh "result") ty

  let exn_v_result ls = match ls.ls_args with
    | [] -> None
    | [ty] -> Some (v_result ty)
    | _ -> assert false

  let post_map f ((v, q), ql) =
    (v, f q), List.map (fun (e,(v,q)) -> e, (v, f q)) ql

  let type_c_of_type_v = function
    | Tarrow ([], c) ->
        c
    | v ->
        let ty = trans_type_v ~pure:true v in
        { c_result_type = v;
          c_effect      = E.empty;
          c_pre         = t_true;
          c_post        = (v_result ty, t_true), []; }

  let apply_type_v_var v pv = match v with
    | Tarrow (x :: bl, c) ->
        let ts = ty_match Mtv.empty x.pv_effect.vs_ty pv.pv_effect.vs_ty in
        let c = type_c_of_type_v (Tarrow (bl, c)) in
        subst_type_c ts (Mvs.singleton x.pv_pure (t_var pv.pv_pure)) c
    | Tarrow ([], _) | Tpure _ ->
        assert false

(*   let apply_type_v_sym v s = match v with *)
(*     | Tarrow (x :: bl, c) -> *)
(*         let ts = ty_match Mtv.empty x.pv_effect.vs_ty s.p_ty in *)
(*         let c = type_c_of_type_v (Tarrow (bl, c)) in *)
(*         let t = t_app s.p_ls [] (ty_inst ts x.pv_effect.vs_ty) in *)
(*         subst_type_c ts (Mvs.singleton x.pv_pure t) c *)
(*     | _ -> *)
(*         assert false *)

(*   let apply_type_v_ref v = function *)
(*     | R.Rlocal pv -> apply_type_v_var v pv *)
(*     | R.Rglobal s -> apply_type_v_sym v s *)

  let occur_formula r f = Stv.mem r.R.r_tv (Term.t_ty_freevars Stv.empty f)

  let rec occur_type_v r = function
    | Tpure ty ->
        R.occurs_ty r ty
    | Tarrow (bl, c) ->
        occur_arrow r bl c

  and occur_arrow r bl c = match bl with
    | [] ->
        occur_type_c r c
    | v :: bl ->
        occur_type_v r v.pv_tv ||
          not (R.occurs_ty r v.pv_effect.vs_ty) && occur_arrow r bl c

  and occur_type_c r c =
    occur_type_v r c.c_result_type ||
      occur_formula r c.c_pre ||
      E.occur r c.c_effect ||
      occur_post r c.c_post

  and occur_post r ((_, q), ql) =
    occur_formula r q ||
      List.exists (fun (_, (_, qe)) -> occur_formula r qe) ql

  let rec eq_type_v v1 v2 = match v1, v2 with
    | Tpure ty1, Tpure ty2 ->
        ty_equal ty1 ty2
    | Tarrow (bl1, c1), Tarrow (bl2, c2) ->
        assert (List.length bl1 = List.length bl2); (* FIXME? *)
        let ts =
          List.fold_left2
            (fun ts v1 v2 -> ty_match ts v1.pv_effect.vs_ty v2.pv_effect.vs_ty)
            Mtv.empty bl1 bl2
        in
        eq_type_c (subst_type_c ts Mvs.empty c1) c2
    | _ ->
        false

  and eq_type_c c1 c2 =
    eq_type_v c1.c_result_type c2.c_result_type &&
    E.equal   c1.c_effect      c2.c_effect

  (* pretty-printers *)

  open Pp
  open Format
  open Pretty

  let print_pvsymbol fmt pv =
    fprintf fmt "@[{ %a }@]" print_vs pv.pv_effect

  let print_pre fmt f =
    fprintf fmt "@[{ %a }@]" Pretty.print_term f

  let print_post fmt ((v, q), el) =
    let print_exn_post fmt (l, (v, q)) =
      fprintf fmt "@[<hov 2>| %a %a->@ {%a}@]"
        print_ls l (print_option print_vs) v print_term q
    in
    fprintf fmt "@[{%a | %a}@ %a@]" print_vsty v print_term q
      (print_list space print_exn_post) el

  let rec print_type_v fmt = function
    | Tpure ty ->
        print_ty fmt ty
    | Tarrow (bl, c) ->
        fprintf fmt "@[<hov 2>%a ->@ %a@]"
          (print_list arrow print_binder) bl print_type_c c

  and print_type_c fmt c =
    fprintf fmt "@[{%a}@ %a%a@ %a@]" print_term c.c_pre
      print_type_v c.c_result_type E.print c.c_effect
      print_post c.c_post

  and print_binder fmt x =
    fprintf fmt "(%a/%a:%a)"
      print_vs x.pv_effect print_vs x.pv_pure print_type_v x.pv_tv

end


and E : sig

  type t = private {
    reads  : Sreg.t;
    writes : Sreg.t;
    raises : Sexn.t;
  }

  val empty : t

  val add_read  : R.t -> t -> t
  val add_write : R.t -> t -> t
  val add_raise : T.esymbol -> t -> t
  val add_var   : T.pvsymbol -> t -> t (* add all regions for x, in reads *)

  val remove : Sreg.t -> t -> t
  val filter : (R.t -> bool) -> t -> t

  val remove_raise : T.esymbol -> t -> t

  val union : t -> t -> t

  val equal : t -> t -> bool

  val no_side_effect : t -> bool

  val subst_set : Ty.ty Mtv.t -> Sreg.t -> Sreg.t
  val subst : Ty.ty Mtv.t -> t -> t

  val occur : R.t -> t -> bool

  val print : Format.formatter -> t -> unit
  val print_rset : Format.formatter -> Sreg.t -> unit

end = struct

  open T
  open R

  type t = {
    reads  : Sreg.t;
    writes : Sreg.t;
    raises : Sexn.t;
  }

  let empty = {
    reads = Sreg.empty;
    writes = Sreg.empty;
    raises = Sexn.empty;
  }

  let add_read  r t = { t with reads  = Sreg.add r t.reads  }
  let add_write r t = { t with writes = Sreg.add r t.writes }
  let add_raise e t = { t with raises = Sexn.add e t.raises }
  let add_var pv ef = Sreg.fold add_read pv.pv_regions ef

  let remove s t =
    { t with reads = Sreg.diff t.reads s; writes = Sreg.diff t.writes s }

  let filter p t =
    { t with reads = Sreg.filter p t.reads; writes = Sreg.filter p t.writes }

  let remove_raise e t = { t with raises = Sexn.remove e t.raises }

  let union t1 t2 =
    { reads  = Sreg.union t1.reads  t2.reads;
      writes = Sreg.union t1.writes t2.writes;
      raises = Sexn.union t1.raises t2.raises;
      (* globals = Spv.union t1.globals t2.globals; *) }

  let equal t1 t2 =
    Sreg.equal t1.reads  t2.reads  &&
    Sreg.equal t1.writes t2.writes &&
    Sexn.equal t1.raises t2.raises

  let no_side_effect t =
    Sreg.is_empty t.writes && Sls.is_empty t.raises

  let subst_set ts s =
    let add1 r s =
      let r' =
        try begin match (Mtv.find r.r_tv ts).ty_node with
          | Tyvar r' -> R.create r' (ty_inst ts r.r_ty)
          | Tyapp _  -> assert false
        end with Not_found -> r
      in
      Sreg.add r' s
    in
    Sreg.fold add1 s Sreg.empty

  let subst ts t =
    { reads = subst_set ts t.reads;
      writes = subst_set ts t.writes;
      raises = t.raises;
      (* globals = t.globals;  *)}

  let occur r t =
    Sreg.mem r t.reads || Sreg.mem r t.writes

  open Format
  open Pp
  open Pretty

  let print_rset fmt s = print_list comma R.print  fmt (Sreg.elements s)
  let print_eset fmt s = print_list comma print_ls fmt (Sexn.elements s)
  let print_pvset fmt s = print_list comma T.print_pvsymbol fmt (Spv.elements s)

  let print fmt e =
    if not (Sreg.is_empty e.reads) then
      fprintf fmt "@ reads %a" print_rset e.reads;
    if not (Sreg.is_empty e.writes) then
      fprintf fmt "@ writes %a" print_rset e.writes;
    if not (Sexn.is_empty e.raises) then
      fprintf fmt "@ raises %a" print_eset e.raises
    (* if not (Spv.is_empty e.globals) then *)
    (*   fprintf fmt "@ globals %a" print_pvset e.globals *)

end

and Spv : sig include Set.S with type elt = T.pvsymbol end =
  Set.Make(struct type t = T.pvsymbol let compare = T.compare_pvsymbol end)

and Mpv : sig include Map.S with type key = T.pvsymbol end =
  Map.Make(struct type t = T.pvsymbol let compare = T.compare_pvsymbol end)

(* ghost code

  abstract type ghost_ 'a model 'a
  parameter ghost_ : x:'a -> {} ghost_ 'a {result=x}
  parameter unghost: x:ghost_ 'a -> {} 'a {result=x}
*)
(*****
let mt_ghost =
  let a = create_tvsymbol (id_fresh "a") in
  create_mtsymbol ~mut:false (id_fresh "ghost") [a] (Some (ty_var a))

let ps_ghost =
  let a = create_tvsymbol (id_fresh "a") in
  let x = T.create_pvsymbol (id_fresh "x") (T.tpure (ty_var a)) in
  let ty = ty_app mt_ghost.mt_abstr [ty_var a] in
  let result = create_vsymbol (id_fresh "result") (ty_var a) in
  let eq_result_x = t_equ (t_var result) (t_var x.T.pv_vs) in
  let c = { T.c_result_type = T.tpure ty;
            T.c_effect = E.empty; T.c_pre = t_true;
            T.c_post = (result, eq_result_x), []; }
  in
  T.create_psymbol (id_fresh "ghost") (T.tarrow [x] c)

let ps_unghost =
  let a = create_tvsymbol (id_fresh "a") in
  let ty = ty_app mt_ghost.mt_abstr [ty_var a] in
  let x = T.create_pvsymbol (id_fresh "x") (T.tpure ty) in
  let result = create_vsymbol (id_fresh "result") (ty_var a) in
  let eq_result_x = t_equ (t_var result) (t_var x.T.pv_vs) in
  let c = { T.c_result_type = T.tpure (ty_var a);
            T.c_effect = E.empty; T.c_pre = t_true;
            T.c_post = (result, eq_result_x), []; }
  in
  T.create_psymbol (id_fresh "unghost") (T.tarrow [x] c)
*****)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
