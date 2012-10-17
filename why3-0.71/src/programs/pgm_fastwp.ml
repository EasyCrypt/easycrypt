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

(* CURRENTLY DEAD CODE; FOR LATER USE... *)

open Format
open Why3
open Ident
open Ty
open Term
open Decl
open Theory
open Pgm_ttree
open Pgm_typing

module E = Pgm_types.E

module State : sig
  type t
  val create     : env -> E.t -> t
  val push_label : env -> ?label:label -> t -> label * t
  val havoc      : env -> ?pre:label -> E.t   -> t -> t
  val term       : env ->               t -> term -> term
  val fmla       : env -> ?old:label -> t -> fmla -> fmla
  val quantify   : env -> t -> E.t -> fmla -> fmla
end = struct

  type t = {
    current : vsymbol E.Mref.t;
    old     : vsymbol E.Mref.t Mvs.t;
  }

  let unref_ty env ty = match ty.ty_node with
    | Tyapp (ts, [ty]) when ts_equal ts (ts_ref env) -> ty
    | _ -> assert false

  let var_of_reference env = function
    | E.Rlocal vs ->
        create_vsymbol (id_fresh vs.vs_name.id_string) (unref_ty env vs.vs_ty)
    | E.Rglobal { ls_name = id; ls_value = Some ty } ->
        create_vsymbol (id_fresh id.id_string) (unref_ty env ty)
    | E.Rglobal { ls_value = None } ->
        assert false

  let havoc1 env r m =
    let v = var_of_reference env r in
    E.Mref.add r v m

  let create env ef =
    let s = E.Sref.union ef.E.reads ef.E.writes in
    { current = E.Sref.fold (havoc1 env) s E.Mref.empty; old = Mvs.empty; }

  let havoc env ?pre ef s =
    let l = match pre with
      | None -> fresh_label env
      | Some l -> l
    in
    { current = E.Sref.fold (havoc1 env) ef.E.writes s.current;
      old = Mvs.add l s.current s.old; }

  let push_label env ?label s =
    let l = match label with None -> fresh_label env | Some l -> l in
    l, havoc env ~pre:l E.empty s

  let ref_at cur s r =
    let m = match cur with
      | None -> s.current
      | Some l -> assert (Mvs.mem l s.old); Mvs.find l s.old
    in
    assert (E.Mref.mem r m);
    E.Mref.find r m

  (* old = label for old state,     if any
     cur = label for current state, if any *)
  let rec term_at env old cur s t = match t.t_node with
    | Tapp (ls, [t]) when ls_equal ls (ls_bang env) ->
        let r = reference_of_term t in
        t_var (ref_at cur s r)
    (* TODO: old, at *)
    | _ ->
        t_map (term_at env old cur s) (fmla_at env old cur s) t

  and fmla_at env old cur s f =
    t_map (term_at env old cur s) (fmla_at env old cur s) f

  let term env      s t = term_at env None None s t
  let fmla env ?old s f = fmla_at env old  None s f

  let quantify _env s ef f =
    let quant r f = wp_forall [ref_at None s r] [] f in
    let s = E.Sref.union ef.E.reads ef.E.writes in
    E.Sref.fold quant s f

  let print _fmt _s = assert false (*TODO*)

end

