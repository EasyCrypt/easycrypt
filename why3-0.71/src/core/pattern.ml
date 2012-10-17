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

open Util
open Ident
open Ty
open Term

module type Action = sig
  type action
  type branch
  val mk_let : vsymbol -> term -> action -> action
  val mk_branch : pattern -> action -> branch
  val mk_case : term -> branch list -> action
end

exception ConstructorExpected of lsymbol
exception NonExhaustive of pattern list

module Compile (X : Action) = struct
  open X

  let rec compile constructors tl rl = match tl,rl with
    | _, [] -> (* no actions *)
        let pl = List.map (fun t -> pat_wild (t_type t)) tl in
        raise (NonExhaustive pl)
    | [], (_,a) :: _ -> (* no terms, at least one action *)
        a
    | t :: tl, _ -> (* process the leftmost column *)
        let ty = t_type t in
        (* extract the set of constructors *)
        let css = match ty.ty_node with
          | Tyapp (ts,_) ->
              let csl = constructors ts in
              List.fold_left (fun s cs -> Sls.add cs s) Sls.empty csl
          | Tyvar _ ->
              Sls.empty
        in
        (* map every constructor occurring at the head
         * of the pattern list to the list of its args *)
        let types =
          let rec populate acc p = match p.pat_node with
            | Pwild | Pvar _ -> acc
            | Pas (p,_) -> populate acc p
            | Por (p,q) -> populate (populate acc p) q
            | Papp (fs,pl) when Sls.mem fs css -> Mls.add fs pl acc
            | Papp (fs,_) -> raise (ConstructorExpected fs)
          in
          let populate acc (pl,_) = populate acc (List.hd pl) in
          List.fold_left populate Mls.empty rl
        in
        (* dispatch every case to a primitive constructor/wild case *)
        let cases,wilds =
          let add_case fs pl a cases =
            Mls.change fs (function
              | None -> Some [pl,a]
              | Some rl -> Some ((pl,a)::rl)) cases
          in
          let union_cases pl a types cases =
            let add pl q = pat_wild q.pat_ty :: pl in
            let wild ql = [List.fold_left add pl ql, a] in
            let join _ wl rl = Some (List.append wl rl) in
            Mls.union join (Mls.map wild types) cases
          in
          let rec dispatch (pl,a) (cases,wilds) =
            let p = List.hd pl in let pl = List.tl pl in
            match p.pat_node with
              | Papp (fs,pl') ->
                  add_case fs (List.rev_append pl' pl) a cases, wilds
              | Por (p,q) ->
                  dispatch (p::pl, a) (dispatch (q::pl, a) (cases,wilds))
              | Pas (p,x) ->
                  dispatch (p::pl, mk_let x t a) (cases,wilds)
              | Pvar x ->
                  let a = mk_let x t a in
                  union_cases pl a types cases, (pl,a)::wilds
              | Pwild ->
                  union_cases pl a types cases, (pl,a)::wilds
          in
          List.fold_right dispatch rl (Mls.empty,[])
        in
        (* how to proceed if [t] is [Tapp(cs,al)] and [cs] is in [cases] *)
        let comp_cases cs al =
          try compile constructors (List.rev_append al tl) (Mls.find cs cases)
          with NonExhaustive pl ->
            let rec cont acc vl pl = match vl,pl with
              | (_::vl), (p::pl) -> cont (p::acc) vl pl
              | [], pl -> pat_app cs acc ty :: pl
              | _, _ -> assert false
            in
            raise (NonExhaustive (cont [] cs.ls_args pl))
        in
        (* how to proceed if [t] is not covered by [cases] *)
        let comp_wilds () =
          try compile constructors tl wilds
          with NonExhaustive pl ->
            let find_cs cs =
              if Mls.mem cs types then () else
              let tm = ty_match Mtv.empty (of_option cs.ls_value) ty in
              let wild ty = pat_wild (ty_inst tm ty) in
              let pw = pat_app cs (List.map wild cs.ls_args) ty in
              raise (NonExhaustive (pw :: pl))
            in
            Sls.iter find_cs css;
            raise (NonExhaustive (pat_wild ty :: pl))
        in
        (* assemble the primitive case statement *)
        match t.t_node with
        | _ when Mls.is_empty types ->
            comp_wilds ()
        | Tapp (cs,al) when Sls.mem cs css ->
            if Mls.mem cs types then comp_cases cs al else comp_wilds ()
        | _ ->
            let base =
              if Mls.set_submap css types then []
              else [mk_branch (pat_wild ty) (comp_wilds ())]
            in
            let add cs ql acc =
              let get_vs q = create_vsymbol (id_fresh "x") q.pat_ty in
              let vl = List.rev_map get_vs ql in
              let pl = List.rev_map pat_var vl in
              let al = List.rev_map t_var vl in
              mk_branch (pat_app cs pl ty) (comp_cases cs al) :: acc
            in
            mk_case t (Mls.fold add types base)

end

module CompileTerm  = Compile (struct
  type action = term
  type branch = term_branch
  let mk_let v s t  = t_let_close_simp v s t
  let mk_branch p t = t_close_branch p t
  let mk_case t bl  = t_case t bl
end)

