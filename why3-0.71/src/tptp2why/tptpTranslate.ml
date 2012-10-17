(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Simon Cruanes                                                       *)
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

(** module to translate from the basic abstract tree from the parser
to a proper why internal representation to be pretty-printed *)

open TptpTree

open Why3
open Why3.Ident

module S = Set.Make(String)
module M = Map.Make(String)

(*s exploratory module, to find atoms and functors in order to declare them
as a header *)
module Summary : sig
  type indic = Pred | Term
  val findFreeVars : fmla -> S.t
  val findAtoms : S.t -> fmla -> S.t
  val findFunctors : (indic * int) M.t ->
        TptpTree.fmla -> (indic * int) M.t
  val findAllAtoms : TptpTree.decl list -> S.t
  val findAllFunctors : TptpTree.decl list -> (indic * int) M.t
end = struct

  (** type used to differentiate predicates from functions *)
  type indic = Pred | Term


  (** find free vars in the formula *)
  let findFreeVars f =
    let rec find_f = function
      | FBinop(_,f1,f2) -> S.union (find_f f1) (find_f f2)
      | FUnop(_,f) -> find_f f
      | FQuant(_,vars,f) -> List.fold_right S.remove vars (find_f f)
      | FPred(_, terms) -> List.fold_left S.union S.empty
          (List.map find_t terms)
      | FTermBinop(_,t1,t2) -> S.union (find_t t1) (find_t t2)
    and find_t = function
      | TAtom _ -> S.empty
      | TConst _ -> S.empty
      | TFunctor(_, terms) -> List.fold_left S.union S.empty
          (List.map find_t terms)
      | TVar x -> S.singleton x
    in find_f f

  let rec findAtoms_t s = function
  | TAtom a -> S.add a s
  | TConst _ | TVar _ -> s
  | TFunctor (_, terms) ->
    List.fold_left findAtoms_t s terms

  let rec findAtoms s = function
  | FBinop (_, f1, f2) -> findAtoms (findAtoms s f2) f1
  | FUnop (_, f) -> findAtoms s f
  | FQuant (_, _, f) -> findAtoms s f
  | FPred (_, terms) -> List.fold_left findAtoms_t s terms
  | FTermBinop (_, t1, t2) -> findAtoms_t (findAtoms_t s t2) t1

  let rec findFunctors_t m = function
  | TAtom _ | TConst _ | TVar _ -> m
  | TFunctor (f, terms) -> let new_m = M.add f (Term, List.length terms) m in
      List.fold_left findFunctors_t new_m terms

  let rec findFunctors m = function
  | FBinop (_, f1, f2) -> findFunctors (findFunctors m f2) f1
  | FUnop (_, f) -> findFunctors m f
  | FQuant (_, _, f) -> findFunctors m f
  | FPred (p, terms) -> let new_m = M.add p (Pred, List.length terms) m in
      List.fold_left findFunctors_t new_m terms
  | FTermBinop (_, t1, t2) ->
      findFunctors_t (findFunctors_t m t2) t1

  (** find all atoms used in declarations *)
  let findAllAtoms decls =
    let helper m = function
      | Fof(_, _, f)
      | Cnf(_, _, f) -> findAtoms m f
      | _ -> assert false in
    List.fold_left helper S.empty decls

  (** find all functors in all declarations, with their arity *)
  let findAllFunctors decls =
    let helper s = function
      | Fof(_, _, f)
      | Cnf(_, _, f) -> findFunctors s f
      | _ -> assert false in
    List.fold_left helper M.empty decls

end

(*s this module manages scoping of vars using a stack of
variables bindings *)
(* TODO : use a hashtable and a stack of key lists instead *)
module Scope
  (T : sig
    type key
    type value
    val create : key -> value
  end) = struct
  module M = Map.Make(struct type t=T.key let compare=Pervasives.compare end)

  let scope = ref []

  let is_empty () = !scope = []

  (** adds a new scope with fresh vars *)
  let push_scope vars = let cur = match !scope with
    | (hd::_) -> hd
    | [] -> M.empty in
    let new_m = List.fold_left
      (fun acc x -> M.add x (T.create x) acc) cur vars in
    scope := new_m::(!scope)
  (** exits the outermost scope and forgets all bindings inside *)
  let pop_scope () =
    assert (not (is_empty ()));
    scope := List.tl !scope

  (** finds a symbol in any scope, including deeper ones.
  If the symbol cannot be found, a new binding is created. *)
  let find symbol =
    let rec helper = function
    | [] -> raise Not_found
    | (x::xs) -> try M.find symbol x with Not_found -> helper xs in
    try helper !scope
    with Not_found -> begin
      let v = T.create symbol in
      scope := ( match !scope with
        | [] -> let new_m = M.empty in [M.add symbol v new_m]
        | (hd::tl) -> (M.add symbol v hd)::tl );
      v
    end

  let depth () = List.length !scope

end

let const x _ = x;;

let rec range n obj = match n with
| 0 -> []
| n -> obj::range (n-1) obj

(*s module to translate a basic tptp originated tree into a why AST tree *)
module Translate = struct

  (** an abstract type for the whole theory *)
  let ts = Ty.create_tysymbol (Ident.id_fresh "t") [] None
  let t = Ty.ty_app ts []

  let ident_sanitizer = Ident.create_ident_printer []

  module EnvVar = Scope(
    struct
      type key = variable
      type value = Term.vsymbol
      let create name = Term.create_vsymbol (id_fresh (String.uncapitalize name)) t
    end)
  module EnvFunctor = Scope(
    struct
      type key = (atom * Ty.ty list * Summary.indic)
      type value = Term.lsymbol
      let create (name,l,ty) = match ty with
      | Summary.Term -> Term.create_fsymbol (id_fresh (String.uncapitalize name)) l t
      | Summary.Pred -> Term.create_psymbol (id_fresh (String.uncapitalize name)) l
    end)

  (** used when a cnf declaration is met, to remember you have to add a
  goal : false at the end of the problem *)
  exception CnfProblem

  (** for cnf declarations, add quantifiers for free vars *)
  let rec cnfAddQuantifiers f =
    let freeVars = Summary.findFreeVars f in
    FQuant(Forall, S.fold (fun x y -> x::y) freeVars [], f)


  (** translation for terms *)
  let rec term2term = function
  | TAtom x -> Term.fs_app (EnvFunctor.find (x, [], Summary.Term)) [] t
  | TConst x -> Term.fs_app (EnvFunctor.find (x, [], Summary.Term)) [] t
  | TVar x -> Term.t_var (EnvVar.find x)
  | TFunctor (f, terms) ->
      Term.fs_app
        (EnvFunctor.find (f, List.map (const t) terms, Summary.Term))
        (List.map term2term terms)
        t

  (** translation for formulae *)
  let translate_binop = function
    | And -> Term.Tand | Or -> Term.Tor
    | Implies -> Term.Timplies | Equiv -> Term.Tiff

  let translate_quant = function
    | Forall -> Term.Tforall | Exist -> Term.Texists

  let rec fmla2fmla = function
  | FBinop (op, f1, f2) ->
    Term.t_binary
      (translate_binop op)
      (fmla2fmla f1)
      (fmla2fmla f2)
  | FUnop (op, f) ->
    assert (op = Not);
    Term.t_not_simp (fmla2fmla f)
  | FQuant (quant, vars, f) -> begin
    (* Format.printf "@[<hov 2>quantifier %s %s (depth %d)@]\n" (if quant=Forall then "forall" else "exists") (String.concat ", " vars) (EnvVar.depth ()); *)
    EnvVar.push_scope vars; (* new scope *)
    let answer = Term.t_quant_close
      (translate_quant quant)
      (List.map EnvVar.find vars)
      [] (* no triggers *)
      (fmla2fmla f) in
    EnvVar.pop_scope (); (* exit scope *)
    answer
  end
  | FPred (p, terms) ->
    Term.ps_app
      (EnvFunctor.find (p, List.map (const t) terms, Summary.Pred))
      (List.map term2term terms)
  | FTermBinop (op, t1, t2) ->
      ( match op with
        | Equal -> Term.t_equ
        | NotEqual -> Term.t_neq)
      (term2term t1) (term2term t2)

  let translatePropKind = function
  | Axiom -> Decl.Paxiom
  | Conjecture -> Decl.Pgoal
  | NegatedConjecture -> Decl.Pgoal
  | Lemma -> Decl.Plemma

  (** add a declaration to a theory, after translation *)
  let rec addDecl theory = function
  | Cnf(_, NegatedConjecture, _) ->
      raise CnfProblem
  | Cnf(name, ty, f) -> (* just add quantifiers and process it as a fof *)
      addDecl theory (Fof(name, ty, cnfAddQuantifiers f))
  | Fof(name, ty, f) ->
      let fmla = fmla2fmla f in
      let name = Ident.string_unique ident_sanitizer name in (* fresh name *)
      (*print_endline ("adds declaration of "^name); *)
      Theory.add_prop_decl theory (translatePropKind ty)
        (Decl.create_prsymbol (id_fresh name)) fmla
  | Include _ ->
    failwith "There should not be includes when adding declarations"


  (** forward declaration of atoms and functors *)
  let addAtomForwardDecl name theory =
    (* Format.printf "declares %s\n (depth %d)" name (EnvVar.depth ()); *)
    let logic_decl = Decl.create_logic_decl
      [(EnvFunctor.find (name, [], Summary.Term)), None] in
    Theory.add_decl theory logic_decl

  let addFunctorsForwardDecl name obj theory =
    (* Format.printf "declares functor %s (type %s) (depth %d)\n" name
    (if fst obj = Summary.Pred then "pred" else "term"); *)
    let logic_decl = Decl.create_logic_decl
      [(EnvFunctor.find (name, range (snd obj) t, (fst obj))), None] in
    Theory.add_decl theory logic_decl

  let rec buildFofTheory theory decls =
    try
      List.fold_left addDecl theory decls
    with CnfProblem -> (* raised if a cnf NegatedConjecture is found *)
      buildCnfTheory theory decls
  (* if this problem is about cnf NegatedConjecture, just transform
  every NegatedConjecture to an axiom, and add False as a goal *)
  and buildCnfTheory theory decls =
    let hideNegatedConjecture = function
      | Cnf(name, NegatedConjecture, f) -> Cnf(name,Axiom, f)
      | blah -> blah in
    let theory = List.fold_left addDecl theory
      (List.map hideNegatedConjecture decls) in
    Theory.add_decl theory (Decl.create_prop_decl Decl.Pgoal
      (Decl.create_prsymbol (id_fresh "negated_goal")) Term.t_false)




  (** from a list of untyped declarations, translates them into a why theory *)
  let theory_of_decls path theoryName decls =
    let theory = Theory.create_theory ~path (Ident.id_fresh theoryName) in
    let theory = Theory.add_ty_decl theory [ts, Decl.Tabstract] in
    let theory = S.fold addAtomForwardDecl (Summary.findAllAtoms decls) theory in
    (* Format.eprintf "atoms forward decls finished.@."; *)
    let theory = M.fold addFunctorsForwardDecl (Summary.findAllFunctors decls) theory in
    (* Format.eprintf "functors forward decls finished.@."; *)
    let theory = buildFofTheory theory decls in
    Theory.close_theory theory


end

(** exported symbol *)
let theory_of_decls = Translate.theory_of_decls
