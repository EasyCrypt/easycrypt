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

(*s Transformation which removes most hypothesis, only keeping the one
a graph-based heuristic finds close enough to the goal *)

open Util
open Ident
open Ty
open Term
open Decl
open Task

(* lots of modules and functors applications to be used later *)

module Int_Dft = struct
  type t = int
  let compare = Pervasives.compare
  let default = max_int
end

open Graph
module GP = Graph.Persistent.Digraph.ConcreteLabeled(
  struct
    type t = lsymbol
    let compare x y = compare (ls_hash x) (ls_hash y)
    let hash = ls_hash
    let equal = ls_equal
  end)(Int_Dft)

(** a way to compare/hash expressions *)
module ExprNode = struct
    type t = Term.term
    let compare x y = compare (t_hash x) (t_hash y)
    let hash = t_hash
    let equal = t_equal
end
module GC = Graph.Persistent.Graph.Concrete(ExprNode)
module Sls = Set.Make(GP.V)
module Sexpr = Set.Make(ExprNode)

let err = Format.err_formatter

(** prints the given expression, transforming spaces into _ *)
let string_of_expr_node node =
  let print_in_buf printer x =
    let b = Buffer.create 42 in
    Format.bprintf b "@[%a@]" printer x;
    Buffer.contents b in
  let white_space = Str.regexp "[ ()]" in
  let translate x = Str.global_replace white_space "_" x in
  let repr = print_in_buf Pretty.print_term node in
  translate repr

(* for debugging (graph printing) purposes *)
module Dot_ = Graph.Graphviz.Dot(struct
                          include GC
                          let graph_attributes _ = []
                          let default_vertex_attributes _ = []
                          let vertex_attributes _ = []
                          let vertex_name x = string_of_expr_node (GC.V.label x)
                          let get_subgraph _ = None
                          let default_edge_attributes _ = []
                          let edge_attributes _ = []
                        end)



(** some useful things *)
module Util = struct
  let print_clause fmt = Format.fprintf fmt "@[[%a]@]"
    (Pp.print_list Pp.comma Pretty.print_term)
  let print_clauses fmt = Format.fprintf fmt "[%a]@."
    (Pp.print_list Pp.comma print_clause)

  (** [combinator] applied to all combinaisons of elements
      of [left] and [right] *)
  let map_complete combinator left right =
    let explorer left_elt =
      List.map (fun right_elt -> combinator left_elt right_elt) right in
    List.flatten (List.map explorer left)

(** all combinaisons of elements of [left] and [right],
    folded with [combinator] starting with [acc] *)
  let fold_complete combinator acc left right =
    let explorer acc left_elt =
      List.fold_left
        (fun acc right_elt -> combinator acc left_elt right_elt)
        acc right in
    List.fold_left explorer acc left

  (** given two lists of sets of expr, returns the list made from their union.
      It is like zipping the lists with Sexpr.union. *)
  let rec merge_list l1 l2 = match l1,l2 with
    | x::xs,y::ys -> (Sexpr.union x y) :: merge_list xs ys
    | _,[] -> l1
    | [],_ -> l2
end


(** module used to reduce formulae to Normal Form *)
module NF = struct (* add memoization, one day ? *)
  (* TODO ! *)
  (** all quantifiers in prenex form, currently just identity *)
  let prenex_fmla fmla =
    Format.fprintf err "prenex_fmla : @[%a@]@." Pretty.print_term fmla;
    fmla

  (** creates a fresh non-quantified formula, representing a quantified formula *)
  let create_fmla (vars:Term.vsymbol list) : Term.term =
    let pred = create_psymbol (id_fresh "temoin")
      (List.map (fun var -> var.vs_ty) vars) in
    ps_app pred (List.map t_var vars)


  (** transforms a formulae into its Normal Form as a list of clauses.
      The first argument is a hastable from formulae to formulae.
      A clause is a list of formulae, so this function returns a list
      of list of formulae. *)
  let rec transform fmlaTable fmla =
    Format.fprintf err "transform : @[%a@]@." Pretty.print_term fmla;
    match fmla.t_node with
    | Tquant (_,f_bound) ->
        let var,_,f =  t_open_quant f_bound in
        traverse fmlaTable fmla var f
    | Tbinop (_,_,_) ->
        let clauses = split fmla in
        Format.fprintf err "split : @[%a@]@." Util.print_clause clauses;
        begin match clauses with
          | [f] -> begin match f.t_node with
              | Tbinop (Tor,f1,f2) ->
                  let left = transform fmlaTable f1 in
                  let right = transform fmlaTable f2 in
                  Util.map_complete List.append left right
              | _ -> [[f]]
            end
          | _ -> List.concat (List.map (transform fmlaTable) clauses)
        end
    | Tnot f -> handle_not fmlaTable fmla f
    | Tapp (_,_) -> [[fmla]]
    | Ttrue | Tfalse -> [[fmla]]
    | Tif (_,_,_) -> failwith "if formulae not handled"
    | Tlet (_,_) -> failwith "let formulae not handled"
    | Tcase (_,_) -> failwith "case formulae not handled"
    | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected fmla)

  (** travers prefix quantifiers until it reaches a non-quantified formula,
      collecting bounded vars encountered *)
  and traverse fmlaTable old_fmla vars fmla = match fmla.t_node with
    | Tquant (_,f_bound) ->
        let var,_,f = t_open_quant f_bound in
        traverse fmlaTable old_fmla (var@vars) f
    | _ ->
        if Hterm.mem fmlaTable fmla then
          [[Hterm.find fmlaTable fmla]]
        else
          let new_fmla = create_fmla vars in
          Hterm.add fmlaTable old_fmla new_fmla;
          Hterm.add fmlaTable new_fmla new_fmla;
          [[new_fmla]]

  (** skips prenex quantifiers *)
  and skipPrenex fmlaTable fmla = match fmla.t_node with
    | Tquant (_,f_bound) ->
        let _,_,f = t_open_quant f_bound in
        skipPrenex fmlaTable f
    | _ -> transform fmlaTable fmla

(** logical binary operators splitting *)
  and split f = match f.t_node with
    | Tbinop (Timplies,{t_node = Tbinop (Tor, h1, h2)},f2) ->
        (split (t_binary Timplies h1 f2)) @ (split (t_binary Timplies h2 f2))
    | Tbinop (Timplies,f1,f2) ->
        let clauses = split f2 in
        if List.length clauses >= 2 then
          List.concat
            (List.map (fun f -> split (t_binary Timplies f1 f)) clauses)
        else split (t_or (t_not f1) f2)
    | Tbinop (Tand,f1,f2) -> [f1; f2]
    | _ -> [f]

  (** negation operator handling (with de morgan rules) *)
  and handle_not fmlaTable old_f f = match f.t_node with
    | Tquant (Tforall,f_bound) ->
        let vars,triggers,f1 = t_open_quant f_bound in
        transform fmlaTable (t_exists_close vars triggers (t_not f1))
    | Tnot f1 -> transform fmlaTable f1
    | Tbinop (Tand,f1,f2) ->
        transform fmlaTable (t_or (t_not f1) (t_not f2))
    | Tbinop (Tor,f1,f2) ->
        transform fmlaTable (t_and (t_not f1) (t_not f2))
    | Tbinop (Timplies,f1,f2) ->
        transform fmlaTable (t_and f1 (t_not f2))
    | Tbinop (Tiff,f1,f2) ->
        transform fmlaTable (t_or (t_and f1 (t_not f2)) (t_and (t_not f1) f2))
    | _ -> [[old_f]] (* default case *)

  (** the function to use to effectively transform into a normal form *)
  let make_clauses fmlaTable prop =
    let prenex_fmla = prenex_fmla prop in
    let clauses = skipPrenex fmlaTable prenex_fmla in
    Format.eprintf "==>@ @[%a@]@.@." Util.print_clauses clauses;
    clauses
end


(** module used to compute the graph of relations between constants *)
module GraphConstant = struct

  (** memoizing for formulae and terms, and then expressions *)
  let rec findF fTbl fmla = try
    Hterm.find fTbl fmla
  with Not_found ->
    let new_v = GC.V.create fmla in
    Hterm.add fTbl fmla new_v;
    (* Format.eprintf "generating new vertex : %a@."
      Pretty.print_term fmla; *)
    new_v
  and findT tTbl term = try
    Hterm.find tTbl term
  with Not_found ->
    let new_v = GC.V.create term in
    Hterm.add tTbl term new_v;
    (* Format.eprintf "generating new vertex : %a@."
      Pretty.print_term fmla; *)
    new_v
  and find fTbl tTbl expr = TermTF.t_select (findT tTbl) (findF fTbl) expr

  (** adds a symbol to the graph *)
  let add_symbol fTbl tTbl gc expr =
    GC.add_vertex gc (find fTbl tTbl expr)

  (** analyse dynamic dependencies in one atomic formula, from the bottom *)
  let rec analyse_fmla_base fTbl tTbl gc fmla =
    let gc,_ = analyse_fmla fTbl tTbl (gc,[]) fmla in gc

  (** recursive function used by the previous function *)
  and analyse_fmla fTbl tTbl (gc,vertices) fmla = match fmla.t_node with
    | Tapp (_,terms) ->
        let gc,sub_vertices =
          List.fold_left (analyse_term fTbl tTbl) (gc,[]) terms in
        (* make a clique with [sub_vertices] elements *)
        let gc = Util.fold_complete GC.add_edge gc sub_vertices sub_vertices in
        let pred_vertex = findF fTbl fmla in
        (* add edges between [pred_vertex] and [sub_vertices] *)
        let gc = List.fold_left
          (fun gc term_vertex -> GC.add_edge gc pred_vertex term_vertex)
          gc sub_vertices in
        (gc, pred_vertex :: vertices)
    | _ -> TermTF.t_fold (analyse_term fTbl tTbl) (analyse_fmla fTbl tTbl)
        (gc,vertices) fmla

  (** explore terms. mutually recursive with the previous function *)
  and analyse_term fTbl tTbl (gc,vertices) term = match term.t_node with
    | Tvar _ | Tconst _ ->
        let vertex = findT tTbl term in
        (gc,vertex::vertices)
    | Tapp (_,terms) ->
        let gc,sub_vertices =
          List.fold_left (analyse_term fTbl tTbl) (gc,[]) terms in
        (* make a clique with [sub_vertices] elements *)
        let gc = Util.fold_complete GC.add_edge gc sub_vertices sub_vertices in
        let func_vertex = findT tTbl term in
        (* add edges between [func_vertex] and [sub_vertices] *)
        let gc = List.fold_left
          (fun gc term_vertex -> GC.add_edge gc func_vertex term_vertex)
          gc sub_vertices in
        (gc, func_vertex :: vertices)
    | _ -> TermTF.t_fold (analyse_term fTbl tTbl) (analyse_fmla fTbl tTbl)
        (gc,vertices) term

(** analyse a single clause by folding analyse_fmla_base over it *)
  let analyse_clause fTbl tTbl gc clause =
    List.fold_left (analyse_fmla_base fTbl tTbl) gc clause

  (** analyses a proposition :
      - get it into normal form
      - fold over clauses with analyse_clause *)
  let analyse_prop fmlaTable fTbl tTbl gc prop =
    let clauses = NF.make_clauses fmlaTable prop in
    List.fold_left (analyse_clause fTbl tTbl) gc clauses

  (** processes a single task_head. *)
  let update fmlaTable fTbl tTbl gc task_head =
    match task_head.task_decl.Theory.td_node with
    | Theory.Decl {d_node = Dprop(_,_,prop_decl)} ->
      analyse_prop fmlaTable fTbl tTbl gc prop_decl
    | _ -> gc
end

(** module used to compute the directed graph of predicates *)
module GraphPredicate = struct
  exception Exit of lsymbol

  (** test for negative formulae *)
  let is_negative = function
    | { t_node = Tnot _ } -> true
    | _ -> false

  (** assuming the formula looks like p(t1,t2...),
      returns the symbol p *)
  let extract_symbol fmla =
    let rec search = function
      | { t_node = Tapp(p,_) } -> raise (Exit p)
      | f -> TermTF.t_map (fun t->t) search f in
    try ignore (search fmla);
      Format.eprintf "invalid formula : ";
      Pretty.print_term Format.err_formatter fmla; assert false
    with Exit p -> p

  let find symbTbl x = try
    Hls.find symbTbl x
  with Not_found ->
    let new_v = GP.V.create x in
    Hls.add symbTbl x new_v;
    (* Format.eprintf "generating new vertex : %a@." Pretty.print_ls x; *)
    new_v

  (** analyse a single clause, and creates an edge between every positive
      litteral and every negative litteral of [clause] in [gp] graph. *)
  let analyse_clause symbTbl gp clause =
    let get_symbol x = find symbTbl (extract_symbol x) in
    let negative,positive = List.partition is_negative clause in
    let negative = List.map get_symbol negative in
    let positive = List.map get_symbol positive in
    let n = List.length clause in
    let add left gp right =
      try
        let old = GP.find_edge gp left right in
        if GP.E.label old <= n
        then gp (* old edge is fine *)
        else
          let new_gp = GP.remove_edge_e gp old in
          assert (not (GP.mem_edge new_gp left right));
          GP.add_edge_e gp (GP.E.create left n right)
      with Not_found ->
        let e = GP.E.create left n right in
        GP.add_edge_e gp e in
    List.fold_left (* add an edge from every negative to any positive *)
      (fun gp left ->
       List.fold_left (add left) gp positive) gp negative

  (** takes a prop, puts it in Normal Form and then builds a clause
      from it *)
  let analyse_prop fmlaTable symbTbl gp prop =
    let clauses = NF.make_clauses fmlaTable prop in
    List.fold_left (analyse_clause symbTbl) gp clauses

  (** add a symbol to the graph as a new vertex *)
  let add_symbol symbTbl gp lsymbol =
    GP.add_vertex gp (find symbTbl lsymbol)

  (** takes a constant graph and a task_head, and add any interesting
      element to the graph it returns. *)
  let update fmlaTable symbTbl gp task_head =
    match task_head.task_decl.Theory.td_node with
      | Theory.Decl {d_node = Dprop (_,_,prop_decl) } ->
        (* a proposition to analyse *)
        analyse_prop fmlaTable symbTbl gp prop_decl
      | Theory.Decl {d_node = Dlogic logic_decls } ->
        (* a symbol to add *)
        List.fold_left
          (fun gp logic_decl -> add_symbol symbTbl gp (fst logic_decl))
          gp logic_decls
      | _ -> gp
end

(** module that makes the final selection *)
module Select = struct

  (** gets all predicates symbols of the formula *)
  let get_predicates fmla =
    let id acc _ = acc in
    let rec explore acc fmla = match fmla.t_node with
      | Tapp (pred,_) -> pred::acc
      | _ -> TermTF.t_fold id explore acc fmla
    in explore [] fmla

  (** gets all predicate symbols from a clause *)
  let get_clause_predicates acc clause =
    let rec fmla_get_pred ?(pos=true) acc fmla = match fmla.t_node with
      | Tnot f -> fmla_get_pred ~pos:false acc f
      | Tapp (pred,_) -> (pred, (if pos then `Positive else `Negative))::acc
      | _ -> failwith "bad formula in get_predicates !"
    in List.fold_left fmla_get_pred acc clause

  (** get all sub-formulae *)
  let rec get_sub_fmlas fTbl tTbl fmla =
    let rec gather_sub_fmla fTbl tTbl acc fmla = match fmla.t_node with
      | Tapp (_,terms) ->
          let acc = List.fold_left (gather_sub_term fTbl tTbl) acc terms in
          GraphConstant.findF fTbl fmla :: acc
      | _ -> TermTF.t_fold (gather_sub_term fTbl tTbl)
          (gather_sub_fmla fTbl tTbl) acc fmla
    and gather_sub_term fTbl tTbl acc term = match term.t_node with
      | Tapp (_,terms) ->
          let acc = List.fold_left (gather_sub_term fTbl tTbl) acc terms in
          GraphConstant.findT tTbl term :: acc
      | Tconst _ | Tvar _ -> GraphConstant.findT tTbl term :: acc
      | _ -> TermTF.t_fold (gather_sub_term fTbl tTbl)
          (gather_sub_fmla fTbl tTbl) acc term in
    gather_sub_fmla fTbl tTbl [] fmla

  (** get the predecessors of [positive] in the graph [gp], at distance <= [i]*)
  let rec get_predecessors i gp acc positive =
    if i < 0 then acc
    else
      let acc = Sls.add positive acc in
      List.fold_left (follow_edge gp i)
        acc (GP.pred_e gp positive)
  and follow_edge ?(forward=false) gp i acc edge =
    let f = if forward then get_successors else get_predecessors in
    f (i - GP.E.label edge) gp acc
      ((if forward then GP.E.dst else GP.E.src) edge)
  and get_successors j gp acc negative =
    if j < 0 then acc
    else
      let acc = Sls.add negative acc in
      List.fold_left (follow_edge ~forward:true gp j)
        acc (GP.succ_e gp negative)

  exception FixPoint
  exception Exit of Sexpr.t list

  (** builds the list of reachable nodes in a non-directed graph (of constants)*)
  let build_relevant_variables gc goal_clause =
    let acc = Sexpr.empty in
    let l0 = List.fold_right Sexpr.add goal_clause acc in

    (** explore one more step *)
    let rec one_step cur =
      let step = Sexpr.fold explore cur [cur;cur] in
      Format.eprintf "one step made !@.";
      step

    (** explores the neighbours of [vertex] *)
    and explore vertex l = match l with [_next_cur;cur] ->

      (** [changed] indicates whether a vertex has been added;
          [v] is a vertex *)
      let find_odd v ((acc,_changed) as old) =
        if Sexpr.mem v acc then old else
          let count = GC.fold_pred
            (fun v2 count -> if Sexpr.mem v2 acc then count+1 else count)
            gc v 0 in (* how many predecessors in acc ? *)
          if count >= 2 then (Sexpr.add v acc,true) else old in
      let find_even prev_step v ((acc,_changed) as old) =
        if Sexpr.mem v prev_step || Sexpr.mem v acc then old else
          if GC.fold_pred (fun v2 bool -> bool || (Sexpr.mem v2 acc))
            gc v false (* connected to a vertex in acc ? *)
          then (Sexpr.add v acc, true) else old in
      let next_cur_odd,has_changed = (* compute 2^n+1 elts *)
        GC.fold_succ find_odd gc vertex (cur,false) in
      let next_cur_even,has_changed = (* compute 2^n+2 elts *)
        GC.fold_succ (find_even next_cur_odd)
          gc vertex (cur,has_changed) in
      if has_changed then [next_cur_even;next_cur_odd]
      else raise FixPoint

      | _ -> assert false (*only not to have warnings on non-exhaustive match*)

    (** iterates [one_step] until an exception is raised *)
    and control cur acc =
      let next_acc = try
        let next_step = one_step cur in
        next_step @ acc (* next step contains *2* steps *)
      with FixPoint ->
        Format.eprintf "[control] : fixpoint reached !";
        raise (Exit acc) in
      control (List.hd next_acc) next_acc in
    try
      ignore (control l0 [l0]);
      [l0] (* never returns. this is an odd step (step 1) *)
    with Exit answer ->
      List.rev answer

  (* TODO : be more clear... *)
  (** determines if a proposition is pertinent w.r.t the given goal formula,
      from data stored in the graph [gp] given.
      [i] is the parameter of predicate graph ([gp]) based filtering.
      [j] is the parameter for dynamic constants ([gc]) dependency filtering *)
  let is_pertinent_predicate symTbl goal_clauses ?(i=4) gp fmla =
    let is_negative = function
      | (_,`Negative) -> true
      | (_,`Positive) -> false in
    let find_secure symbTbl x =
      try Hls.find symbTbl x
      with Not_found ->
        Format.eprintf "failure finding %a !@." Pretty.print_ls x;
        raise Not_found in
    let goal_predicates =
      List.fold_left get_clause_predicates [] goal_clauses in
    let predicates = get_predicates fmla in
    let negative,positive = List.partition is_negative goal_predicates in
    let negative,positive = List.map fst negative, List.map fst positive in
    let negative = List.map (find_secure symTbl) negative in (* to be optimized ? *)
    let positive = List.map (find_secure symTbl) positive in
    let predicates = List.map (find_secure symTbl) predicates in
    (* list of negative predecessors of any positive predicate of the goal,
       at distance <= i *)
    let predecessors = List.fold_left (get_predecessors i gp) Sls.empty positive in
    let successors = List.fold_left (get_successors i gp) Sls.empty negative in
    (* a predicates is accepted iff all its predicates are close enough in
       successors or predecessors lists *)
    List.for_all
      (fun x -> if Sls.mem x predecessors || Sls.mem x successors
       then true else begin Format.eprintf "%a not close enough (dist %d)@."
           Pretty.print_ls (GP.V.label x) i; false end)
      predicates

  (** tests whether a formula is pertinent according to the dynamic
      dependency criterion (using the undirected graph gc). *)
  let is_pertinent_dynamic fTbl tTbl goal_clauses ?(j=4) gc =
    let relevant_variables = (* ideally, there should be only one goal clause *)
      List.fold_left Util.merge_list []
        (List.map (build_relevant_variables gc) goal_clauses) in
    function fmla ->
      let rec is_close_enough x l count = match (l,count) with
        | _,n when n < 0 -> false
        | y::_,_ when Sexpr.mem x y -> true
        | _::ys,count -> is_close_enough x ys (count-1)
        | _,_ ->
            false (* case where the fmla is not reachable from goal vars *) in
      let is_acceptable fmla = is_close_enough fmla relevant_variables j in
      let sub_fmlas = get_sub_fmlas fTbl tTbl fmla in
      let sub_fmlas = List.map GC.V.label sub_fmlas in
      List.for_all is_acceptable sub_fmlas

  (** preprocesses the goal formula and the graph, and returns a function
      that will accept or not axioms according to their relevance.
      This is the function directly used to filter axioms. *)
  let filter fTbl tTbl symTbl goal_clauses (gc,gp) decl =
    match decl.d_node with
      | Dtype _ | Dlogic _ | Dind _ -> [decl]
      | Dprop (Paxiom,_,fmla) -> (* filter only axioms *)
          Format.eprintf "filter : @[%a@]@." Pretty.print_term fmla;
          let goal_exprs = goal_clauses in
          let return_value =
            if is_pertinent_predicate symTbl goal_clauses gp fmla &&
              is_pertinent_dynamic fTbl tTbl goal_exprs gc fmla
            then [decl] else [] in
          if return_value = [] then Format.eprintf "NO@.@."
          else Format.eprintf "YES@.@.";
          return_value
      | Dprop(_,_,_) -> [decl]
end

(** if this is the goal, return it as Some goal after checking there is no other
    goal. Else, return the option *)
let get_goal task_head option =
  match task_head.task_decl.Theory.td_node with
    | Theory.Decl {d_node = Dprop(Pgoal,_,goal_fmla)} ->
        assert (option = None); (* only one goal ! *)
        Some goal_fmla
    | _ -> option

(** collects data on predicates and constants in task *)
let collect_info fmlaTable fTbl tTbl symbTbl =
  Trans.fold
    (fun t (gc, gp, goal_option) ->
       GraphConstant.update fmlaTable fTbl tTbl gc t,
       GraphPredicate.update fmlaTable symbTbl gp t,
       get_goal t goal_option)
    (GC.empty, GP.empty, None)

(** the transformation, made from applying collect_info and
then mapping Select.filter *)
let transformation fmlaTable fTbl tTbl symbTbl task =
  (* first, collect data in 2 graphes *)
  let (gc,gp,goal_option) =
    Trans.apply (collect_info fmlaTable fTbl tTbl symbTbl) task in
  Format.fprintf Format.err_formatter "graph: @\n@\n%a@\n@." Dot_.fprint_graph gc;
  (* get the goal *)
  let goal_fmla = match goal_option with
    | None -> failwith "no goal !"
    | Some goal_fmla -> goal_fmla in
  let goal_clauses = NF.make_clauses fmlaTable goal_fmla in
  (* filter one declaration at once *)
  Trans.apply
    (Trans.decl
       (Select.filter fTbl tTbl symbTbl goal_clauses (gc,gp)) None) task

(** the transformation to be registered *)
let hypothesis_selection = (* create lots of hashtables... *)
  let fmlaTable = Hterm.create 17 in
  let fTbl = Hterm.create 17 in
  let tTbl = Hterm.create 17 in
  let symbTbl = Hls.create 17 in
  Trans.store (transformation fmlaTable fTbl tTbl symbTbl)

let _ = Trans.register_transform "hypothesis_selection" hypothesis_selection

(*
Local Variables:
  compile-command: "unset LANG; make"
End:
vim:foldmethod=indent:foldnestmax=1
*)

