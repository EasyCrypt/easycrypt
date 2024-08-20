open EcAst
open EcTypes
open EcModules
open EcSymbols

(*---------------------------------------------------------------------------------------*)
type u_error =
  | UE_InvalidRetInstr
  | UE_UnexpectedReturn
  | UE_ExprNotInLockstep of expr * expr
  | UE_InstrNotInLockstep of instr * instr
  | UE_DifferentProgramLengths of stmt * stmt

exception UnificationError of u_error

(*---------------------------------------------------------------------------------------*)
type u_value =
  | Empty
  | Fixed of expr
 
type umap = u_value Msym.t

(*---------------------------------------------------------------------------------------*)
let rec unify_exprs umap e1 e2 =
  match e1.e_node, e2.e_node with
  | Eint _, Eint _ -> umap
  | Elocal _, Elocal _ -> umap
  | Evar pv, e2n ->
     let var = symbol_of_pv pv in

     (* Only update a value if it hasn't been fixed previously *)
     let update value =
       match value with
       | None ->
          begin
            match e2n with
            | Evar _ -> None
            | _ -> raise (UnificationError (UE_ExprNotInLockstep (e1, e2)))
          end
       | Some Empty -> Some (Fixed e2)
       | _ -> value
     in

     Msym.change update var umap
  | Eop _, Eop _ -> umap
  | Eapp (f1, a1), Eapp (f2, a2) ->
     let umap = unify_exprs umap f1 f2 in
     List.fold_left (fun umap (e1, e2) -> unify_exprs umap e1 e2) umap (List.combine a1 a2)
  | Equant (_, _, e1), Equant (_, _, e2) ->
     unify_exprs umap e1 e2
  | Elet (_, e1, u1), Elet (_, e2, u2) ->
     let umap = unify_exprs umap e1 e2 in
     unify_exprs umap u1 u2
  | Etuple t1, Etuple t2 ->
     List.fold_left (fun umap (e1, e2) -> unify_exprs umap e1 e2) umap (List.combine t1 t2)
  | Eif (c1, t1, f1), Eif (c2, t2, f2) ->
     let umap = unify_exprs umap c1 c2 in
     let umap = unify_exprs umap t1 t2 in
     unify_exprs umap f1 f2
  | Ematch (c1, p1, _), Ematch (c2, p2, _) ->
     let umap = unify_exprs umap c1 c2 in
     List.fold_left (fun umap (e1, e2) -> unify_exprs umap e1 e2) umap (List.combine p1 p2)
  | Eproj (e1, _), Eproj (e2, _) ->
     unify_exprs umap e1 e2
  | _ -> raise (UnificationError (UE_ExprNotInLockstep (e1, e2)))

(*---------------------------------------------------------------------------------------*)
let rec unify_instrs umap i1 i2 =
 match i1.i_node, i2.i_node with
  | Sasgn(_, e1), Sasgn(_, e2)
  | Srnd(_, e1), Srnd(_, e2) ->
     unify_exprs umap e1 e2
  | Scall(_, _, args1), Scall(_, _, args2) ->
     List.fold_left (fun umap (e1, e2) -> unify_exprs umap e1 e2) umap (List.combine args1 args2)
  | Sif(e1, st1, sf1), Sif(e2, st2, sf2) ->
     let umap = unify_exprs umap e1 e2 in
     let umap = unify_stmts umap st1 st2 in
     unify_stmts umap sf1 sf2
  | Swhile(e1, s1), Swhile(e2, s2) ->
     let umap = unify_exprs umap e1 e2 in
     unify_stmts umap s1 s2
  | Smatch(e1, bs1), Smatch(e2, bs2) ->
     let umap = unify_exprs umap e1 e2 in
     List.fold_left (fun umap (b1, b2) -> unify_stmts umap (snd b1) (snd b2)) umap (List.combine bs1 bs2)
  | Sassert e1, Sassert e2 ->
     unify_exprs umap e1 e2
  | Sabstract _, Sabstract _ -> umap
  | _ -> raise (UnificationError (UE_InstrNotInLockstep (i1, i2)));

and unify_stmts umap s1 s2 =
  let s1n, s2n = s1.s_node, s2.s_node in
  if List.length s1n <> List.length s2n then
    raise (UnificationError (UE_DifferentProgramLengths (s1, s2)));
  List.fold_left (fun umap (i1, i2) -> unify_instrs umap i1 i2) umap (List.combine s1n s2n)

(*---------------------------------------------------------------------------------------*)
(* Given a function definition attempt to unify its body with the statements `sb` 
   and if a return statement is given, also unify it's expression. *)
let unify_func umap fdef sb sr =
  (* Unify the body *)
  let umap = unify_stmts umap fdef.f_body sb in

  (* Unify the return stmt (if it exists) and retrieve its lv *)
  match sr with
  | Some i -> begin
      (* Check that there is a return expression to unify with *)
      if fdef.f_ret = None then
        raise (UnificationError UE_UnexpectedReturn);

      (* Only unify with assignment instructions *)
      match i.i_node with
      | Sasgn (lv, e) -> Some lv, unify_exprs umap (Option.get fdef.f_ret) e
      | _ -> raise (UnificationError UE_InvalidRetInstr)
  end
  | _ -> None, umap
