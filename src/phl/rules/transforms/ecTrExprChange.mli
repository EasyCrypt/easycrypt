(* -------------------------------------------------------------------- *)
open EcAst
open EcMatching.Position

(* ==================================================================== *)
(* Catalogue entry (trusted)                                            *)

(* The expressions of the range, in program order (see [exprs]): each one
   is either unchanged ([None]) or replaced ([Some (ys, e')]), [e'] being
   stated over the local identifiers [ys], one per match-arm local in
   scope of the expression (in the order of [exprs]). *)
type tr_expr_change = {
  trec_range : nm_codegap_range option;   (* the range [p : [s..f)]
                                             (resolved, possibly nested);
                                             [None]: the whole statement *)
  trec_exprs : (EcIdent.t list * expr) option list;
                                          (* the replacements, in program
                                             order *)
}

(* [TrExprChange { trec_range = r; trec_exprs = cs }] — replaces
   expressions of the instructions of the range [r] (of the whole
   statement when [r] is [None]), at any depth (guards and bodies of
   [if] / [while], discriminants and arms of [match]):

     c = C[b]   ~~>   c' = C[b']    (b' is b with e_i replaced by e_i')

   The expressions of [b] are enumerated in program order ([exprs]), each
   with the match-arm locals [xs_i] in scope at its occurrence (those of
   the enclosing arms of [r] first). The list [cs] has one element per
   expression: [None] leaves [e_i] unchanged; [Some (ys_i, e_i')] replaces
   [e_i] by [e_i'[ys_i := xs_i]]. One obligation per replaced expression,
   in program order:

     OExprEq { oee_locals = ys_i : tys_i; oee_lhs = e_i[xs_i := ys_i];
               oee_rhs = e_i' }

   i.e. [forall &m, forall ys_i, e_i[xs_i := ys_i] = e_i'], [tys_i] being
   the types of [xs_i]. Same memory.

   Side conditions, for each replaced [e_i]: [e_i'] has the type of [e_i];
   [ys_i] has the length of [xs_i]; the [ys_i] are pairwise distinct and
   none of them is free in [e_i] other than as one of the [xs_i]; no local
   of [xs_i] that is not in [ys_i] is free in [e_i'] (so that the
   renamings capture nothing). Fails with "invalid code position" when [r]
   is not a range of [c], and with "invalid expression change" when [cs]
   does not have one element per expression or a side condition does not
   hold. *)
type EcPlTransform.transform += TrExprChange of tr_expr_change

(* ==================================================================== *)
(* Enumeration (shared with the derived tactic)                         *)

(* [exprs] is the enumeration of the entry: [exprs f acc s] folds [f
   locals] over the expressions of [s] in program order, [locals] being
   the match-arm locals in scope (on top of [?locals]), mapping each
   expression to the result of [f]. *)
val exprs :
     ?locals:(EcIdent.t * ty) list
  -> ((EcIdent.t * ty) list -> 'a -> expr -> 'a * expr)
  -> 'a -> instr list -> 'a * instr list

(* [locals_of_path p]: the match-arm locals in scope at the zipper path
   [p], outermost first. *)
val locals_of_path : EcMatching.Zipper.ipath -> (EcIdent.t * ty) list
