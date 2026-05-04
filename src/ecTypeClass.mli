(* -------------------------------------------------------------------- *)
open EcAst
open EcTheory
open EcEnv

(* -------------------------------------------------------------------- *)
val infer : env -> ty -> typeclass -> tcwitness option

(* -------------------------------------------------------------------- *)
(* Like [infer], but the carrier may be left abstract: only the
   typeclass arguments are matched. Returns the matching instance(s)
   with the partial type-substitution that pinned each argument; the
   caller must then unify the carrier with [subst tci_type] and recover
   the witness. Used by the "infer-by-args" strategy of the unifier
   when the carrier is a fresh type univar. *)
val candidates_by_args :
     env -> typeclass
  -> (EcPath.path option * tcinstance * ty option EcIdent.Mid.t) list

(* -------------------------------------------------------------------- *)
(* Flatten the parent chain: [tc; tc.parent; tc.grandparent; ...].
   Args are substituted along the chain. *)
val ancestors : env -> typeclass -> typeclass list

(* -------------------------------------------------------------------- *)
(* Like [ancestors], but each ancestor is paired with the cumulative
   op renaming accumulated along the BFS walk from [tc]. The renaming
   is a list of (ancestor_op_name, local_op_name) pairs. Empty list
   means no renaming (plain inheritance). *)
val ancestors_with_renaming :
  env -> typeclass -> (typeclass * (EcSymbols.symbol * EcSymbols.symbol) list) list
