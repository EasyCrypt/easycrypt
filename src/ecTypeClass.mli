(* -------------------------------------------------------------------- *)
open EcAst
open EcTheory
open EcEnv

(* -------------------------------------------------------------------- *)
exception NoMatch

(* -------------------------------------------------------------------- *)
val infer : env -> ty -> typeclass -> tcwitness option

(* -------------------------------------------------------------------- *)
(* Match [pattern] (with free [Tvar]s listed in [params]) against [ty]
   and return the resulting substitution. Raises [NoMatch] on shape
   mismatch.                                                            *)
val ty_match :
     env -> EcIdent.t list
  -> pattern:ty -> ty:ty
  -> ty option EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
(* Build one [tcwitness] per entry of [tcs] for a carrier [body],
   suitable for plugging into the witness slot of an [add_tydef]
   binding. Each witness is queried via [infer]; on lookup failure,
   falls back to a [`Abs body_path] / [`Var a] placeholder so the
   substitution preserves the pre-fix shape (no regression for
   TC-free callers). *)
val witnesses_for_body :
     env -> ty -> typeclass list -> tcwitness list

(* -------------------------------------------------------------------- *)
(* All matching instances as witnesses (vs. [infer] which returns the
   first). Used to detect ambiguity from multi-flavor inheritance. *)
val infer_all : env -> ty -> typeclass -> tcwitness list

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

(* Like [ancestors_with_renaming], but also returns the label path
   traversed from [tc] down to each ancestor. The label path is
   outermost-first: [["comring"; "Mul"; "monoid"]] for the walk
   [boolring -> comring -> mulmonoid (as Mul) -> monoid]. Empty
   label path for [tc] itself. *)
val ancestors_with_labels :
     env
  -> typeclass
  -> (typeclass
      * (EcSymbols.symbol * EcSymbols.symbol) list
      * EcSymbols.symbol list)
     list

(* -------------------------------------------------------------------- *)
(* Compose two cumulative renamings. [outer] is the renaming on a
   parent edge (grandparent op → parent op); [inner] is the
   already-accumulated renaming on the child side (parent op → child
   op). Result maps grandparent op names to child op names. *)
val compose_renaming :
     outer:(EcSymbols.symbol * EcSymbols.symbol) list
  -> inner:(EcSymbols.symbol * EcSymbols.symbol) list
  -> (EcSymbols.symbol * EcSymbols.symbol) list

(* -------------------------------------------------------------------- *)
(* [op_preserved ren n] is true iff applying the cumulative
   ancestor→child renaming [ren] to op name [n] leaves it as [n] (or
   doesn't mention [n] at all). Used to filter parent-DAG paths when
   resolving a TC witness for a specific named op: only paths whose
   cumulative renaming preserves the op name expose that op under
   the same name at the carrier site. *)
val op_preserved :
  (EcSymbols.symbol * EcSymbols.symbol) list -> EcSymbols.symbol -> bool
