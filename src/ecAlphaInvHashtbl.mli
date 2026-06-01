(* -------------------------------------------------------------------- *)
open EcAst

(* -------------------------------------------------------------------- *)
(* Hash-table over formulas keyed by alpha-equivalence (and conversion)
   in a fixed hypotheses context [Ctxt.hyps]. The hash is invariant under
   the renaming of bound variables, so alpha-equivalent formulas share a
   table entry. *)
module Make (Ctxt : sig val hyps : EcEnv.LDecl.hyps end) : sig
  (* The formula-keyed hash-table (keys compared up to alpha-equivalence). *)
  module Htbl : Batteries.Hashtbl.S with type key = form

  (* Clear the table (and the internal de-Bruijn ident cache). *)
  val clear : 'a Htbl.t -> unit
end
