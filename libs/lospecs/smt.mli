(* -------------------------------------------------------------------- *)
(* SMT (Bitwuzla) decision procedures for AIG circuits. *)

(* A solving context bundles a backend solver with per-query memoization.
   Create one per query: a fresh solver gives assertion isolation. The
   procedures assert into [ctx] and return a verdict; [model] reads the
   satisfying assignment back from the same context, so it is only
   meaningful right after a query that left the solver satisfiable (a [sat]
   that returned [true], or a refuted [equiv]/[valid]), and before [ctx] is
   reused. *)
module BWZ : sig
  type ctx

  val create : unit -> ctx

  (* [equiv ctx r1 r2 pcond] is [true] iff [r1] and [r2] agree on every
     input satisfying the 1-bit precondition [pcond]. *)
  val equiv : ctx -> Circuit.reg -> Circuit.reg -> Aig.node -> bool

  val sat   : ctx -> Aig.node -> bool
  val valid : ctx -> Aig.node -> bool

  (* The satisfying assignment, as [(input-id, value)] pairs over the input
     bit-groups the last query materialized. *)
  val model : ctx -> (int * string) list
end
