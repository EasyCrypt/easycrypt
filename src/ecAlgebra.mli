(* -------------------------------------------------------------------- *)
open EcFol
open EcRing
open EcField
open EcDecl
open EcEnv

module RState : sig
  type rstate

  val empty   : rstate
  val add     : LDecl.hyps -> form -> rstate -> int * rstate
  val get     : int -> rstate -> form option
  val update  : rstate -> int list -> form list -> rstate
end

(* -------------------------------------------------------------------- *)
val rapp   : ring -> EcPath.path -> form list -> form
val rzero  : ring -> form
val rone   : ring -> form
val radd   : ring -> form -> form -> form
val ropp   : ring -> form -> form
val rmul   : ring -> form -> form -> form
val rexp   : ring -> form -> int -> form
val rsub   : ring -> form -> form -> form
val rofint : ring -> int -> form

(* -------------------------------------------------------------------- *)
val fzero  : field -> form
val fone   : field -> form
val fadd   : field -> form -> form -> form
val fopp   : field -> form -> form
val fmul   : field -> form -> form -> form
val fexp   : field -> form -> int -> form
val fsub   : field -> form -> form -> form
val finv   : field -> form -> form
val fdiv   : field -> form -> form -> form
val fofint : field -> int -> form

(* -------------------------------------------------------------------- *)
val emb_rzero : ring  -> form
val emb_fzero : field -> form

val emb_rone : ring  -> form
val emb_fone : field -> form

(* -------------------------------------------------------------------- *)
type eq  = form * form
type eqs = eq list

(* -------------------------------------------------------------------- *)
type cring
type cfield

val cring_of_ring   : ring  -> cring
val cfield_of_field : field -> cfield
val ring_of_cring   : cring -> ring 
val field_of_cfield : cfield-> field

(* -------------------------------------------------------------------- *)
val toring : LDecl.hyps -> cring -> RState.rstate -> form -> pexpr * RState.rstate
val ofring : ring -> RState.rstate -> pexpr -> form
val ring_simplify_pe : cring -> (pexpr * pexpr) list -> pexpr -> pexpr

val ring_simplify : LDecl.hyps -> cring -> eqs -> form -> form
val ring_eq : LDecl.hyps -> cring -> eqs -> form -> form -> form

(* -------------------------------------------------------------------- *)
val tofield : EcEnv.LDecl.hyps ->
           cfield ->
           RState.rstate -> form -> fexpr * RState.rstate
val offield : field -> RState.rstate -> fexpr -> form

val field_simplify_pe : 
  cfield -> (pexpr * pexpr) list -> fexpr -> pexpr list * pexpr * pexpr

val field_simplify : LDecl.hyps -> cfield -> eqs -> form -> form list * form * form
val field_eq : LDecl.hyps -> cfield -> eqs -> form -> form -> form list * (form * form) * (form * form)
