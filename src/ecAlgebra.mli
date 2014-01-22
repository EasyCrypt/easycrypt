(* -------------------------------------------------------------------- *)
open EcFol

(* -------------------------------------------------------------------- *)
type ring = {
  r_type  : EcTypes.ty;
  r_zero  : EcPath.path;
  r_one   : EcPath.path;
  r_add   : EcPath.path;
  r_opp   : EcPath.path option;
  r_mul   : EcPath.path;
  r_exp   : EcPath.path option;
  r_sub   : EcPath.path option;
  r_embed : [ `Direct | `Embed of EcPath.path | `Default];
  r_bool  : bool; (* true means boolean ring *)
}

val ring_equal : ring -> ring -> bool
(* -------------------------------------------------------------------- *)
type field = {
  f_ring : ring;
  f_inv  : EcPath.path;
  f_div  : EcPath.path option;
}
val field_equal : field -> field -> bool

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

(* -------------------------------------------------------------------- *)
val ring_simplify : cring -> eqs -> form -> form
val ring_eq : cring -> eqs -> form -> form -> form

(* -------------------------------------------------------------------- *)
val field_simplify : cfield -> eqs -> form -> form list * form * form
val field_eq : cfield -> eqs -> form -> form -> form list * (form * form) * (form * form)
