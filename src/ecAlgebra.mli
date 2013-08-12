(* -------------------------------------------------------------------- *)
open EcFol

(* -------------------------------------------------------------------- *)
type ring = {
  r_type   : EcTypes.ty;
  r_zero   : EcPath.path;
  r_one    : EcPath.path;
  r_add    : EcPath.path;
  r_opp    : EcPath.path;
  r_mul    : EcPath.path;
  r_exp    : EcPath.path;
  r_sub    : EcPath.path option;
  r_intmul : [ `Embed | `IntMul of EcPath.path ];
}

(* -------------------------------------------------------------------- *)
type field = {
  f_ring : ring;
  f_inv  : EcPath.path;
  f_div  : EcPath.path option;
}

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
