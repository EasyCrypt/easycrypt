require import AllCore.

(* Negative: registering two instances on the same carrier where a
   shared ancestor's ops would have to disagree must hard-error with
   a "diamond coherence violation" message. *)

type class parent = {
  op my_f : parent
  axiom ax : forall (x : parent), x = x
}.

type class child <: parent = {
  op my_g : child
  axiom bx : forall (x : child), x = x
}.

op f_zero : int = 0.
op f_one  : int = 1.
op g_zero : int = 0.

instance parent as parent_int with int
  op my_f = f_zero.

realize ax by trivial.

(* This second instance binds parent's op my_f to f_one, which
   conflicts with the existing parent_int instance binding it to
   f_zero. Phase B coherence check must hard-error. *)
instance child as child_int with int
  op my_f = f_one
  op my_g = g_zero.

realize ax by trivial.
realize bx by trivial.
