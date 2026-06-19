(* See handlers/ecm4.py and ecm4.m4

   This example uses a whole quotation using the m4 macro processor to
   include the m4 file ecm4.m4 and then evaluate the macro call
   Test(split; last right, left, right), which generates a sequence of
   EasyCrypt tactics, which, after processing, leave two sub-goals,
   which are later solved by trivial.

   Replace "{%!" with "{%!*" to debug the macro call.

   Note that the "{%!" is terminated by the next ".". The function of
   the "!%}." is to force Proof General to display the next open
   goal, after the expansion of the macro call is processed by
   EasyCrypt. *)

require import AllCore.

lemma foo : ((false \/ true) \/ false) /\ (false \/ true).
proof.
{%! ecm4 ecm4.m4
Test(split; last right, left, right).
!%}.
trivial.
trivial.
qed.

lemma foo_debug : ((false \/ true) \/ false) /\ (false \/ true).
proof.
{%!* ecm4 ecm4.m4
Test(split; last right, left, right).
!%}.
trivial.
trivial.
qed.
