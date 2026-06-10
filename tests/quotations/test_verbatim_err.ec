require import Int.

(* Error-location test.  The body references an undefined identifier
   'no_such_op'.  The 'fail' prefix asserts that expanding and checking this
   sentence raises an error -- so the file as a whole still succeeds while
   exercising the failure path.

   The quotation is a FRAGMENT; the terminating '.' is written after %}.

   When run without 'fail', EasyCrypt reports the error at the ORIGINAL
   location of 'no_such_op' inside the quotation (column-precise, via the
   verbatim segment map). *)
fail {% verbatim op broken : int = no_such_op + 1 %}.
