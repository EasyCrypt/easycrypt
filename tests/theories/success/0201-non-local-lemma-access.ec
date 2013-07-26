theory Foo.
  section.
    theory U.
      (* was: axiom foo : true. but could not be found, breaking the test case. *)
      lemma foo : true by trivial.
    end U.
  end section.

  lemma bar : true.
  proof.
    apply U.foo; admit.
  qed.
end Foo.
