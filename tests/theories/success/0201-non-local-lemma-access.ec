theory Foo.
  section.
    theory U.
      axiom foo : true.
    end U.
  end section.

  lemma bar : true.
  proof.
    apply U.foo; admit.
  qed.
end Foo.
