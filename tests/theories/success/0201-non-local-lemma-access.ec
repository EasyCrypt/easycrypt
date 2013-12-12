theory Foo.
  section.
    theory U.
      lemma foo : true by admit.
    end U.
  end section.

  lemma bar : true.
  proof -strict.
    apply U.foo; admit.
  qed.
end Foo.
