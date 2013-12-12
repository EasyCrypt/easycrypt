theory Foo.
  section.
    theory U.
      local axiom foo : true.
    end U.
  end section.

  lemma bar : true.
  proof -strict.
    apply U.foo; admit.
  qed.
end Foo.
