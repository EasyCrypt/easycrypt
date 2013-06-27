type t.

theory T.
  section.
    local module M = {
      var x : t

      fun f() : t = { return x; }
    }.

    lemma L : equiv[M.f ~ M.f : true ==> true].
    proof. admit.
  end section.
end T.
