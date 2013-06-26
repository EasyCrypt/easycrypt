theory T.
  module type I = {}.

  section.
    local module M : I = {}.

    module F(X : I) = {}.

    module K = F(M).
  end section.
end T.
