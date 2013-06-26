type t.

theory T.
  section.
    local module M = {
      var x : t
    }.

    module G = {
      fun f() : t = { return M.x; }
    }.
  end section.
end T.
