type t.

theory T.
  section.
    local module M = {
      var x : t
    }.

    module G = {
      proc f() : t = { return M.x; }
    }.
  end section.
end T.
