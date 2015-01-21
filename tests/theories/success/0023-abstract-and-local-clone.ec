(* -------------------------------------------------------------------- *)
abstract theory T.
  abstract theory U.
    module X = { }.
  end U.
end T.

section.
  local clone T as T'.
end section.
