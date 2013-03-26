theory T.
  type t.
  cnst default:t.
end T.

clone T as U with
  type t = int,
  cnst default = 0.
