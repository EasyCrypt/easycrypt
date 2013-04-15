theory T.
  type t.
  op default:t.
end T.

clone T as U with
  type t = int,
  op default = 0.
