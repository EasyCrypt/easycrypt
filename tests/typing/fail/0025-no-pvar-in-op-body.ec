type t.

module X = {
  var x : t
}.

op fail : t = X.x.
