type ('a, 'b) t = { x : 'a; y : 'b; }.

op a : int.
op o = let {| x = x; |} = {| x = a; y = 1; |} in x.

lemma L : 0 = a => o = 0.
proof. by rewrite /o /= => <-. qed.
