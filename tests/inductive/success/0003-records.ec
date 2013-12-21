(* -------------------------------------------------------------------- *)
type 'a myrecord = { x : 'a; y : 'a; }.

op r (x y : 'a) = {| x = x; y = y; |}.

lemma L (x y : 'a) : (r x y).`x = x.
proof -strict. by rewrite /r. qed.

lemma LE (v : 'a myrecord): v = {| x = v.`x; y = v.`y; |}.
proof -strict. by elim v. qed.

op id (x : 'a) = x.

lemma Lid (x y : 'a) : id (r x y).`x = x.
proof -strict. by rewrite /id /r. qed.
