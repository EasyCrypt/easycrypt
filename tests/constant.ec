cnst k : int.

type 'a list'.

cnst Nil : 'a list'.

cnst Nil1 : 'b list' = Nil.

cnst Nil2 : int list' = Nil.

cnst Nil3 : int list' = Nil1.

cnst Nil4 : bool list' = Nil1.

(* TODO: this should be rejected *)
cnst bad : 'a.
