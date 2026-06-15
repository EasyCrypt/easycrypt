op gen ['a]: bool = true.

theory T.
axiom ax : gen<:bool>.
end T.

lemma lem: gen<:'a> by done.

clone T as T' with
axiom ax <- lem.