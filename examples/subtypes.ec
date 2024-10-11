require import AllCore List.

subtype 'a vector <: n: int> = {
  w : 'a list | size w = n
}.
print vector.

subtype 'a matrix <: rows: int, cols: int> = {
  w : ('a list) list 
  | size w = rows /\ all (fun c => size c = cols) w
}.
print matrix.

op cat <n m : int> (x : {'a vector<: n>}) (y : {'a vector<: m>}) : {'a vector<: (n+m)>}.
print cat.
print cat_spec.

op cat_concr <n m : int> (x : {'a vector<: n>}) (y : {'a vector<: m>}) : {'a vector<: (n+m)>} = x ++ y.    
realize cat_concr_spec.
proof.
move => n m x y.
by rewrite /cat_concr size_cat => -> ->.
qed.

lemma t: size (#|cat_concr [1] [2]) = 2.
proof.
exact (cat_concr_spec 1 1).
qed. 

print t.
