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

op cat (n m : int) (x : {'a vector<: n>}) (y : {'a vector<: m>}) : {'a vector<: (n+m)>}.

print cat.
print cat_spec.

op cat_concr (n m : int) (x : {'a vector<: n>}) (y : {'a vector<: m>}) : {'a vector<: (n+m)>} = x ++ y.

print cat_concr.
print cat_concr_spec.

lemma t: size (cat 1 1 [1] [2]) = 2.
proof.
exact cat_spec.
qed.

print t.
