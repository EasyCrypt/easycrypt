require import AllCore List.

notation #pair ['a 'b] (a : 'a) (b : 'b) "[" a ", " b "] " = (a, b).

(* Three levels deep, mixing template punct and form-slot content. *)
lemma deep3 (x y z w : int) :
  #pair [#pair [x, y], #pair [z, w]] = ((x, y), (z, w)).
proof. by trivial. qed.

lemma deep4 (x y z w v : int) :
  #pair [#pair [x, #pair [y, z]], #pair [w, v]] = ((x, (y, z)), (w, v)).
proof. by trivial. qed.

(* Multi-binder notation where a single form slot depends on both binders. *)
notation #ij #< i : int, j : int > (f : i, j ==> int)
  "[" i ", " j " : " f "] " =
  f 10 20.

lemma ij_call : #ij [a, b : a * b + 1] = 201.
proof. by trivial. qed.

lemma ij_call_eq : #ij [i, j : i + j] = (fun (i j : int) => i + j) 10 20.
proof. by trivial. qed.

(* Three binders, three different form slots depending on subsets of them. *)
notation #rank #< i : int, j : int, k : int >
  (fij : i, j ==> int)
  (fjk : j, k ==> int)
  (fik : i, k ==> int)
  "[" i ", " j ", " k " : " fij " | " fjk " | " fik "] " =
  fij 1 2 + fjk 2 3 + fik 1 3.

lemma rank_check :
  #rank [a, b, c : a + b | b * c | a - c] = (1 + 2) + (2 * 3) + (1 - 3).
proof. by trivial. qed.

(* Deep nesting + binder slot. The inner #pair provides the value for the *)
(* form slot; the tuple result matches a polymorphic `'a = int * int`.    *)
notation #mapI ['a] #< i : int > (n : int) (f : i ==> 'a)
  "[" i " : " n " : " f "] " =
  map f (iota_ 0 n).

lemma nested_binder (n : int) :
  #mapI [i : n : #pair [i, i + 1]]
  = map (fun i => (i, i + 1)) (iota_ 0 n).
proof. by trivial. qed.
