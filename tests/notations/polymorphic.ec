require import AllCore List.

(* Polymorphic pair with two independent type parameters. *)
notation #ppair ['a 'b] (a : 'a) (b : 'b) "[" a ", " b "] " = (a, b).

lemma t1 : #ppair [1, true] = (1, true).
proof. by trivial. qed.

lemma t2 (x : int) (y : bool) : #ppair [x, y] = (x, y).
proof. by trivial. qed.

(* Polymorphic list-mapper — 'a and 'b are independent. *)
notation #pmap ['a 'b] (f : 'a -> 'b) (xs : 'a list) "[" f " : " xs "] " =
  map f xs.

lemma t3 : #pmap [(fun x => x + 1) : [1; 2; 3]] = [2; 3; 4].
proof. by trivial. qed.

lemma t4 : #pmap [(fun (x : int) => (x, x)) : [1; 2]] = [(1, 1); (2, 2)].
proof. by trivial. qed.

(* Polymorphic with binder slot. *)
notation #piota ['a] #< i : int > (n : int) (f : i ==> 'a)
  "[" i " : " n " : " f "] " =
  map f (iota_ 0 n).

lemma t5 (n : int) :
  #piota [i : n : i + 10] = map (fun i => i + 10) (iota_ 0 n).
proof. by trivial. qed.
