require import AllCore List.

(* Binder slot `i` declared via `#<...>`; form slot `f` has `i` as a    *)
(* binder dep, so inside the body `f` appears as a function; at the    *)
(* call site `f` is written as an open form over the user-chosen name. *)
notation #mapI #< i : int > (n : int) (f : i ==> int)
  "[" i " : " n " : " f "] " =
  map f (iota_ 0 n).

(* Expansion equals the fully-expanded form with the user-chosen binder. *)
lemma t1 : #mapI [i : 3 : i * 10] = map (fun i => i * 10) (iota_ 0 3).
proof. by trivial. qed.

lemma t2 : #mapI [k : 4 : k + 1] = map (fun k => k + 1) (iota_ 0 4).
proof. by trivial. qed.

(* Two binder slots with two form-slot deps. *)
notation #matI #< i : int, j : int > (n : int) (m : int) (f : i, j ==> int)
  "[" i ", " j " : " n " : " m " : " f "] " =
  map (fun i => map (fun j => f i j) (iota_ 0 m)) (iota_ 0 n).

lemma t3 :
  #matI [a, b : 2 : 2 : a * 10 + b]
  = map (fun a => map (fun b => a * 10 + b) (iota_ 0 2)) (iota_ 0 2).
proof. by trivial. qed.

(* Comprehension-style: the form slot `f` appears BEFORE the binder `x` in the
   template; binding is two-pass so dep idents are available regardless of
   template order. *)
notation #mapC #< x : int > (f : x ==> int) (s : int list)
  "[" f " | " x " : " s "] " =
  map f s.

lemma t4 : #mapC [x + 1 | x : [1; 2; 3]] = [2; 3; 4].
proof. by trivial. qed.
