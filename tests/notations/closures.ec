require import AllCore List.

(* A notation whose form slots are function-typed — user supplies lambdas. *)
notation #map (f : int -> int) (xs : int list) "[" f " : " xs "] " =
  map f xs.

lemma t1 : #map [(fun x => x + 1) : [1; 2; 3]] = [2; 3; 4].
proof. by trivial. qed.

(* Nested notation use — the inner #map expands first. *)
lemma t2 (xs : int list) :
  #map [(fun x => x * 2) : #map [(fun x => x + 1) : xs]]
  = map (fun x => x * 2) (map (fun x => x + 1) xs).
proof. by trivial. qed.
