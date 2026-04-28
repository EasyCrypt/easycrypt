require import AllCore List.

(* A notation with one optional group containing one form slot that has *)
(* a default. The call site may omit the ` | P` suffix.                 *)
notation #filter ['a] #< i : 'a >
    (xs : 'a list)
    (P : i ==> bool = predT)
  "[" i " : " xs ("| " P)? "]" =
  filter P xs.

(* With the optional group: P is user-supplied. *)
lemma with_P (xs : int list) :
  #filter [ i : xs | 0 <= i ] = filter (fun i => 0 <= i) xs.
proof. by trivial. qed.

(* Without the optional group: P defaults to predT. *)
lemma without_P (xs : int list) :
  #filter [ i : xs ] = filter predT xs.
proof. by trivial. qed.

(* Two independent optional groups in one notation (different puncts). *)
notation #take2 (xs : int list) (lo : int = 0) (hi : int = 1000)
  "[" xs ("| " lo)? ("; " hi)? "]" =
  take (hi - lo) (drop lo xs).

lemma no_opt (xs : int list) :
  #take2 [ xs ] = take (1000 - 0) (drop 0 xs).
proof. by trivial. qed.

lemma both_opt (xs : int list) :
  #take2 [ xs | 5 ; 20 ] = take (20 - 5) (drop 5 xs).
proof. by trivial. qed.

lemma only_second (xs : int list) :
  #take2 [ xs ; 7 ] = take (7 - 0) (drop 0 xs).
proof. by trivial. qed.
