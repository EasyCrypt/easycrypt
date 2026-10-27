(* A theory override whose two sides are pristine clones of the same
   theory is replayed as a renaming of the source copy; the result still
   instantiates, and an override whose sides are not pristine takes the
   item-by-item path. *)
require import AllCore.

abstract theory Base.
  op n : int.
  op f (x : int) = x + n.
  axiom n_pos : 0 < n.
end Base.

abstract theory Lower.
  clone import Base as B.
  lemma f_gt (x : int) : x < f x by smt(n_pos).
end Lower.

(* both B are pristine copies of Base *)
abstract theory Upper.
  clone import Base as B.
  clone import Lower as L with theory B <- B.
  lemma f2_gt (x : int) : x < f (f x) by smt(f_gt).
end Upper.

(* the pristine copy still instantiates *)
clone Upper as U with op B.n <- 3 proof B.n_pos by done.

lemma t1 (x : int) : x < U.B.f (U.B.f x) by apply U.f2_gt.

(* the target carries an override: not pristine, replayed item by item *)
abstract theory Upper2.
  clone import Base as B with op n <= 2 proof n_pos by done.
  clone import Lower as L with theory B <- B.
  lemma f2_gt (x : int) : x < f (f x) by smt(f_gt).
end Upper2.

clone Upper2 as U2.

lemma t2 (x : int) : x < U2.B.f (U2.B.f x) by apply U2.f2_gt.

(* the source copy carries an override: not pristine either *)
abstract theory Lower3.
  clone import Base as B with op n <= 2 proof n_pos by done.
  lemma f_gt (x : int) : x < f x by smt(n_pos).
end Lower3.

abstract theory Upper3.
  clone import Base as B with op n <= 2 proof n_pos by done.
  clone import Lower3 as L with theory B <- B.
  lemma f2_gt (x : int) : x < f (f x) by smt(f_gt).
end Upper3.

clone Upper3 as U3.

lemma t3 (x : int) : x < U3.B.f (U3.B.f x) by apply U3.f2_gt.
