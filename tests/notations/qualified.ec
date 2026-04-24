require import AllCore.

theory Src.
  notation #pair (a : int) (b : int) "[" a ", " b "] " = (a, b).
end Src.

clone Src as Dst.

(* Qualified call without `import`. *)
lemma qualified_call (x y : int) : Dst.#pair [x, y] = (x, y).
proof. by trivial. qed.

(* Deeper qualifier. *)
theory Outer.
  theory Inner.
    notation #twice (a : int) "[" a "] " = a + a.
  end Inner.
end Outer.

lemma deep_qualified (x : int) : Outer.Inner.#twice [x] = x + x.
proof. by trivial. qed.

(* Bare call after explicit import still works. *)
import Src.

lemma bare_after_import (x y : int) : #pair [x, y] = (x, y).
proof. by trivial. qed.
