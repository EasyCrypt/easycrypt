(* pHL `call` (upstream #1124): the bound of the conclusion is interpreted
   in the initial memory, while the specification of the called procedure
   interprets the same formula in the memory the procedure starts from,
   i.e. after the statements preceding the call and with the local
   variables of the callee. A bound that depends on variables written by
   those statements, or on local variables, must be rejected. *)
require import AllCore.

module M = {
  var x, y : bool

  proc f() = { }

  proc g() : bool = { var r; M.x <- true; r <@ f(); return true; }

  proc h() : bool = { var r; M.x <- true; r <@ f(); return M.y; }
}.

(* The bound `b2r M.x` is 0 initially, but 1 when `f` is called; the
   judgment is false (`M.g` returns `true`). *)
lemma bad : phoare[M.g : !M.x ==> res] <= (b2r M.x).
proof.
proc.
fail call (_ : M.x ==> true).
abort.

module N = {
  proc f(x : bool) : bool = { return x; }
  proc g(x : bool) : bool = { var r; r <@ f(!x); return r; }
}.

(* The local `x` of `N.g` would be read as the argument `x` of `N.f`; the
   judgment is false for `x = false`. *)
lemma bad' : phoare[N.g : true ==> res] <= (b2r x).
proof.
proc.
fail call (_ : true ==> res).
abort.

(* A bound on a global variable that the prefix does not write is fine. *)
lemma ok : phoare[M.h : true ==> res] <= (b2r M.y).
proof.
proc.
call (_ : true ==> M.y).
+ proc; case (M.y).
  + by conseq (: _ ==> true : <= 1%r) => [/#|]; auto.
  by conseq (: _ ==> _ : <= 0%r) => [/#|]; hoare; auto.
by auto.
qed.
