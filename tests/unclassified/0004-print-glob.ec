require import Real.

module M1 = {
  var a : real
}.

module M2 = {
  var x : int
  var y : bool
  proc foo() : unit = {
    M1.a = 1%r;
  }
}.

(* prints x, y, M1.a *)
print glob M2.

(* we match against x, y, a *)
pred p (m : glob M2) = let (x,y,a) = m in x = 1 /\ y = true /\ a = 1%r.