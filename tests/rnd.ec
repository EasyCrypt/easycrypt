prover "alt-ergo".

game G0 = {
  fun F() : int = {
    var z : int = [0..0];
    return z;
  } 
}.

(* Should not be provable *)
equiv minimal : G0.F ~ G0.F : true ==> res{1} < res{2}.
proof.
 rnd (z + 1), (z - 1); trivial. 
abort.

game G1 = {
  fun F() : bool = {
    var z : int = [0..0];
    return true;
  } 
}.

game G2 = {
  fun F() : bool = {
    var z : int = [0..0];
    var b : bool = false;
    if (z = 1) { b = true; }
    return b;
  } 
}.

(* Should not be provable *)
equiv forward : G1.F ~ G2.F : (true).
proof.
 rnd>> (z -> 1 - z); trivial.
abort.

(* Should not be provable *)
equiv backward : G1.F ~ G2.F : (true).
 wp; rnd (z -> 1 - z); trivial.
abort.


game G3 = {
  var z : int
  fun F() : int  = {
    z = [0..1];
    return z;
  } 
}.

game G4 = {
  var z : int
  fun F() : int  = {
    z = [1..2];
    return z;
  } 
}.

(* Should be provable *)
equiv different : G3.F ~ G4.F : true ==> z{2} = z{1} + 1.
proof.
 rnd (z -> z + 1), (z -> z - 1).
 trivial.
abort.

(* Should not be provable *)
equiv range_fwd : G3.F ~ G4.F : true ==> 1 <= z{1} && z{1} <= 2.
proof.
 rnd>>; trivial.
abort.

(* Should not be provable *)
equiv range_bwd : G3.F ~ G4.F : true ==> 1 <= z{1} && z{1} <= 2.
proof.
 rnd; trivial.
abort.

(* Should not be provable *)
equiv equality : G3.F ~ G4.F : (true).
proof.
 rnd>>; trivial.
abort.


cnst a, b, c, d : int.

op Q_ : (int, int) -> bool.
pred Q(a,b:int) = Q_(a,b).

op f    : int -> int.
op finv : int -> int.

axiom f_finv : 
  forall (x:int), a <= x => x <= b => 
    c <= f(x) && f(x) <= d && finv(f(x)) = x.

axiom finv_f : 
  forall (y:int), c <= y => y <= d => 
     a <= finv(y) && finv(y) <= b && f(finv(y)) = y.

game G5 = {
  var z : int
  fun F() : int  = {
    z = [a..b];
    return z;
  } 
}.

game G6 = {
  var z : int
  fun F() : int  = {
    z = [c..d];
    return z;
  } 
}.

axiom Q_valid : forall (x:int), a <= x => x <= b => Q(x, f(x)).

(* Should be provable *)
equiv test_wp : G5.F ~ G6.F : true ==> Q(z{1},z{2}).
proof.
 rnd (x -> f(x)), (x -> finv(x)).
 trivial.
abort.

(* Should be provable *)
equiv test_sp : G5.F ~ G6.F : true ==> Q(z{1},z{2}).
proof.
 rnd>> (x -> f(x)), (x -> finv(x)).
 trivial.
abort.

(* Should be provable *)
equiv test_sp : G5.F ~ G6.F : Q(z{1},z{2}) ==>
 z{2} = f(z{1}) && a <= z{1} && z{1} <= b && c <= z{2} && z{2} <= d &&
 exists (u,v:int), Q(u, v).
proof.
 rnd>> (x -> f(x)), (x -> finv(x)).
 trivial.
abort.
