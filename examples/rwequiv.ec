require import AllCore Distr.

type t, u.

module BiSample = {
  proc sample(dt : t distr, du : u distr) = {
    var t, u;

    t <$ dt;
    u <$ du;
    return (t, u);
  }
}.

module Prod = {
  var s : unit

  proc sample(dt : t distr, du : u distr) = {
    var tu;

    tu <$ dt `*` du;
    return tu;
  }
}.

equiv eq: BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof. admitted.

equiv eq': BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof.
proc.
transitivity {1} { (t,u) <@ BiSample.sample(dt,du); }
  (={dt,du} ==> ={t,u})
  (={dt,du} ==> (t,u){1} = tu{2});
    [4:transitivity {2} { tu <@ Prod.sample(dt,du); }
    (={dt,du} ==> (t,u){1} = tu{2})
    (={dt,du} ==> ={tu})];
  [ 3,7:inline *; try (auto; done)
  |   6:call eq]; trivial.

+ move=> &1 &2 H; exists dt{1} du{1}; move: H => //.
+ move=> &1 &2 H; exists dt{2} du{2}; move: H => //.
by auto=> /> [].
qed.

pred P. pred Q.
axiom PQ: P => Q.

require Distr.
equiv eq2: BiSample.sample ~ Prod.sample: arg{2} = arg{1} /\ P ==> res{2} = res{1} /\ Q.
proof.
proc.
rewrite equiv [{1} eq (dt, du) (t, u) (dt, du) tu].
by auto=> /> /PQ -> [].
qed.

equiv eq3: Prod.sample ~ BiSample.sample: arg{2} = arg{1} /\ P ==> res{2} = res{1} /\ Q.
proof.
proc.
rewrite equiv [{2} eq (dt, du) (t,u) (dt, du) tu].
by auto=> /> /PQ -> [].
qed.


op dst : int distr.
module M = {
  proc f(b: bool) : int = {
    var y;
    y <$ dst;
    if (b) {
      y <$ dst;
    }
    return y;
  }

  proc g(s: bool): int = {
    var a, b;
    a <$ dst;
    b <$ dst;
    return (if s then b else a);
  }
}.

op db : bool distr.
module N = {
  proc foo(): int = {
    var s, x, y;
    s <- true;
    x <- 1;
    y <$ dst;
    if (s) {
      y <$ dst;
    }
    x <- y + x;
    return x;
  }
  proc bar(): int = {
    var b, w, x, y, z;
    b <- true;
    x <- 2;
    z <- 1;
    y <$ dst;
    w <$ dst;
    y <- if b then w else y;
    x <- y + x - z;
    return x;
  }
}.

equiv doubleSample: M.f ~ M.g: ={arg} ==> ={res}.
proof.
admitted.

equiv test: N.foo ~ N.bar: true ==> ={res}.
proof.
proc.
sp; wp 2 3.
rewrite equiv [{1} doubleSample (s) y (b) y]. 
sim.
qed.

equiv test': N.foo ~ N.bar: true ==> ={res}.
proof.
proc.
sp; wp 2 3.
transitivity {1} { y <@ M.f(s); }
  (={s, x} ==> ={y, x})
  (x{2} = 2 /\ x{1} = 1 /\ s{1} = true /\ b{2} = true /\ z{2} = 1 ==>
    y{1} + x{1} = y{2} + x{2} - z{2}).
+ move=> &1 &2 H; exists s{1} x{1}; move: H => //.
+ move=> />. 
+ by inline*; sim.
transitivity {2} {y <@ M.g(b); }
  (x{2} = 2 /\ x{1} = 1 /\ s{1} = true /\ b{2} = true /\ z{2} = 1 ==>
    y{1} + x{1} = y{2} + x{2} - z{2})
  (={b, x, z} ==> ={y, x, z}).
+ move=> &1 &2 H; exists b{2} x{2} z{2}; move: H => //.
+ move=> />.
+ by call doubleSample.
by inline*; auto.
qed.
