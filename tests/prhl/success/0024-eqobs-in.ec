require import Int.

module G1 = {
  var u : int

  proc g(x : int) : int = {
    if (u < 10) {
      x = x + 1;
      x = x + 2;
      x = x - 1;
      u = u + 1 + x;
    }
    return x;
  }

  proc f(x : int) : int = {
    x = x + 3;
    x = x + 1 - 4;
    x = g(x);
    return x;
  }

  proc main (x:int) : int = { 
    var y, z : int;
    u = 10;
    y = f(x);
    z = f(y);
    return z;
  }
}.

module G2 = {
  var u : int

  proc g(x : int) : int = {
    if (u < 10) {
      x = x + 1;
      x = x + 1;
      u = u + 1 + x;
    }
    return x;
  }

  proc f(x : int) : int = {
    x = g(x);
    return x;
  }

  proc main (x:int) : int = { 
    var y, z : int;
    u = 10;
    y = f(x);
    z = f(y);
    return z;
  }
}.

lemma G1_G2_g :
  equiv[G1.g ~ G2.g :
        ={x} /\ G1.u{1} = G2.u{2} ==>
        ={res} /\ G1.u{1} = G2.u{2}].
proof -strict.
proc; wp; skip; smt.
qed.

lemma G1_G2_f :
  equiv[G1.f ~ G2.f :
        ={x} /\ G1.u{1} = G2.u{2} ==>
        ={res} /\ G1.u{1} = G2.u{2}].
proof -strict.
proc.
call (_ : ={x} /\ G1.u{1} = G2.u{2} ==> ={res} /\ G1.u{1} = G2.u{2}).
apply G1_G2_g.
wp; skip; smt.
qed.

lemma G1_G2_main :
  equiv[G1.main ~ G2.main : ={x} ==> ={res}].
proof -strict.
proc.
sim (G1.u{1} = G2.u{2}) true : (={z}).
apply G1_G2_f.
qed.




