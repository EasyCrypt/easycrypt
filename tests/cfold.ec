(* -------------------------------------------------------------------- *)
require import AllCore Distr.

(* -------------------------------------------------------------------- *)
theory CfoldStopIf.
  module M = {
    proc f(a : int, b : int) : int = {
      var c : int;
      var d : int;
      
      c <- 0;
      d <- c + 1;
      c <- b + a;
      
      if (a + b = c) {
        c <- 0;
        a <- c;
      } else {
        c <- 1;
        b <- c;
      }
      return c;
    }
  }.
  
  lemma L : hoare[M.f : true ==> res = 0].
  proof.
    proc.
    cfold 1.
    by auto => /> ?; apply addzC.
  qed.
end CfoldStopIf.

(* -------------------------------------------------------------------- *)
theory CfoldTuple.
  module M = {
    proc f( x : int * int) : int = {
      var a : int;
      var b : int;
      var c : int <- 0;

      x <- (0, 0);
      a <- x.`1;
      b <- snd x;

      while (a + b <> b + a) {
        c <- c + 1;
      }
      return c;
    }
  }.
  
  lemma L : hoare[M.f : true ==> res = 0].
  proof.
  proc.
  cfold 2.
  by rcondf ^while; auto.
  qed.
end CfoldTuple.

theory CfoldN.
  module M = {
    proc f(a : int, b : int) : int = {
      var c : int;
      c <- 0;
      a <- c;
      c <- 1;
      b <- 2;
      c <- 2;
      a <- 3;
      c <- 3;
      if (a <> b) {
        c <- 0;
      } 
      return c;
    }
  }.

  lemma L : hoare[M.f : true ==> res = 0].
  proof.
  proc.
  cfold 1 !4.
  by auto => />.
  qed.
end CfoldN.

theory CfoldWhileUnroll.
  module M = {
    proc f(a : int, b : int) : int = {
      var c : int;
    c <- 0;
    c <- c + 1;
      c <- 0;
      while (c < 10) {
        a <- c;
        c <- c + 1;
      }
      b <- c;
      if (a <> b) {
        c <- 0;
      }
      return c;
    }
  }.

  lemma L : hoare[M.f : true ==> res = 0].
  proof.
    proc.
    cfold 1.
    unroll for 2.
    cfold 1.
    by auto => />.
  qed.
end CfoldWhileUnroll.
