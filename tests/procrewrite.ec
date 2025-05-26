(* -------------------------------------------------------------------- *)
require import AllCore Distr.

(* -------------------------------------------------------------------- *)
theory ProcRewriteAssign.
  module M = {
    proc f(a : int, b : int) : int = {
      var c : int <- a * (a + b);
      return c;
    }
  }.
  
  lemma L a0 b0 : hoare[M.f : arg = (a0, b0) ==> res = (b0 + a0) * a0].
  proof.
  proc.
  proc rewrite 1 addzC.
  proc rewrite 1 mulzC.
  auto=> />.
  qed.
end ProcRewriteAssign.

(* -------------------------------------------------------------------- *)
theory ProcRewriteSample.
  module M = {
    proc f(a : int, b : int) : int = {
      var c : int;

      c <$ dunit (a * (a + b));
      return c;
    }
  }.
  
  lemma L a0 b0 : hoare[M.f : arg = (a0, b0) ==> res = (b0 + a0) * a0].
  proof.
  proc.
  proc rewrite 1 addzC.
  proc rewrite 1 mulzC.
  by auto=> /> ?; rewrite supp_dunit.
  qed.
end ProcRewriteSample.

(* -------------------------------------------------------------------- *)
theory ProcRewriteIf.
  module M = {
    proc f(a : int, b : int) : int = {
      var c : int;

      if (a + b = b + a) {
        c <- 0;
      } else {
        c <- 1;
      }
      return c;
    }
  }.
  
  lemma L : hoare[M.f : true ==> res = 0].
  proof.
  proc.
  proc rewrite 1 addzC.
  by auto=> />.
  qed.
end ProcRewriteIf.

(* -------------------------------------------------------------------- *)
theory ProcRewriteWhile.
  module M = {
    proc f(a : int, b : int) : int = {
      var c : int <- 0;

      while (a + b <> b + a) {
        c <- c + 1;
      }
      return c;
    }
  }.
  
  lemma L : hoare[M.f : true ==> res = 0].
  proof.
  proc.
  proc rewrite ^while addzC.
  by rcondf ^while; auto.
  qed.
end ProcRewriteWhile.

(* -------------------------------------------------------------------- *)
theory ProcRewritePrhl.
  module M = {
    proc f(a : int, b : int) : int = {
      var c : int <- a * (a + b);
      return c;
    }

    proc g(a: int, b:int) : int = {
      var c : int <- (a * a) + (a * b);
      return c;
    }
  }.
  
  lemma L a0 b0 : equiv[M.f ~ M.g : ={arg} /\ arg{1} = (a0, b0) ==> ={res} /\ res{1} = (b0 + a0) * a0].
  proof.
  proc.
    proc rewrite {1} 1 addzC.
  proc rewrite {2} 1 addzC.
  proc rewrite {1} 1 mulzC.
  auto=> />.
  ring.
  qed.
end ProcRewritePrhl.
