require import AllCore Distr.

(* -------------------------------------------------------------------- *)
theory ProcChangeAssign.
  module M = {
    proc f(x : int) = {
      x <- x + 0;
    }
  }.
  
  lemma L : equiv[M.f ~ M.f : true ==> true].
  proof.
  proc.
  proc change {1} 1 : x.
  - smt().
  abort.
end ProcChangeAssign.

(* -------------------------------------------------------------------- *)
theory ProcChangeSample.
  module M = {
    proc f(x : int) = {
      x <$ dunit (x + 0);
    }
  }.
  
  lemma L : equiv[M.f ~ M.f : true ==> true].
  proof.
  proc.
  proc change {1} 1 : (dunit x).
  - smt().
  abort.
end ProcChangeSample.

(* -------------------------------------------------------------------- *)
theory ProcChangeIf.
  module M = {
    proc f(x : int, y : int) = {
      if (x + 0 = y) {
        x <- y;
      } else {
        x <- -y;
      }
    }
  }.
  
  lemma L : equiv[M.f ~ M.f : true ==> true].
  proof.
  proc.
  proc change {1} 1 : (x = y).
  - smt().
  abort.
end ProcChangeIf.

(* -------------------------------------------------------------------- *)
theory ProcChangeWhile.
  module M = {
    proc f(x : int, y : int) = {
      while (x + 0 <> y) {
        x <- x + 1;
      }
    }
  }.
  
  lemma L : equiv[M.f ~ M.f : true ==> true].
  proof.
  proc.
  proc change {1} 1 : (x <> y).
  - smt().
  abort.
end ProcChangeWhile.
