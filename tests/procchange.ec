require import AllCore Distr.

(* -------------------------------------------------------------------- *)
theory ProcChangeAssignEquiv.
  module M = {
    proc f(x : int) = {
      x <- x + 0;
    }
  }.
  
  lemma L : equiv[M.f ~ M.f: true ==> true].
  proof.
  proc.
    proc change {1} 1 1 : { x <- x; }.
    
    wp. skip. smt().
  abort.
end ProcChangeAssignEquiv.

theory ProcChangeAssignHoareEquiv.
  module M = {
    proc f(x : int) = {
      x <- x + 0;
    }
  }.
  
  lemma L : hoare[M.f : true ==> true].
  proof.
  proc.
    proc change 1 1 : { x <- x ; }. wp. skip. smt().
  abort.
end ProcChangeAssignHoareEquiv.

(* -------------------------------------------------------------------- *)
theory ProcChangeSampleEquiv.
  module M = {
    proc f(x : int) = {
      x <$ dunit (x + 0);
    }
  }.
  
  lemma L : equiv[M.f ~ M.f : true ==> true].
  proof.
  proc.
  proc change {1} 1 1 : { x <$ (dunit x); }.
  rnd. skip. smt().
  abort.
end ProcChangeSampleEquiv.

(* -------------------------------------------------------------------- *)
theory ProcChangeIfEquiv.
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
  proc change {1} 1 1 : { 
    if (x = y) {
      x <- y;
    } else {
      x <- -y;
    }
}. wp. skip. smt().
  abort.
end ProcChangeIfEquiv.

(* -------------------------------------------------------------------- *)
theory ProcChangeWhileEquiv.
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
  proc change {1} 1 1 : {
    while (x <> y) {
      x <- x + 1;
    }
  }.
  admit. (* FIXME *)
  abort.
end ProcChangeWhileEquiv.

(* -------------------------------------------------------------------- *)
theory ProcChangeAssignHoare.
  module M = {
    proc f(x : int) = {
      x <- x + 0;
    }
  }.
  
  lemma L : hoare[M.f: true ==> true].
  proof.
  proc.
    proc change 1 1 : { x <- x; }.
    wp; skip; smt().
  abort.
end ProcChangeAssignHoare.

(* -------------------------------------------------------------------- *)
theory ProcChangeSampleHoare.
  module M = {
    proc f(x : int) = {
      x <$ dunit (x + 0);
    }
  }.
  
  lemma L : hoare[M.f: true ==> true].
  proof.
  proc.
  proc change 1 1 : { x <$ (dunit x); }.
  rnd; skip; smt().
  abort.
end ProcChangeSampleHoare.

(* -------------------------------------------------------------------- *)
theory ProcChangeIfHoare.
  module M = {
    proc f(x : int, y : int) = {
      if (x + 0 = y) {
        x <- y;
      } else {
        x <- -y;
      }
    }
  }.
  
  lemma L : hoare[M.f: true ==> true].
  proof.
  proc.
  proc change 1 1 : { 
    if (x = y) {
      x <- y;
    } else {
      x <- -y;
    }
}. wp. skip. smt().
  abort.
end ProcChangeIfHoare.

(* -------------------------------------------------------------------- *)
theory ProcChangeWhileHoare.
  module M = {
    proc f(x : int, y : int) = {
      while (x + 0 <> y) {
        x <- x + 1;
      }
    }
  }.
  
  lemma L : hoare[M.f: true ==> true].
  proof.
  proc.
  proc change 1 1 : {
    while (x <> y) {
      x <- x + 1;
    }
  }.
  admit. (* FIXME *)
  abort.
end ProcChangeWhileHoare.
