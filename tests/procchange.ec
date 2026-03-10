require import AllCore Distr.

(* -------------------------------------------------------------------- *)
theory ProcChangeEmptyRangeAddCode.
  module M = {
    proc f(x : int) = {
      x <- x + 1;
      x <- x + 2;
      x <- x + 3;
    }
  }.
  
  lemma L : hoare[M.f: x = 0 ==> true].
  proof.
  proc.
    proc change [0..0] : [y : int] { x <- 0; y <- x; }.
    by auto.
  abort.
end ProcChangeEmptyRangeAddCode.

theory ProcChangeFullProgram.
  module M = {
    proc f(x : int) = {
      x <- x + 1;
      x <- x + 2;
      x <- x + 3;
    }
  }.
  
  lemma L : hoare[M.f: x = 0 ==> true].
  proof.
  proc.
    proc change [0..100] : [y : int] {
      x <- x + 1;
      x <- x + 2;
      x <- x + 3;
    }.
    by auto.
  abort.
end ProcChangeFullProgram.

theory ProcChangeFrameFail.
  module M = {
    proc f(x : int) = {
      x <- x + 1;
      x <- x + 2;
      x <- x + 3;
    }
  }.
  
  lemma L : hoare[M.f: x = 0 ==> true].
  proof.
  proc.
    proc change [2..2] : [y : int] { x <- 0; y <- x; }.
    fail by auto.
  abort.
end ProcChangeFrameFail.

theory ProcChangeAddCodeFail.
  module M = {
    proc f(x : int) = {
      x <- x + 1;
      x <- x + 2;
      x <- x + 3;
    }
  }.
  
  lemma L : hoare[M.f: x = 2 ==> true].
  proof.
  proc.
    proc change [1..1] : [y : int] { x <- 0; y <- x; }.
    fail by auto.
  abort.
end ProcChangeAddCodeFail.


(* -------------------------------------------------------------------- *)
theory ProcChangeEmptyRangeAddCodeEquiv.
  module M = {
    proc f(x : int) = {
      x <- x + 1;
      x <- x + 2;
      x <- x + 3;
    }
  }.
  
  lemma L : equiv[M.f ~ M.f: x{1} = 0 ==> true].
  proof.
  proc.
    proc change {1} [0..0] : [y : int] { x <- 0; y <- x; }; 1:by auto.
    fail proc change {2} [0..0] : [y : int] { x <- 0; y <- x; }; 1:by auto.
    fail proc change {2} [100..102] : [y : int ] { x <- 0; y <- x; }. (* FIXME: move test *)
  abort.
end ProcChangeEmptyRangeAddCodeEquiv.

theory ProcChangeAssignHoareEquiv.
  module M = {
    proc f(x : int) = {
      x <- x + 0;
    }
  }.
  
  lemma L : hoare[M.f : true ==> true].
  proof.
  proc.
    proc change [0..2] : { x <- x ; }. wp. skip. smt().
  abort.
end ProcChangeAssignHoareEquiv.

(* -------------------------------------------------------------------- *)
theory ProcChangeAssignEquiv.
  module M = {
    proc f(x : int) = {
      x <- 0;
      x <- x + 1;
      x <- x + 2;
      x <- x + 3;
    }
  }.
  
  lemma L : equiv[M.f ~ M.f: true ==> true].
  proof.
  proc.
    proc change {1} [1..4] : [y : int] { y <- 3; x <- y; }.
    wp. skip. smt().
  abort.
end ProcChangeAssignEquiv.


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
  proc change {1} [1..2] : { x <$ (dunit x); }.
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
  proc change {1} [1..2] : { 
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
  proc change {1} [1..2] : {
    while (x <> y) {
      x <- x + 1 + 0;
    }
  }.
  (* proc rewrite {1} 1 /=. *)
  admit. (* FIXME *)
  (*
  proc rewrite {1} 1 /=.
  proc rewrite {2} 1.1 /=. 
  sim.
  *)
  abort.
end ProcChangeWhileEquiv.


(* -------------------------------------------------------------------- *)
theory ProcChangeInWhileEquiv.
  module M = {
    proc f(x : int, y : int) = {
    while (x + 0 <> y) {
        x <- 1;
        x <- x + 1;
        x <- 2;
      }
    }
  }.
  
  lemma L : equiv[M.f ~ M.f : true ==> true].
  proof.
  proc.
  proc change {1} ^while.2 : {
    x <- x + 0 + 1;
  }.
  wp; skip. smt().
  proc change {1} [^while.1..^while.3] : {
    x <- 2;
  }. wp; skip. smt().
  proc change {2} [^while.1+2] : {
    x <- 2;
  }. wp; skip. smt().
  abort.
end ProcChangeInWhileEquiv.


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
    proc change [1..2] : { x <- x; }.
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
  proc change 1 : { x <$ (dunit x); }.
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
  proc change 1 : { 
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
  proc change 1 : {
    while (x <> y) {
      x <- x + 1;
    }
  }.
  proc rewrite {1} ^while /=; sim.
  abort.
end ProcChangeWhileHoare.


(* -------------------------------------------------------------------- *)
theory ProcChangeInWhileHoare.
  module M = {
    proc f(x : int, y : int) = {
      while (x + 0 <> y) {
        x <- x + 1;
      }
    }
  }.
  
  lemma L : hoare[M.f : true ==> true].
  proof.
  proc.
  proc change ^while.1 : {
    x <- x + 0 + 1;
  }.
  wp; skip. smt().
  abort.
end ProcChangeInWhileHoare.

