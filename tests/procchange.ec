require import AllCore Int Distr.

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
    proc change {1} [1..3] : { x <- 3; }.
    
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
    proc change [1..1] : { x <- x ; }. wp. skip. smt().
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
  proc change {1} [1..1] : { x <$ (dunit x); }.
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
  proc change {1} [1..1] : { 
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
  proc change {1} [1..1] : {
    while (x <> y) {
      x <- x + 1 + 0;
    }
  }.
  proc rewrite {1} 1 /=.
  proc rewrite {2} 1.1 /=. 
  sim.
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
  proc change {1} [^while.1..^while.2] : {
    x <- 2;
  }. wp; skip. smt().
  proc change {2} [^while.1-1] : {
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
    proc change [1..1] : { x <- x; }.
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

theory ProcChangeHoareFrame.
  module M = {
    proc foo(uc: int) = {
      var foo;
      foo <- 1;
      foo <- foo + uc;
      return uc;
    }
  }.

  lemma minimalexamplelemma (a: int):
     hoare [M.foo: arg = a ==> res = a].
  proof.
    proc.
    proc change [1..2] : { foo <- 1 + a; }. auto. auto.
  qed.
end ProcChangeHoareFrame.

theory ProcChangeEquivFrame.
  module M = {
    proc foo1(uc: int) = {
      var foo;
      foo <- 1;
      foo <- foo + uc;
      return uc;
    }

    proc foo2(uc: int) = {
      var foo;
      uc <- uc + 1;
      foo <- 0;
      foo <- foo + uc;
      uc <- uc - 1;
      return uc;
    }
  }.

  lemma minimalexamplelemma (a: int):
     equiv [M.foo1 ~ M.foo2 : ={arg} /\ arg{1} = a ==> ={res} /\ res{1} = a].
  proof.
    proc.
    proc change {1} [1..2] : { foo <- 1 + a; }. auto. 
    conseq (_: ={uc} /\ uc{1} = a /\ uc{2} = a ==> ); 1:auto.
    proc change {2} [1..1] : { uc <- a + 1; }. auto.
    fail proc change {2} [2..3] : { foo <- a + 1; }; smt(). 
  abort.
end ProcChangeEquivFrame.
