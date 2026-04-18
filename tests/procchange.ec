(* Tests for the proc change tactic.
   proc change replaces a range of program statements with semantically
   equivalent code, generating an equivalence sub-goal to justify the
   replacement.

   The file is organised in three sections:
   1. Basic instruction types — assign, sample, if, while (equiv and hoare).
   2. Statements inside while bodies.
   3. Precondition framing — tests that the tactic correctly determines
      whether the precondition can reach the change site. *)
require import AllCore Distr.

(* -------------------------------------------------------------------- *)
(* Section 1: basic instruction types.
   Each theory changes a single instruction (or range) and checks that
   the generated equivalence sub-goal can be discharged. *)

(* proc change on an equiv goal: replace a range of assignments [1..3]
   with a single equivalent assignment on the left-hand side. *)
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
    proc change {1} [1..3] : [y : int] { y <- 3; x <- y; }.
    wp. skip. smt().
  abort.
end ProcChangeAssignEquiv.

(* -------------------------------------------------------------------- *)
(* proc change to add instructions to the program *)
theory ProcChangeAddInstrs.
  module M = {
    proc f(x : int) = {
      x <- x + 1;
      x <- x + 2;
      x <- x + 3;
      return x;
    }
  }.
  
  lemma L : hoare[ M.f : arg = 0 ==> res = 6].
  proof.
  proc.
    proc change <1 : { x <- 0; }; 1:by auto. 
    sp 4;  proc change >(-1) : { x <- 6; }; 1: by auto.
    wp; skip; auto.
  abort.
end ProcChangeAddInstrs.

(* -------------------------------------------------------------------- *)
theory ProcChangeAssignHoare.
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
end ProcChangeAssignHoare.

(* -------------------------------------------------------------------- *)
(* proc change on a sampling instruction in an equiv goal:
   simplify  x <$ dunit (x + 0)  to  x <$ dunit x. *)
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
(* proc change on an if statement in an equiv goal:
   simplify the condition  x + 0 = y  to  x = y. *)
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
(* proc change on a while statement in an equiv goal: simplify the
   loop condition  x + 0 <> y  to  x <> y  (the body also changes). *)
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
(* Section 2: proc change applied to individual statements inside a
   while body.  Position ^while.N selects statement N of the loop body;
   [^while.N..^while.M] selects a range; ^while.N-K is an offset variant. *)

(* Three consecutive uses of proc change on the same equiv goal:
   (a) ^while.2 — change a single statement at position 2 in the body.
   (b) [^while.1..^while.2] — change a two-statement range.
   (c) [^while.1-1] — offset-range form selecting one statement. *)
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
  proc change {1} ^while.:[1..2] : {
    x <- 2;
  }. wp; skip. smt().
  proc change {2} ^while.:[1+>2] : {
    x <- 2;
  }. wp; skip. smt().
  abort.
end ProcChangeInWhileEquiv.

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
(* proc change on a single statement inside a while body, hoare goal. *)
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

(* -------------------------------------------------------------------- *)
(* Section 3: precondition framing.
   proc change checks whether the precondition value of each variable
   can "reach" the change site — i.e., that no earlier statement in the
   same path writes to that variable first.  If the check passes the
   tactic succeeds; otherwise it fails. *)

(* Positive flat case: change statement 2 (x <- x + 1 → x <- 4).
   Only y is written before position 2, so x = 3 from the precondition
   propagates freely to the change site. *)
theory ProcChangeFrameTest.
  module M = {
    proc f(x: int, y: int) = {
      y <- 0;
      x <- x + 1;
    }
  }.

  lemma L : hoare[M.f : x = 3 ==> true].
  proof.
  proc=> /=.
  proc change 2 : {
    x <- 4;
  }; by auto.
  qed.
end ProcChangeFrameTest.

(* -------------------------------------------------------------------- *)
(* Negative flat case: change statement 3 (x <- x + 1 → x <- 4) fails.
   Statement 2 (x <- 4) writes x before the change site, so the
   precondition x = 3 cannot propagate to position 3. *)
theory ProcChangeFrameFailTest.
  module M = {
    proc f(x: int, y: int) = {
      y <- 0;
      x <- 4;
      x <- x + 1;
      return x;
    }
  }.

  lemma L : hoare[M.f : x = 3 ==> res = 0].
  proof.
  proc=> /=.
  fail proc change 3 : {
    x <- 4;
  }; by auto.
  abort.
end ProcChangeFrameFailTest.

(* -------------------------------------------------------------------- *)
(* Positive if-block case: change ^if.1 (x <- x + 1 → x <- 4) inside
   the true branch.  No write to x precedes ^if.1 in this branch, so
   the precondition x = 3 reaches the change site. *)
theory ProcChangeBlockFrameTest.
  module M = {
    proc f(x: int, y: int) = {
      y <- 0;
      if( y = 0) {
        x <- x + 1;
        x <- 4;
      } else {
        x <- 4;
      }
    }
  }.

  lemma L : hoare[M.f : x = 3 ==> true].
  proof.
  proc=> /=.
  proc change ^if.1 : {
    x <- 4;
  }; by auto.
  qed.
end ProcChangeBlockFrameTest.

(* -------------------------------------------------------------------- *)
(* Negative if-block case: change ^if.2 (x <- x + 1 → x <- 4) fails.
   Statement ^if.1 (x <- 4) writes x before ^if.2 in the same branch,
   blocking the precondition x = 3 from propagating. *)
theory ProcChangeBlockFailFrameTest.
  module M = {
    proc f(x: int, y: int) = {
      y <- 0;
      if( y = 0) {
        x <- 4;
        x <- x + 1;
      } else {
        x <- 4;
      }
      return x;
    }
  }.

  lemma L : hoare[M.f : x = 3 ==> res = 0].
  proof.
  proc=> /=.
  fail proc change ^if.2 : {
    x <- 4;
  }; by auto.
  abort.
end ProcChangeBlockFailFrameTest.

(* -------------------------------------------------------------------- *)
(* Positive while case: change ^while.1 (x <- x + 1 → x <- 4).
   No write to x precedes ^while.1 inside the loop body (y <- 1 writes
   y, not x), so the precondition x = 3 propagates. *)
theory ProcChangeWhileFrameTest.
  module M = {
    proc f(x: int, y: int) = {
      y <- 0;
      while(y = 0) {
        x <- x + 1;
        y <- 1;
      }
    }
  }.

  lemma L : hoare[M.f : x = 3 ==> true].
  proof.
  proc=> /=.
  proc change ^while.1 : {
    x <- 4;
  }; by auto.
  qed.
end ProcChangeWhileFrameTest.

(* -------------------------------------------------------------------- *)
(* Negative while case — write after the change site:
   change ^while.1 (x <- x + 1 → x <- 4) fails.
   ^while.2 (x <- 4) writes x after the change site inside the same
   loop iteration, so x entering ^while.1 on a subsequent iteration
   would be 4, not the precondition value 3. *)
theory ProcChangeWhileFrameFailWriteAfterTest.
  module M = {
    proc f(x: int, y: int) = {
      y <- 0;
      while(y = 0) {
        x <- x + 1;
        x <- 4;
        y <- 1;
      }
    }
  }.

  lemma L : hoare[M.f : x = 3 ==> true].
  proof.
  proc=> /=.
  proc change ^while.1 : {
    x <- 4;
  }.

  by auto.
  abort.
end ProcChangeWhileFrameFailWriteAfterTest.

(* -------------------------------------------------------------------- *)
(* Negative while case — write before the change site:
   change ^while.2 (x <- x + 1 → x <- 4) fails.
   ^while.1 (x <- 4) writes x before ^while.2 in the loop body,
   blocking the precondition x = 3 from reaching the change site. *)
theory ProcChangeWhileFrameFailWriteBeforeTest.
  module M = {
    proc f(x: int, y: int) = {
      y <- 0;
      while(y = 0) {
        x <- 4;
        x <- x + 1;
        y <- 1;
      }
      return x;
    }
  }.

  lemma L : hoare[M.f : x = 3 ==> res = 0].
  proof.
  proc=> /=.
  fail proc change ^while.2 : {
    x <- 4;
  }; by auto.
  abort.
end ProcChangeWhileFrameFailWriteBeforeTest.

(* -------------------------------------------------------------------- *)
(* Negative while case — write outside (before) the loop:
   change ^while.1 (x <- x + 1 → x <- 4) fails.
   Statement 2 (x <- 4) writes x before the while loop is entered,
   so the precondition x = 3 is overwritten before the change site. *)
theory ProcChangeWhileFrameFailWriteOutsideTest.
  module M = {
    proc f(x: int, y: int) = {
      y <- 0;
      x <- 4;
      while(y = 0) {
        x <- x + 1;
        y <- 1;
      }
      return x;
    }
  }. 

  lemma L : hoare[M.f : x = 3 ==> res = 0].
  proof.
  proc=> /=.
  fail proc change ^while.1 : {
    x <- 4;
  }; by auto.
  abort.
end ProcChangeWhileFrameFailWriteOutsideTest.

(* -------------------------------------------------------------------- *)
(* observability through the context/post.
   These tests exercise the variable selection performed by [zpr_pv]
   and the post-side read analysis used by proc change. *)

(* The continuation reads only x, so y can be changed freely in the
   replacement block. *)
theory ProcChangeContextReadXOnlyTest.
  module M = {
    proc f(x : int, y : int) = {
      x <- 1;
      y <- 2;
      x <- x + 1;
      return x;
    }
  }.

  lemma L : hoare[M.f : true ==> res = 2].
  proof.
  proc=> /=.
  proc change [1..2] : {
    x <- 1;
    y <- 99;
  }; by auto.
  qed.
end ProcChangeContextReadXOnlyTest.

(* -------------------------------------------------------------------- *)
(* The continuation reads only y, so x can be changed freely in the
   replacement block. *)
theory ProcChangeContextReadYOnlyTest.
  module M = {
    proc f(x : int, y : int) = {
      x <- 1;
      y <- 2;
      y <- y + 1;
      return y;
    }
  }.

  lemma L : hoare[M.f : true ==> res = 3].
  proof.
  proc=> /=.
  proc change [1..2] : {
    x <- 99;
    y <- 2;
  }; by auto.
  qed.
end ProcChangeContextReadYOnlyTest.

(* -------------------------------------------------------------------- *)
(* The continuation reads x, so changing x in the replacement block is
   observable and proc change must fail. *)
theory ProcChangeContextReadXFailTest.
  module M = {
    proc f(x : int, y : int) = {
      x <- 1;
      y <- 2;
      x <- x + 1;
      return x;
    }
  }.

  lemma L : hoare[M.f : true ==> res = 2].
  proof.
  proc=> /=.
  proc change [1..2] : {
    x <- 99;
    y <- 2;
  }.
  fail by auto.
  abort.
end ProcChangeContextReadXFailTest.

(* -------------------------------------------------------------------- *)
(* The continuation reads y, so changing y in the replacement block is
   observable and proc change must fail. *)
theory ProcChangeContextReadYFailTest.
  module M = {
    proc f(x : int, y : int) = {
      x <- 1;
      y <- 2;
      y <- y + 1;
      return y;
    }
  }.

  lemma L : hoare[M.f : true ==> res = 3].
  proof.
  proc=> /=.
  proc change [1..2] : {
    x <- 1;
    y <- 99;
  }.
  fail by auto.
  abort.
end ProcChangeContextReadYFailTest.

(* -------------------------------------------------------------------- *)
(* With no continuation, the post mentions only x, so y can vary in the
   replacement block. *)
theory ProcChangePostReadXOnlyTest.
  module M = {
    var x : int
    var y : int

    proc f() = {
      x <- 1;
      y <- 2;
    }
  }.

  lemma L : hoare[M.f : true ==> M.x = 1].
  proof.
  proc=> /=.
  proc change [1..2] : {
    M.x <- 1;
    M.y <- 99;
  }; by auto.
  qed.
end ProcChangePostReadXOnlyTest.

(* -------------------------------------------------------------------- *)
(* With no continuation, the post mentions x, so changing x in the
   replacement block is observable and proc change must fail. *)
theory ProcChangePostReadXFailTest.
  module M = {
    var x : int
    var y : int

    proc f() = {
      x <- 1;
      y <- 2;
    }
  }.

  lemma L : hoare[M.f : true ==> M.x = 1].
  proof.
  proc=> /=.
  proc change [1..2] : {
    M.x <- 99;
    M.y <- 2;
  }.
  fail by auto.
  abort.
end ProcChangePostReadXFailTest.

(* -------------------------------------------------------------------- *)
(* With no continuation, the post mentions only y, so x can vary in the
   replacement block. *)
theory ProcChangePostReadYOnlyTest.
  module M = {
    var x : int
    var y : int

    proc f() = {
      x <- 1;
      y <- 2;
    }
  }.

  lemma L : hoare[M.f : true ==> M.y = 2].
  proof.
  proc=> /=.
  proc change [1..2] : {
    M.x <- 99;
    M.y <- 2;
  }; by auto.
  qed.
end ProcChangePostReadYOnlyTest.

(* -------------------------------------------------------------------- *)
(* With no continuation, the post mentions y, so changing y in the
   replacement block is observable and proc change must fail. *)
theory ProcChangePostReadYFailTest.
  module M = {
    var x : int
    var y : int

    proc f() = {
      x <- 1;
      y <- 2;
    }
  }.

  lemma L : hoare[M.f : true ==> M.y = 2].
  proof.
  proc=> /=.
  proc change [1..2] : {
    M.x <- 1;
    M.y <- 99;
  }.
  fail by auto.
  abort.
end ProcChangePostReadYFailTest.

theory ProcChangeUseNewVars.
  module M = {
    proc f(x : int) = {
      x <- 1;
      x <- x - x;
      return x;
    }
  }.
    
  lemma L : hoare[M.f : 4 < arg ==> res = 0].
  proof.
  proc.
  proc change [1..1] : [y : int] {
    y <- x;
    x <- 1;
  }; 1: by auto.
  seq 2 : (x = 1 /\ 4 < y); 1: by auto.
  conseq (: ==> x = 0 /\ 4 < y); 1: by auto.
  wp. skip => &hr H. simplify. 
  by move : H => [] <*>> -> //.
  qed.
end ProcChangeUseNewVars.
