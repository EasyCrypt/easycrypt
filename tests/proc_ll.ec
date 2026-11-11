require import AllCore.

module type O = {
  proc o (x:int) : int
}.

module type A (O:O) = {
  proc f () : bool
}.

module O1 = {
  var bad : bool
  var s : int
  proc o (x:int) = {
    if (x = 10) { 
      bad <- true;
      x <- 100;
    } 
    s <- s + x;
    return x;
  }

}.

module O2 = {
  import var O1

  proc o (x:int) = {
    if (x = 10) { 
      bad <- true;
      x <- 200;
    } 
    s <- s + x;
    return x;
  }
}.

section SECTION.

declare module A <: A {-O1}.

equiv proc_ll : A(O1).f ~ A(O2).f : 
  if O1.bad{2} then ={O1.bad} 
  else ={glob A, O1.bad, O1.s} 
  ==> 
  if O1.bad{2} then ={O1.bad} 
  else ={res, glob A, O1.bad, O1.s}.
proof.
  proc @[ll] O1.bad (={O1.bad, O1.s}) (={O1.bad}) => />.
  (* A(O1).f is lossless *)
  + admit.
  (* A(O2).f is lossless *)
  + admit.
  (* ???? *)
  + smt().
  (* Oracle are upto bad *)
  + by proc; auto => />.
  (* O1 preserves invariant once bad is set *)
  + by move=> &2 h; proc; auto => />; rewrite h.
  (* O2 preserves invariant once bad is set *)
  by move=> &1; proc; auto => />; rewrite h.
qed.

equiv proc_ll1 : A(O1).f ~ A(O2).f : 
  if O1.bad{2} then ={O1.bad} 
  else ={glob A, O1.bad, O1.s} 
  ==> 
  if O1.bad{2} then ={O1.bad} 
  else ={res, glob A, O1.bad, O1.s}.
proof.
  proc *.
  call @[ll] (_: O1.bad, ={O1.bad, O1.s}, ={O1.bad}).
  (* A(O1).f is lossless *)
  + admit.
  (* A(O2).f is lossless *)
  + admit.
  (* Oracle are upto bad *)
  + by proc; auto => />.
  (* O1 preserves invariant once bad is set *)
  + by move=> &2 h; proc; auto => />; rewrite h.
  (* O2 preserves invariant once bad is set *)
  + by move=> &1; proc; auto => />; rewrite h.
  by auto.
qed.

