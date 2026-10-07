require import AllCore Xreal.

(* `match C k` on ehoare goals: the prefix obligation is a hoare judgement
   on the boolean part [P] of the precondition [P `|` f], and the framed
   condition is added to [P]. *)

module N = {
  var o : int option

  proc h() : int = {
    var r;
    r <- 0;
    match o with
    | None   => {}
    | Some v => { r <- v; }
    end;
    return r;
  }

  proc w() : int = {
    var r;
    o <- Some 1;
    r <- 0;
    match o with
    | None   => {}
    | Some v => { r <- v; }
    end;
    return r;
  }
}.

(* Framed: [N.o] is independent of the prefix [r <- 0]. *)
lemma ehoare_framed :
  ehoare [N.h : (N.o = Some 1) `|` (1%xr) ==> (res%r)%xr].
proof.
proc.
match Some 2.
+ by auto => /#.
by wp; skip => &hr; apply xle_cxr_r => /> /#.
qed.

(* Unframed: the prefix writes [N.o]. *)
lemma ehoare_unframed :
  ehoare [N.w : (true) `|` (1%xr) ==> (res%r)%xr].
proof.
proc.
match Some 3.
+ by auto => /#.
by wp; skip => &hr; apply xle_cxr_r => /> /#.
qed.
