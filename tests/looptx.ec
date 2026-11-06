require import AllCore Xreal.

(* Loop transformations (fission, fusion, unroll, splitwhile) in every
   logic: each one replaces the program by an equivalent one. The equiv
   lemmas check the transformed program against its expected form with
   [sim]. *)

exception e1.

module M = {
  var x, y : int
  var b : bool
  var o : int option

  proc f() = {
    var i;
    i <- 0;
    while (i < 10) {
      x <- x + 1;
      y <- y + 2;
      i <- i + 1;
    }
  }

  (* [f] after [fission 2 @ 1, 2]. *)
  proc f_fis() = {
    var i;
    i <- 0;
    while (i < 10) {
      x <- x + 1;
      i <- i + 1;
    }
    i <- 0;
    while (i < 10) {
      y <- y + 2;
      i <- i + 1;
    }
  }

  (* [f] after [unroll 2]. *)
  proc f_unroll() = {
    var i;
    i <- 0;
    if (i < 10) {
      x <- x + 1;
      y <- y + 2;
      i <- i + 1;
    }
    while (i < 10) {
      x <- x + 1;
      y <- y + 2;
      i <- i + 1;
    }
  }

  (* [f] after [splitwhile 2 : (i < 5)]. *)
  proc f_split() = {
    var i;
    i <- 0;
    while (i < 10 /\ i < 5) {
      x <- x + 1;
      y <- y + 2;
      i <- i + 1;
    }
    while (i < 10) {
      x <- x + 1;
      y <- y + 2;
      i <- i + 1;
    }
  }

  (* The loop of [f] under a conditional (both branches), a match and a
     loop. *)
  proc g() = {
    var i, j;
    if (b) {
      i <- 0;
      while (i < 10) {
        x <- x + 1;
        y <- y + 2;
        i <- i + 1;
      }
    } else {
      x <- 0;
      i <- 0;
      while (i < 10) {
        x <- x + 1;
        y <- y + 2;
        i <- i + 1;
      }
    }
    match o with
    | None => { }
    | Some v => {
        i <- v;
        while (i < 10) {
          x <- x + 1;
          y <- y + 2;
          i <- i + 1;
        }
      }
    end;
    j <- 0;
    while (j < 2) {
      i <- 0;
      while (i < 10) {
        x <- x + 1;
        y <- y + 2;
        i <- i + 1;
      }
      j <- j + 1;
    }
  }

  (* [g] after fission in the then branch, unroll in the else branch,
     splitwhile in the match branch and fission then fusion in the
     loop. *)
  proc g_r() = {
    var i, j;
    if (b) {
      i <- 0;
      while (i < 10) {
        x <- x + 1;
        i <- i + 1;
      }
      i <- 0;
      while (i < 10) {
        y <- y + 2;
        i <- i + 1;
      }
    } else {
      x <- 0;
      i <- 0;
      if (i < 10) {
        x <- x + 1;
        y <- y + 2;
        i <- i + 1;
      }
      while (i < 10) {
        x <- x + 1;
        y <- y + 2;
        i <- i + 1;
      }
    }
    match o with
    | None => { }
    | Some v => {
        i <- v;
        while (i < 10 /\ x < 3) {
          x <- x + 1;
          y <- y + 2;
          i <- i + 1;
        }
        while (i < 10) {
          x <- x + 1;
          y <- y + 2;
          i <- i + 1;
        }
      }
    end;
    j <- 0;
    while (j < 2) {
      i <- 0;
      while (i < 10) {
        x <- x + 1;
        y <- y + 2;
        i <- i + 1;
      }
      j <- j + 1;
    }
  }

  (* Error paths. *)
  proc h() = {
    var i;
    x <- 0;
    i <- 0;
    while (i < 10) {
      x <- x + 1;
      y <- y + x;
      i <- i + 1;
      b <$ {0,1};
    }
    i <- 0;
    while (i < 10) {
      y <- y + 1;
      i <- i + 1;
      b <$ {0,1};
    }
    i <- 0;
    while (i < 11) {
      y <- y + 1;
      i <- i + 2;
    }
  }

  proc k() = {
    var i;
    i <- 0;
    while (i < 10) {
      x <- x + 1;
      i <- i + 1;
    }
    i <- 1;
    while (i < 10) {
      y <- y + 1;
      i <- i + 1;
    }
  }

  (* For [unroll for]. *)
  proc u() = {
    var i;
    i <- 0;
    while (i < 3) {
      x <- x + i;
      i <- i + 1;
    }
  }
}.

(* -------------------------------------------------------------------- *)
(* equiv, both sides: the transformed program is the expected one.      *)

lemma equiv_fission_left : equiv [M.f ~ M.f_fis : ={glob M} ==> ={glob M}].
proof. proc; fission{1} 2 @ 1, 2; sim. qed.

lemma equiv_fission_right : equiv [M.f_fis ~ M.f : ={glob M} ==> ={glob M}].
proof. proc; fission{2} 2!1 @ 1, 2; sim. qed.

lemma equiv_fusion_left : equiv [M.f_fis ~ M.f : ={glob M} ==> ={glob M}].
proof. proc; fusion{1} 2 @ 1, 1; sim. qed.

lemma equiv_fusion_right : equiv [M.f ~ M.f_fis : ={glob M} ==> ={glob M}].
proof. proc; fusion{2} 2!1 @ 1, 1; sim. qed.

lemma equiv_unroll : equiv [M.f ~ M.f_unroll : ={glob M} ==> ={glob M}].
proof. proc; unroll{1} 2; sim. qed.

lemma equiv_unroll_right : equiv [M.f_unroll ~ M.f : ={glob M} ==> ={glob M}].
proof. proc; unroll{2} ^while; sim. qed.

lemma equiv_splitwhile : equiv [M.f ~ M.f_split : ={glob M} ==> ={glob M}].
proof. proc; splitwhile{1} 2 : (i < 5); sim. qed.

lemma equiv_splitwhile_right : equiv [M.f_split ~ M.f : ={glob M} ==> ={glob M}].
proof. proc; splitwhile{2} -1 : (i < 5); sim. qed.

(* Nested positions: then / else branches, match branch, loop body. *)
lemma equiv_nested : equiv [M.g ~ M.g_r : ={glob M} ==> ={glob M}].
proof.
proc.
fission{1} 1.2 @ 1, 2.
unroll{1} 1?3.
splitwhile{1} 2#Some.2 : (M.x < 3).
fission{1} 4.2 @ 2, 2.
fusion{1} 4.2 @ 2, 0.
sim.
qed.

lemma equiv_nested_right : equiv [M.g_r ~ M.g : ={glob M} ==> ={glob M}].
proof.
proc.
fission{2} 1.2 @ 1, 2.
unroll{2} 1?3.
splitwhile{2} 2#Some.2 : (M.x < 3).
sim.
qed.

(* -------------------------------------------------------------------- *)
(* hoare (exceptional postconditions kept), ehoare, phoare.             *)

lemma hoare_looptx : hoare [M.f : true ==> M.x = 0 | e1 => M.y = 0].
proof.
proc.
fission 2 @ 1, 2.
fusion 2 @ 1, 1.
unroll 2.
splitwhile 3 : (i < 5).
abort.

lemma hoare_looptx_nested : hoare [M.g : true ==> true].
proof.
proc.
fission 1.2 @ 1, 2.
fusion 1.2 @ 1, 1.
unroll 1?3.
splitwhile 2#Some.2 : (M.x < 3).
fission 4.2 @ 2, 2.
by trivial.
qed.

lemma ehoare_looptx : ehoare [M.f : 1%xr ==> 1%xr].
proof.
proc.
fission 2 @ 1, 2.
fusion 2 @ 1, 1.
unroll 2.
splitwhile 3 : (i < 5).
abort.

lemma ehoare_looptx_nested : ehoare [M.g : 1%xr ==> 1%xr].
proof.
proc.
fission 1.2 @ 1, 2.
unroll 1?3.
splitwhile 2#Some.2 : (M.x < 3).
fission 4.2 @ 2, 2.
abort.

lemma phoare_looptx : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
fission 2 @ 1, 2.
fusion 2 @ 1, 1.
unroll 2.
splitwhile 3 : (i < 5).
abort.

lemma phoare_looptx_nested : phoare [M.g : true ==> M.x = 0] <= 1%r.
proof.
proc.
fission 1.2 @ 1, 2.
unroll 1?3.
splitwhile 2#Some.2 : (M.x < 3).
fission 4.2 @ 2, 2.
abort.

(* Closed proofs, so that the proof-nodes are checked (EC_RECHECK). *)
lemma ehoare_looptx_closed : ehoare [M.g : 1%xr ==> 0%xr].
proof.
proc.
fission 1.2 @ 1, 2.
fusion 1.2 @ 1, 1.
unroll 1?3.
splitwhile 2#Some.2 : (M.x < 3).
by trivial.
qed.

lemma phoare_looptx_closed : phoare [M.g : false ==> true] = 1%r.
proof.
proc.
fission 1.2 @ 1, 2.
fusion 1.2 @ 1, 1.
unroll 1?3.
splitwhile 2#Some.2 : (M.x < 3).
by exfalso.
qed.

(* unroll for: derived (rcond, wp, seq, conseq, cfold). *)
lemma hoare_unroll_for : hoare [M.u : M.x = 0 ==> M.x = 3].
proof.
proc.
unroll for 2.
by auto.
qed.

lemma equiv_unroll_for : equiv [M.u ~ M.u : ={M.x} ==> ={M.x}].
proof.
proc.
unroll for{1} 2.
unroll for*{2} 2.
by auto.
qed.

(* -------------------------------------------------------------------- *)
(* Error paths.                                                         *)

lemma hoare_fission_errors : hoare [M.h : true ==> true].
proof.
proc.
fail fission 3 @ 2, 1.     (* second offset lower than the first *)
fail fission 2 @ 1, 2.     (* not a loop *)
fail fission 10 @ 1, 2.    (* invalid code position *)
fail fission 10 @ 2, 1.    (* invalid code position, before the offsets *)
fail fission 3!3 @ 1, 2.   (* not headed by 3 instructions *)
fail fission 3 @ 1, 5.     (* invalid offsets range *)
fail fission 3!1 @ 1, 2.   (* independence: c2 reads x, written by c1 *)
fail fission 3!1 @ 2, 3.   (* independence: b reads i, written by c2 *)
fail fission 3!0 @ 2, 2.   (* independence: c3 writes i, read by b, not
                              written by the (empty) prelude *)
fail fission 3 @ 2, 2.     (* epilog samples *)
fail fission 5!1 @ 0, 1.   (* epilog samples (2nd loop) *)
fail fission {1} 3 @ 1, 2. (* side on a hoare goal *)
abort.

lemma hoare_fusion_errors : hoare [M.h : true ==> true].
proof.
proc.
fail fusion 2 @ 1, 1.      (* not a loop *)
fail fusion 10 @ 1, 1.     (* invalid code position *)
fail fusion 3!3 @ 1, 1.    (* 1st loop not headed by 3 instructions *)
fail fusion 7!3 @ 1, 1.    (* 1st loop not followed by 3 instructions *)
fail fusion 5!2 @ 1, 1.    (* no 2nd loop *)
fail fusion 3 @ 5, 1.      (* 1st body too short *)
fail fusion 3 @ 1, 5.      (* 2nd body too short *)
fail fusion 3 @ 1, 1.      (* epilogs do not match *)
fail fusion 5 @ 2, 2.      (* epilogs do not match *)
fail fusion 5 @ 3, 2.      (* conditions do not match *)
fail fusion 3 @ 2, 1.      (* independence: c1 reads y, written by c2 *)
fail fusion 3 @ 3, 2.      (* independence *)
fail fusion {2} 3 @ 1, 1.  (* side on a hoare goal *)
abort.

lemma hoare_fusion_errors2 : hoare [M.k : true ==> true].
proof.
proc.
fail fusion 2 @ 1, 1.      (* preludes do not match *)
fail fusion 2!2 @ 1, 1.    (* not headed by 2 instructions *)
abort.

lemma ehoare_errors : ehoare [M.h : 1%xr ==> 1%xr].
proof.
proc.
fail fission 3 @ 2, 1.     (* second offset lower than the first *)
fail fusion 2 @ 1, 1.      (* not a loop *)
fail unroll 1.             (* not a loop *)
fail splitwhile 10 : true. (* invalid code position *)
abort.

lemma phoare_errors : phoare [M.h : true ==> true] = 1%r.
proof.
proc.
fail fission 3 @ 1, 5.     (* invalid offsets range *)
fail fusion 5 @ 1, 1.      (* epilogs do not match *)
fail fusion 3 @ 2, 1.      (* independence *)
fail unroll 9.             (* invalid code position *)
fail splitwhile 1 : true.  (* not a loop *)
fail unroll {1} 3.         (* side on a phoare goal *)
abort.

lemma loop_errors : hoare [M.g : true ==> true].
proof.
proc.
fail unroll 1.             (* not a loop *)
fail unroll 6.             (* invalid code position *)
fail unroll 5.             (* after the last instruction *)
fail unroll 1.1.           (* not a loop, nested *)
fail unroll 1.4.           (* invalid code position, nested *)
fail unroll 2#None.1.      (* invalid code position, empty branch *)
fail unroll 3.1.           (* no such branch *)
fail splitwhile 1 : true.  (* not a loop *)
fail splitwhile 5 : true.  (* invalid code position *)
fail splitwhile 1.2 : 1.   (* not a boolean *)
fail fission 1.1 @ 1, 2.   (* not a loop, nested *)
fail fission 1.3 @ 1, 2.   (* after the last instruction, nested *)
fail fission 5 @ 1, 2.     (* after the last instruction *)
fail fusion 4.2 @ 1, 1.    (* no 2nd loop *)
abort.

lemma equiv_errors : equiv [M.h ~ M.h : true ==> true].
proof.
proc.
fail unroll 3.             (* no side on an equiv goal *)
fail fission 3 @ 1, 2.     (* no side on an equiv goal *)
fail fission{1} 3 @ 2, 1.  (* second offset lower than the first *)
fail fission{2} 3 @ 2, 2.  (* epilog samples *)
fail fusion{1} 3 @ 1, 1.   (* epilogs do not match *)
fail fusion{2} 5 @ 3, 2.   (* conditions do not match *)
fail fusion{2} 10 @ 1, 1.  (* invalid code position *)
fail unroll{1} 1.          (* not a loop *)
fail unroll{2} 10.         (* invalid code position *)
fail splitwhile{1} 2 : true. (* not a loop *)
fail splitwhile{2} 10 : true. (* invalid code position *)
abort.
