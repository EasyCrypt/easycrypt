require import AllCore Xreal.

(* rcondt / rcondf and match C k in every logic: the conditional (if,
   while) or the match decided at a position, the prefix establishing the
   branch taken. *)

exception e1.

module M = {
  var x : int
  var o : int option

  proc f(y : int) = {
    var z;
    z <- y;
    if (z = 0) { x <- 1; } else { x <- 2; }
    while (z < 1) { z <- z + 1; }
  }

  proc k(y : int) = {
    var z;
    z <- y;
    if (z = 0) { x <- 1; } else { x <- 2; }
  }

  proc r(y : int) = {
    var z;
    x <- 0;
    z <- y;
    if (z = 0) { raise e1; }
    x <- 1;
  }

  (* The prefix neither reads nor writes [o]: framed form of [match]
     (when the logic allows it). *)
  proc g() = {
    x <- 0;
    match o with
    | None => { x <- 1; }
    | Some v => { x <- v; }
    end;
  }

  (* The prefix writes [o]: unframed form of [match]. *)
  proc h() = {
    o <- Some 3;
    match o with
    | None => { x <- 1; }
    | Some v => { x <- v; }
    end;
  }

  (* Empty prefix: framed form of [match] in every logic. *)
  proc m() = {
    match o with
    | None => { x <- 1; }
    | Some v => { x <- v; }
    end;
  }
}.

(* -------------------------------------------------------------------- *)
(* rcondt / rcondf, on an [if] and on a [while].                        *)

lemma hoare_rcondt : hoare [M.f : y = 0 ==> M.x = 1].
proof.
proc.
rcondt 2; 1: by auto.
rcondt 3; 1: by auto.
rcondf 4; 1: by auto.
by auto.
qed.

lemma hoare_rcondf : hoare [M.f : y <> 0 ==> M.x = 2].
proof.
proc.
rcondf 2; 1: by auto.
by while (M.x = 2); auto.
qed.

(* The exceptional postcondition is kept in the prefix obligation. *)
lemma hoare_rcond_exn : hoare [M.r : y = 0 ==> false | e1 => M.x = 0].
proof.
proc.
rcondt 3; 1: by auto.
by auto.
qed.

lemma ehoare_rcondt : ehoare [M.k : (y = 0) `|` 1%xr ==> 1%xr].
proof.
proc.
rcondt 2; 1: by auto.
by wp; skip => &hr /#.
qed.

lemma ehoare_rcondf : ehoare [M.f : (0 < y) `|` 1%xr ==> 1%xr].
proof.
proc.
rcondf 2; 1: by auto => /#.
rcondf 3; 1: by wp; skip => /#.
by wp; skip => &hr /#.
qed.

lemma phoare_rcondt : phoare [M.f : y = 0 ==> M.x = 1] = 1%r.
proof.
proc.
rcondt 2; 1: by auto.
rcondt 3; 1: by auto.
rcondf 4; 1: by auto.
by auto.
qed.

lemma phoare_rcondf : phoare [M.k : y <> 0 ==> M.x = 2] >= 1%r.
proof.
proc.
rcondf 2; 1: by auto.
by auto.
qed.

lemma equiv_rcond : equiv [M.f ~ M.f : y{1} = 0 /\ y{2} = 0 ==> ={M.x}].
proof.
proc.
rcondt {1} 2; 1: by auto.
rcondt {2} 2; 1: by auto.
rcondt {1} 3; 1: by auto.
rcondf {1} 4; 1: by auto.
rcondt {2} 3; 1: by auto.
rcondf {2} 4; 1: by auto.
by auto.
qed.

lemma equiv_rcondf : equiv [M.k ~ M.k : y{1} <> 0 /\ y{2} <> 0 ==> ={M.x}].
proof.
proc.
rcondf {1} 2; 1: by move=> &2; auto.
rcondf {2} 2; 1: by move=> &1; auto.
by auto.
qed.

(* -------------------------------------------------------------------- *)
(* rcond: error paths.                                                  *)

lemma hoare_rcond_errors : hoare [M.f : y = 0 ==> M.x = 1].
proof.
proc.
fail rcondt 1.        (* not a conditional *)
fail rcondt 10.       (* no such position *)
fail rcondt {1} 2.    (* side on a hoare goal *)
abort.

lemma ehoare_rcond_errors : ehoare [M.k : 1%xr ==> 1%xr].
proof.
proc.
fail rcondt 2.        (* the pre is not of the form _ `|` _ *)
fail rcondt 1.        (* not a conditional *)
fail rcondf 10.       (* no such position *)
abort.

lemma phoare_rcond_errors : phoare [M.k : true ==> true] = 1%r.
proof.
proc.
fail rcondt 1.        (* not a conditional *)
fail rcondt {2} 2.    (* side on a phoare goal *)
abort.

lemma equiv_rcond_errors : equiv [M.f ~ M.f : true ==> true].
proof.
proc.
fail rcondt 2.        (* no side on an equiv goal *)
fail rcondt {1} 1.    (* not a conditional *)
fail rcondf {2} 10.   (* no such position *)
abort.

(* -------------------------------------------------------------------- *)
(* rmatch: framed and unframed forms.                                   *)

lemma hoare_rmatch_framed : hoare [M.g : M.o = Some 2 ==> M.x = 2].
proof.
proc.
match Some 2; 1: by auto => /#.
by auto => /#.
qed.

lemma hoare_rmatch_unframed : hoare [M.h : true ==> M.x = 3].
proof.
proc.
match Some 2; 1: by auto => /#.
by auto.
qed.

lemma hoare_rmatch_none : hoare [M.g : M.o = None ==> M.x = 1].
proof.
proc.
match None 2; 1: by auto.
by auto.
qed.

lemma ehoare_rmatch_framed :
  ehoare [M.g : (M.o = Some 2) `|` 1%xr ==> (M.x = 2)%xr].
proof.
proc.
match Some 2; 1: by auto => /#.
by wp; skip => &hr /#.
qed.

lemma ehoare_rmatch_unframed : ehoare [M.h : true `|` 1%xr ==> (M.x = 3)%xr].
proof.
proc.
match Some 2; 1: by auto => /#.
by wp; skip => &hr /#.
qed.

lemma phoare_le_rmatch_framed : phoare [M.g : M.o = Some 2 ==> M.x = 2] <= 1%r.
proof.
proc.
match Some 2; 1: by auto => /#.
by auto => /#.
qed.

(* phoare = with a non-empty prefix: unframed form. *)
lemma phoare_eq_rmatch_unframed : phoare [M.g : M.o = Some 2 ==> M.x = 2] = 1%r.
proof.
proc.
match Some 2; 1: by auto => /#.
by auto => /#.
qed.

lemma phoare_rmatch_unframed : phoare [M.h : true ==> M.x = 3] = 1%r.
proof.
proc.
match Some 2; 1: by auto => /#.
by auto.
qed.

lemma phoare_ge_rmatch_empty_framed : phoare [M.m : M.o = Some 2 ==> M.x = 2] >= 1%r.
proof.
proc.
match Some 1; 1: by auto => /#.
by auto => /#.
qed.

(* equiv with a non-empty prefix: unframed form, on both sides. *)
lemma equiv_rmatch : equiv [M.g ~ M.h : M.o{1} = Some 3 ==> ={M.x}].
proof.
proc.
match Some {1} 2; 1: by move=> &2; auto => /#.
match Some {2} 2; 1: by move=> &1; auto => /#.
by auto => /#.
qed.

lemma equiv_rmatch_sym : equiv [M.h ~ M.g : M.o{2} = Some 3 ==> ={M.x}].
proof.
proc.
match Some {2} 2; 1: by auto => /#.
match Some {1} 2; 1: by auto => /#.
by auto => /#.
qed.

(* equiv with an empty prefix: framed form, on both sides. *)
lemma equiv_rmatch_empty_framed :
  equiv [M.m ~ M.m : ={M.o} /\ M.o{1} = Some 3 ==> ={M.x}].
proof.
proc.
match Some {1} 1; 1: by move=> &2; auto => /#.
match Some {2} 1; 1: by move=> &1; auto => /#.
by auto => /#.
qed.

(* The plain [match] tactic goes through the framed rule (empty prefix). *)
lemma hoare_match : hoare [M.m : true ==> true].
proof.
proc.
match.
+ by auto.
+ by auto.
qed.

lemma equiv_match : equiv [M.m ~ M.m : ={M.o} ==> ={M.x}].
proof.
proc.
match {1}.
+ match {2}; 1: by auto.
  by exfalso => /#.
+ match {2}; 2: by auto.
  by exfalso => /#.
qed.

(* -------------------------------------------------------------------- *)
(* rmatch: error paths.                                                 *)

lemma hoare_rmatch_errors : hoare [M.g : true ==> true].
proof.
proc.
fail match Some 1.     (* not a match *)
fail match Foo 2.      (* no such constructor *)
fail match Some 10.    (* no such position *)
fail match Some {1} 2. (* side on a hoare goal *)
abort.

lemma ehoare_rmatch_errors : ehoare [M.g : 1%xr ==> 1%xr].
proof.
proc.
fail match Some 2.     (* the pre is not of the form _ `|` _ (framed) *)
fail match Some 1.     (* not a match *)
fail match Foo 2.      (* no such constructor *)
abort.

lemma ehoare_rmatch_errors_unframed : ehoare [M.h : 1%xr ==> 1%xr].
proof.
proc.
fail match Some 2.     (* the pre is not of the form _ `|` _ (unframed) *)
abort.

lemma phoare_rmatch_errors : phoare [M.g : true ==> true] <= 1%r.
proof.
proc.
fail match Some 1.     (* not a match *)
fail match Foo 2.      (* no such constructor *)
fail match Some 10.    (* no such position *)
abort.

lemma equiv_rmatch_errors : equiv [M.g ~ M.h : true ==> true].
proof.
proc.
fail match Some 2.     (* no side on an equiv goal *)
fail match Some {1} 1. (* not a match *)
fail match Foo {2} 2.  (* no such constructor *)
fail match Some {2} 9. (* no such position *)
abort.
