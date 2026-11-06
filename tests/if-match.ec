require import AllCore Xreal.

(* -------------------------------------------------------------------- *)
type t = [A | B of int | C of int & bool].

exception oops of int.

module M = {
  (* conditional, then a continuation *)
  proc f(b : bool) : int = {
    var x;
    if (b) { x <- 1; } else { x <- 2; }
    x <- x + 1;
    return x;
  }

  (* conditional alone (empty continuation) *)
  proc f0(b : bool) : int = {
    var x;
    if (b) { x <- 1; } else { x <- 2; }
    return x;
  }

  (* conditional after a prefix, for the [seq]-ing forms *)
  proc f1(b : bool) : int = {
    var x;
    x <- 0;
    if (b) { x <- x + 1; } else { x <- x + 2; }
    x <- x + 1;
    return x;
  }

  (* conditional raising an exception, then a continuation *)
  proc fe(a : int) : int = {
    var x;
    x <- a;
    if (x < 0) { raise (oops x); }
    x <- x + 1;
    return x;
  }

  (* match, then a continuation *)
  proc g(o : t) : int = {
    var x;
    match o with
    | A => { x <- 1; }
    | B y => { x <- y; }
    | C y z => { x <- if z then y else 0; }
    end;
    x <- x + 1;
    return x;
  }

  (* match alone (empty continuation), on another datatype *)
  proc h(o : int option) : int = {
    var x;
    match o with
    | None => { x <- 1; }
    | Some y => { x <- y; }
    end;
    return x;
  }

  (* pattern variables named like program variables, read and written by
     the continuation; wildcards *)
  proc g2(o : t) : int = {
    var x, y;
    y <- 0;
    match o with
    | A => { x <- 1; }
    | B y => { x <- y; }
    | C _ z => { x <- if z then 1 else 0; }
    end;
    x <- x + y;
    y <- x;
    return x + y;
  }

  (* match on another instance of the same datatype *)
  proc k(o : bool option) : int = {
    var x;
    match o with
    | None => { x <- 1; }
    | Some y => { x <- 1; }
    end;
    return x;
  }

  (* nested matches, the inner one followed by a continuation *)
  proc n(o : int option, o' : int option) : int = {
    var x;
    x <- 0;
    match o with
    | None => { x <- 1; }
    | Some y => {
        match o' with
        | None => { x <- y; }
        | Some y' => { x <- y + y'; }
        end;
        x <- x + y;
      }
    end;
    x <- x + 1;
    return x;
  }
}.

(* a [match] duplicated by inlining (same binders in both copies) *)
module N = {
  proc h1(o : int option) : int = {
    var r;
    r <- 0;
    match o with
    | None => { r <- 1; }
    | Some y => { r <- y; }
    end;
    return r;
  }

  proc h2(o : int option) : int = {
    var a, b;
    a <@ h1(o);
    b <@ h1(o);
    return a + b;
  }
}.

(* ==================================================================== *)
(* if                                                                   *)

lemma hoare_if : hoare [M.f : true ==> 1 < res].
proof.
proc; if.
+ by wp; skip.
+ by wp; skip.
qed.

lemma hoare_if_alone : hoare [M.f0 : b ==> res = 1].
proof.
proc; if.
+ by wp; skip.
+ by wp; skip; smt().
qed.

lemma hoare_if_prefix : hoare [M.f1 : b ==> res = 2].
proof.
proc; sp 1; if.
+ by wp; skip.
+ by wp; skip; smt().
qed.

(* exceptional postconditions are kept in both branches *)
lemma hoare_if_raise (a0 : int) :
  hoare [M.fe : a = a0 ==> res = a0 + 1 | oops x => x < 0 /\ x = a0].
proof.
proc; sp; if.
+ by wp; skip => /> /#.
+ by wp; skip => /> /#.
qed.

(* the side is ignored on a [hoare] goal *)
lemma hoare_if_side : hoare [M.f : true ==> 1 < res].
proof.
proc; if{2}.
+ by wp; skip.
+ by wp; skip.
qed.

lemma ehoare_if : ehoare [M.f : (1%xr) ==> (1%xr)].
proof.
proc; if.
+ by wp; skip => &hr; case: (b{hr}).
+ by wp; skip => &hr; case: (b{hr}).
qed.

lemma ehoare_if_alone : ehoare [M.f0 : (1%xr) ==> (1%xr)].
proof.
proc; if.
+ by wp; skip => &hr; case: (b{hr}).
+ by wp; skip => &hr; case: (b{hr}).
qed.

lemma phoare_if_eq : phoare [M.f : true ==> 1 < res] = 1%r.
proof.
proc; if.
+ by wp; skip.
+ by wp; skip.
qed.

lemma phoare_if_alone : phoare [M.f0 : true ==> 0 < res] = 1%r.
proof.
proc; if.
+ by wp; skip.
+ by wp; skip.
qed.

lemma phoare_if_le : phoare [M.f : true ==> res = 0] <= 0%r.
proof.
proc; if.
+ by hoare; wp; skip.
+ by hoare; wp; skip.
qed.

lemma phoare_if_ge : phoare [M.f : true ==> 1 < res] >= (1%r/2%r).
proof.
proc; if.
+ by wp; skip => /> /#.
+ by wp; skip => /> /#.
qed.

lemma equiv_if : equiv [M.f ~ M.f : ={b} ==> ={res}].
proof.
proc; if.
+ by move=> &1 &2 ->.
+ by wp; skip.
+ by wp; skip.
qed.

(* two-sided, a continuation on the left only *)
lemma equiv_if_alone_right : equiv [M.f ~ M.f0 : ={b} ==> res{1} = res{2} + 1].
proof.
proc; if.
+ by move=> &1 &2 ->.
+ by wp; skip.
+ by wp; skip.
qed.

(* two-sided, a continuation on the right only *)
lemma equiv_if_alone_left : equiv [M.f0 ~ M.f : ={b} ==> res{1} + 1 = res{2}].
proof.
proc; if.
+ by move=> &1 &2 ->.
+ by wp; skip.
+ by wp; skip.
qed.

lemma equiv_if_alone_both : equiv [M.f0 ~ M.f0 : ={b} ==> ={res}].
proof.
proc; if.
+ by move=> &1 &2 ->.
+ by wp; skip.
+ by wp; skip.
qed.

lemma equiv_if_left : equiv [M.f ~ M.f0 : ={b} ==> 1 < res{1}].
proof.
proc; if{1}.
+ by wp; skip.
+ by wp; skip.
qed.

lemma equiv_if_right : equiv [M.f0 ~ M.f : ={b} ==> 1 < res{2}].
proof.
proc; if{2}.
+ by wp; skip.
+ by wp; skip.
qed.

lemma equiv_if_left_alone : equiv [M.f0 ~ M.f : ={b} ==> 0 < res{1}].
proof.
proc; if{1}.
+ by wp; skip.
+ by wp; skip.
qed.

(* [if] after [seq], at the last conditional *)
lemma equiv_if_seq : equiv [M.f1 ~ M.f1 : ={b} ==> ={res}].
proof.
proc; if _ _ : (={b, x}).
+ by wp; skip.
+ by move=> &1 &2 [->].
+ by wp; skip.
+ by wp; skip.
qed.

lemma equiv_if_seq_eq : equiv [M.f1 ~ M.f1 : ={b} ==> ={res}].
proof.
proc; if := (={b, x}).
+ by wp; skip.
+ by move=> &1 &2 [->].
+ by wp; skip.
+ by wp; skip.
qed.

(* explicit positions: typed on the given side *)
lemma equiv_if_seq_pos : equiv [M.f1 ~ M.f1 : ={b} ==> ={res}].
proof.
proc.
fail if 2 2 : (={b, x}).
if{1} 2 2 : (={b, x}).
+ by wp; skip.
+ by wp; skip.
+ by wp; skip.
abort.

lemma equiv_if_seq_left : equiv [M.f1 ~ M.f1 : ={b} ==> true].
proof.
proc; if{2} _ _ : (={b}).
+ by wp; skip.
+ by wp; skip.
+ by wp; skip.
qed.

lemma equiv_if_seqone : equiv [M.f1 ~ M.f1 : ={b} ==> true].
proof.
proc; if{1} : (_ : true ==> true).
+ by wp; skip.
+ by wp; skip.
+ by wp; skip.
qed.

lemma equiv_if_seqone_right : equiv [M.f1 ~ M.f1 : ={b} ==> true].
proof.
proc; if{2} 2 : (_ : true ==> true).
+ by wp; skip.
+ by wp; skip.
+ by wp; skip.
qed.

lemma if_errors : equiv [M.f1 ~ M.f : ={b} ==> true].
proof.
proc.
fail if.
fail if{1}.
if{2}.
fail if _ _ : true.
abort.

lemma if_errors_right : equiv [M.f ~ M.f1 : ={b} ==> true].
proof.
proc.
fail if.
fail if{2}.
abort.

lemma if_errors_hoare : hoare [M.f1 : true ==> true].
proof.
proc.
fail if.
fail if _ _ : true.
fail if{1} : (_ : true ==> true).
abort.

lemma if_errors_ehoare : ehoare [M.f1 : (1%xr) ==> (1%xr)].
proof.
proc.
fail if.
fail if := true.
abort.

lemma if_errors_phoare : phoare [M.f1 : true ==> true] = 1%r.
proof.
proc.
fail if.
fail if{1} : (_ : true ==> true).
abort.

lemma if_errors_ambient : true.
proof.
fail if.
fail if := true.
abort.

lemma if_errors_pred : hoare [M.f : true ==> true].
proof.
fail if.
abort.

(* ==================================================================== *)
(* match                                                                *)

lemma hoare_match : hoare [M.g : o = A ==> res = 2].
proof.
proc; match.
+ by wp; skip.
+ by wp; skip => /> /#.
+ by wp; skip => /> /#.
qed.

lemma hoare_match_alone : hoare [M.h : o = None ==> res = 1].
proof.
proc; match.
+ by wp; skip.
+ by wp; skip => /> /#.
qed.

lemma hoare_match_clash : hoare [M.g2 : o = A ==> res = 2].
proof.
proc; sp 1; match.
+ by wp; skip.
+ by wp; skip => /> /#.
+ by wp; skip => /> /#.
qed.

lemma hoare_match_nested : hoare [M.n : o = None ==> res = 2].
proof.
proc; sp 1; match.
+ by wp; skip.
+ match.
  + by wp; skip => /> /#.
  + by wp; skip => /> /#.
qed.

(* the side or [=] is ignored on a [hoare] goal *)
lemma hoare_match_side : hoare [M.g : o = A ==> res = 2].
proof.
proc; match{2}.
+ by wp; skip.
+ by wp; skip => /> /#.
+ by wp; skip => /> /#.
qed.

lemma hoare_match_eq : hoare [M.g : o = A ==> res = 2].
proof.
proc; match =.
+ by wp; skip.
+ by wp; skip => /> /#.
+ by wp; skip => /> /#.
qed.

lemma phoare_match_eq : phoare [M.g : true ==> true] = 1%r.
proof.
proc; match.
+ by wp; skip.
+ by wp; skip.
+ by wp; skip.
qed.

lemma phoare_match_alone : phoare [M.h : true ==> true] = 1%r.
proof.
proc; match.
+ by wp; skip.
+ by wp; skip.
qed.

lemma phoare_match_le : phoare [M.g : o = A ==> res = 0] <= 0%r.
proof.
proc; match.
+ by hoare; wp; skip.
+ by hoare; wp; skip => /> /#.
+ by hoare; wp; skip => /> /#.
qed.

lemma phoare_match_ge : phoare [M.g : o = A ==> res = 2] >= 1%r.
proof.
proc; match.
+ by wp; skip.
+ by wp; skip => /> /#.
+ by wp; skip => /> /#.
qed.

lemma phoare_match_clash : phoare [M.g2 : o = A ==> res = 2] = 1%r.
proof.
proc; sp 1; match.
+ by wp; skip.
+ by wp; skip => /> /#.
+ by wp; skip => /> /#.
qed.

lemma equiv_match_sided : equiv [M.g ~ M.g : ={o} ==> ={res}].
proof.
proc; match{1}.
+ match{2}.
  + by wp; skip.
  + by wp; skip => /> /#.
  + by wp; skip => /> /#.
+ match{2}.
  + by wp; skip => /> /#.
  + by wp; skip => /> /#.
  + by wp; skip => /> /#.
+ match{2}.
  + by wp; skip => /> /#.
  + by wp; skip => /> /#.
  + by wp; skip => /> /#.
qed.

lemma equiv_match_sided_alone : equiv [M.h ~ M.g : o{1} = None /\ o{2} = A ==> res{1} + 1 = res{2}].
proof.
proc; match{1}.
+ match{2}.
  + by wp; skip.
  + by wp; skip => /> /#.
  + by wp; skip => /> /#.
+ by exfalso => /> /#.
qed.

lemma equiv_match_sided_right : equiv [M.g2 ~ M.g2 : ={o} ==> ={res}].
proof.
proc; sp 1 1; match{2}.
+ by match{1}; [wp; skip | wp; skip => /> /# | wp; skip => /> /#].
+ by match{1}; [wp; skip => /> /# | wp; skip => /> /# | wp; skip => /> /#].
+ by match{1}; [wp; skip => /> /# | wp; skip => /> /# | wp; skip => /> /#].
qed.

lemma equiv_match_synced : equiv [M.g ~ M.g : ={o} ==> ={res}].
proof.
proc; match.
+ smt().
+ smt().
+ smt().
+ by wp; skip.
+ by move=> y1 y2; wp; skip => /> /#.
+ by move=> y1 z1 y2 z2; wp; skip => /> /#.
qed.

lemma equiv_match_eq : equiv [M.g ~ M.g : ={o} ==> ={res}].
proof.
proc; match =.
+ done.
+ by wp; skip.
+ by move=> y; wp; skip.
+ by move=> y z; wp; skip.
qed.

lemma equiv_match_eq_clash : equiv [M.g2 ~ M.g2 : ={o} ==> ={res}].
proof.
proc; sp 1 1; match =.
+ done.
+ by wp; skip.
+ by move=> y; wp; skip.
+ by move=> y z; wp; skip.
qed.

(* two-sided, a continuation on one side only *)
lemma equiv_match_synced_inst : equiv [M.h ~ M.k : o{1} = None <=> o{2} = None ==> res{1} = 1 => res{2} = 1].
proof.
proc; match.
+ by move=> &1 &2 /#.
+ by move=> &1 &2 /#.
+ by wp; skip.
+ by move=> y1 y2; wp; skip.
qed.

lemma equiv_match_eq_alone : equiv [M.h ~ M.h : ={o} ==> ={res}].
proof.
proc; match =.
+ done.
+ by wp; skip.
+ by move=> y; wp; skip.
qed.

lemma equiv_match_nested : equiv [M.n ~ M.n : ={o, o'} ==> ={res}].
proof.
proc; sp 1 1; match =.
+ done.
+ by wp; skip.
+ move=> y; match =.
  + done.
  + by wp; skip.
  + by move=> y'; wp; skip.
qed.

(* a free logical variable named like the pattern variables, in the
   continuation of a match *)
lemma equiv_match_dup : equiv [N.h2 ~ N.h2 : ={o} ==> ={res}].
proof.
proc; inline *; sp.
match =.
+ done.
+ admit.
move=> y.
swap{1} [3..5] -2.
sp 2 0.
match{1}.
+ admit.
admit.
abort.

lemma match_errors : equiv [M.g ~ M.h : true ==> true].
proof.
proc.
fail match.
fail match =.
abort.

lemma match_errors_inst : equiv [M.h ~ M.k : true ==> true].
proof.
proc.
fail match =.
abort.

lemma match_errors_nomatch : equiv [M.f ~ M.g : true ==> true].
proof.
proc.
fail match.
fail match =.
fail match{1}.
match{2}.
abort.

lemma match_errors_nomatch_right : equiv [M.g ~ M.f : true ==> true].
proof.
proc.
fail match.
fail match{2}.
abort.

lemma match_errors_hoare : hoare [M.f : true ==> true].
proof.
proc.
fail match.
abort.

lemma match_errors_phoare : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
fail match.
abort.

lemma match_errors_ehoare : ehoare [M.g : (1%xr) ==> (1%xr)].
proof.
proc.
fail match.
abort.

lemma match_errors_ambient : true.
proof.
fail match.
abort.

(* ==================================================================== *)
(* case                                                                 *)

lemma hoare_case : hoare [M.f : true ==> 1 < res].
proof.
proc; case (b).
+ by rcondt 1 => //; wp; skip.
+ by rcondf 1 => //; wp; skip.
qed.

lemma ehoare_case : ehoare [M.f : (1%xr) ==> (1%xr)].
proof.
proc; case (b).
+ by if; wp; skip => &hr; case: (b{hr}).
+ by if; wp; skip => &hr; case: (b{hr}).
qed.

lemma phoare_case : phoare [M.f : true ==> 1 < res] = 1%r.
proof.
proc; case (b).
+ by rcondt 1 => //; wp; skip.
+ by rcondf 1 => //; wp; skip.
qed.

lemma equiv_case : equiv [M.f ~ M.f : ={b} ==> ={res}].
proof.
proc; case (b{1}).
+ by rcondt{1} 1 => //; rcondt{2} 1; auto => /> /#.
+ by rcondf{1} 1 => //; rcondf{2} 1; auto => /> /#.
qed.

(* the case formula is simplified away when trivial *)
lemma hoare_case_true : hoare [M.f : true ==> true].
proof.
proc; case true.
+ by wp; skip.
+ by wp; skip.
qed.

lemma equiv_case_true : equiv [M.f ~ M.f : true ==> true].
proof.
proc; case true.
+ by wp; skip.
+ by wp; skip.
qed.
