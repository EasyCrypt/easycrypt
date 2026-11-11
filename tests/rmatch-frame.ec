require import AllCore.

(* `match C k` after a prefix that may not terminate: the framed form
   (adding `e = C ys` to the precondition) is only used where it is
   sound, i.e. for hoare and phoare-<= judgements. *)

module N = {
  var o : int option
  var b : bool

  proc f() = {
    while (b) {}
    match o with
    | None   => {}
    | Some v => {}
    end;
  }

  proc g() = {}

  proc h() : int = {
    var r;
    r <- 0;
    match o with
    | None   => {}
    | Some v => { r <- v; }
    end;
    return r;
  }

  proc k() : int = {
    var r;
    match o with
    | None   => { r <- 0; }
    | Some v => { r <- v; }
    end;
    return r;
  }
}.

(* equiv: the unframed form is used, so the precondition no longer
   contains `N.o = Some _` and `false` cannot be derived from it. *)
lemma equiv_unframed : equiv [N.f ~ N.g : N.o{1} = None /\ N.b{1} ==> true].
proof.
proc.
match Some {1} 2.
+ by move=> &2; while (N.o = None /\ N.b); skip => /#.
fail by exfalso => &1 &2 /#.
abort.

(* hoare: the framed form is still used. *)
lemma hoare_framed : hoare [N.h : N.o = Some 1 ==> res = 1].
proof.
proc.
match Some 2.
+ by auto => /#.
by auto => /#.
qed.

(* phoare <=: the framed form is still used. *)
lemma phoare_le_framed : phoare [N.h : N.o = Some 1 ==> res = 1] <= 1%r.
proof.
proc.
match Some 2.
+ by auto => /#.
by auto => /#.
qed.

(* phoare =: the unframed form, still usable. *)
lemma phoare_eq_unframed : phoare [N.h : N.o = Some 1 ==> res = 1] = 1%r.
proof.
proc.
match Some 2.
+ by auto => /#.
by auto => /#.
qed.

(* Non-empty prefix in equiv: the unframed form, still usable. *)
lemma equiv_prefix_unframed :
  equiv [N.h ~ N.h : ={N.o} /\ N.o{1} = Some 1 ==> ={res}].
proof.
proc.
match Some {1} 2.
+ by move=> &2; auto => /#.
match Some {2} 2.
+ by move=> &1; auto => /#.
by auto => /#.
qed.

(* Empty prefix: the framed form is always sound and still used, in every
   logic; the precondition then carries `N.o = Some _`. *)
lemma equiv_empty_prefix_framed :
  equiv [N.k ~ N.k : ={N.o} /\ N.o{1} = Some 1 ==> res{1} = 1 /\ ={res}].
proof.
proc.
match Some {1} 1.
+ by move=> &2; auto => /#.
match Some {2} 1.
+ by move=> &1; auto => /#.
by auto => /#.
qed.

lemma phoare_eq_empty_prefix_framed :
  phoare [N.k : N.o = Some 1 ==> res = 1] = 1%r.
proof.
proc.
match Some 1.
+ by auto => /#.
by auto => /#.
qed.
