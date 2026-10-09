(* The [proc] rules in every logic: a concrete procedure by its body, an
   abstract procedure with an invariant (and up to a bad event), and
   [proc*]. *)
require import AllCore Xreal.

module type O = {
  proc o(x : int) : int
}.

module type Adv (O : O) = {
  proc run(x : int) : int
}.

module C = {
  var c : int

  proc f(x : int, y : int) : int = {
    var z;
    z <- x + y;
    return z;
  }

  proc g() : unit = {
    c <- c + 1;
  }
}.

module O1 : O = {
  var bad : bool
  var s   : int

  proc o(x : int) : int = {
    if (x = 10) {
      bad <- true;
    }
    s <- s + x;
    return x;
  }
}.

module O2 : O = {
  import var O1

  proc o(x : int) : int = {
    if (x = 10) {
      bad <- true;
      x <- 0;
    }
    s <- s + x;
    return x;
  }
}.

(* -------------------------------------------------------------------- *)
(* Concrete procedures, by their bodies. *)

lemma hoare_def : hoare [C.f : x = 1 /\ y = 2 ==> res = 3].
proof. proc; wp; skip => /> /#. qed.

lemma ehoare_def : ehoare [C.f : (x + y = 3)%xr ==> (res = 3)%xr].
proof. proc; wp; skip => /> &hr /#. qed.

lemma phoare_def_eq : phoare [C.f : x = 1 /\ y = 2 ==> res = 3] = 1%r.
proof. proc; wp; skip => /> /#. qed.

(* The bound is read in the initial memory: it may mention the arguments. *)
lemma phoare_def_ge :
  phoare [C.f : x = 1 /\ y = 2 ==> res = 3] >= (if y = 2 then 1%r else 1%r/2%r).
proof. proc; wp; skip => //; smt(). qed.

lemma equiv_def : equiv [C.f ~ C.f : ={x, y} ==> ={res}].
proof. proc; wp; skip => />. qed.

lemma equiv_def_unit : equiv [C.g ~ C.g : ={C.c} ==> ={C.c}].
proof. proc; wp; skip => />. qed.

(* Through the [call] tactic (with an invariant, concrete callee). *)
module D = {
  proc h() : unit = { C.g(); }
}.

lemma equiv_call_def : equiv [D.h ~ D.h : ={C.c} ==> ={C.c}].
proof. by proc; call (: ={C.c}); auto. qed.

section.
declare module A <: Adv {-O1}.

(* -------------------------------------------------------------------- *)
(* Abstract procedures, with an invariant. *)

lemma hoare_abs : hoare [A(O1).run : O1.bad ==> O1.bad].
proof.
proc (O1.bad); expect 3; 1,2: by trivial.
by proc; auto.
qed.

lemma hoare_abs_true : hoare [A(O1).run : true ==> true].
proof. by proc (true); expect 3; trivial. qed.

lemma ehoare_abs : ehoare [A(O1).run : (1%xr) ==> (1%xr)].
proof.
proc (1%xr); expect 3; 1,2: by trivial.
by proc; auto.
qed.

lemma phoare_abs_ge :
  (forall (O <: O{-A}), islossless O.o => islossless A(O).run) =>
  phoare [A(O1).run : true ==> true] >= 1%r.
proof.
move=> A_ll; proc (true); expect 4; 1..3: by trivial.
by proc; auto.
qed.

lemma phoare_abs_eq :
  (forall (O <: O{-A}), islossless O.o => islossless A(O).run) =>
  phoare [A(O1).run : true ==> true] = 1%r.
proof.
move=> A_ll; proc (true); expect 4; 1..3: by trivial.
by proc; auto.
qed.

lemma equiv_abs : equiv [A(O1).run ~ A(O1).run :
  ={x, glob A, O1.s, O1.bad} ==> ={res, glob A, O1.s, O1.bad}].
proof.
proc (={O1.s, O1.bad}) => //.
by proc; auto.
qed.

(* Through the [call] tactic (with an invariant, abstract callee). *)
module B (A : Adv) = {
  proc main() : int = {
    var r;
    r <@ A(O1).run(0);
    return r;
  }
}.

lemma equiv_call_abs : equiv [B(A).main ~ B(A).main :
  ={glob A, O1.s, O1.bad} ==> ={res, O1.s}].
proof.
proc; call (: ={O1.s, O1.bad}); last by auto.
by proc; auto.
qed.

(* -------------------------------------------------------------------- *)
(* Abstract procedures, up to a bad event. *)

lemma equiv_upto :
  (forall (O <: O{-A}), islossless O.o => islossless A(O).run) =>
  equiv [A(O1).run ~ A(O2).run :
     ={x, glob A, O1.s, O1.bad} /\ !O1.bad{2}
     ==> !O1.bad{2} => ={res, glob A, O1.s}].
proof.
move=> A_ll.
proc O1.bad (={O1.s}) (true) => //; expect 3.
- by proc; auto => /#.
- by move=> &2 _; proc; auto.
- by move=> &1; proc; auto.
qed.

lemma equiv_upto_ll :
  islossless A(O1).run => islossless A(O2).run =>
  equiv [A(O1).run ~ A(O2).run :
     ={x, glob A, O1.s, O1.bad} /\ !O1.bad{2}
     ==> !O1.bad{2} => ={res, glob A, O1.s}].
proof.
move=> ll1 ll2.
proc @[ll] O1.bad (={O1.s}) (true); expect 7.
- by move=> />.
- by move=> />.
- by apply ll1.
- by apply ll2.
- by proc; auto => /#.
- by move=> &2 _; proc; auto.
- by move=> &1; proc; auto.
qed.

(* -------------------------------------------------------------------- *)
(* Errors. *)

lemma abs_no_inv : hoare [A(O1).run : true ==> true].
proof. fail proc. abort.

lemma abs_dep_glob : hoare [A(O1).run : true ==> true].
proof. fail proc (glob A = glob A). abort.

lemma phoare_abs_le : phoare [A(O1).run : true ==> true] <= 1%r.
proof. fail proc (true). abort.

lemma phoare_abs_half : phoare [A(O1).run : true ==> true] >= (1%r/2%r).
proof. fail proc (true). abort.

end section.

lemma def_with_inv : hoare [C.f : true ==> true].
proof. fail proc (true). abort.

lemma def_upto : equiv [C.f ~ C.f : true ==> true].
proof. fail proc O1.bad (true) (true). abort.

(* -------------------------------------------------------------------- *)
(* [proc*]: procedures as single calls. *)

lemma hoare_code : hoare [C.f : x = 1 /\ y = 2 ==> res = 3].
proof.
proc*; inline *; wp; skip => /> /#.
qed.

lemma ehoare_code : ehoare [C.f : (x + y = 3)%xr ==> (res = 3)%xr].
proof.
proc*; inline *; wp; skip => /> &hr /#.
qed.

lemma phoare_code : phoare [C.f : x = 1 /\ y = 2 ==> res = 3] = 1%r.
proof.
proc*; inline *; wp; skip => /> /#.
qed.

lemma equiv_code : equiv [C.f ~ C.f : ={x, y} ==> ={res}].
proof.
proc*; inline *; wp; skip => />.
qed.

lemma eager_code :
  eager [C.g();, C.f ~ C.f, C.g(); : ={arg, C.c} ==> ={res, C.c}].
proof.
proc*; inline *; wp; skip => />.
qed.

lemma code_unit : equiv [C.g ~ C.g : ={C.c} ==> ={C.c}].
proof.
proc*; inline *; wp; skip => />.
qed.

lemma code_error : forall (x : int), x = x.
proof. fail proc*. abort.
