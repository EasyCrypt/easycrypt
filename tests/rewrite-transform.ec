(* `proc rewrite`, `proc rewrite /=`, `proc change`, `proc change circuit`
   and `idassign` as program transformations: in every logic where they
   exist (hoare, ehoare, phoare, equiv on both sides; `proc change
   circuit` and `idassign` are hoare only), at top-level and nested
   positions (in the branches of an `if`, the body of a `while`, the arms
   of a `match`, with the arm locals in scope), with fresh locals, and
   their error paths. Each tactic is a separate sentence, so that the
   goals it leaves can be compared across builds. *)
require import AllCore List Distr Xreal QFABV.

op foo : int -> int.
axiom fooE (x : int) : foo x = x + 1.

hint simplify fooE.

type t = [A | B of int].

exception oops.

module M = {
  var g : int

  proc f(a : int, b : bool, o : t) : int = {
    var x, y, z : int;
    x <- a + 0;
    y <- foo x;
    if (b) {
      z <- y + 0;
    } else {
      z <- foo 0;
    }
    match o with
    | A => { x <- 0 + 2; }
    | B v => { x <- v + 0; z <- foo v; }
    end;
    while (x < 10) {
      x <- x + 0;
      y <- foo y;
    }
    return x + y + z;
  }

  proc e(a : int) : int = {
    var x : int;
    x <- a;
    if (x = 0) { raise oops; }
    return x;
  }
}.

(* ==================================================================== *)
(* proc rewrite                                                          *)

lemma hoare_rw : hoare [M.f : true ==> 0 <= res].
proof.
proc.
proc rewrite 1 addz0.
proc rewrite 3.1 addz0.
proc rewrite 4#B.1 addz0.
proc rewrite 4#A.1 addzC.
proc rewrite 5.:[1..2] addz0.
proc rewrite 5 ltzE.
admit.
qed.

lemma hoare_rw_simpl : hoare [M.f : true ==> 0 <= res].
proof.
proc.
proc rewrite [1..2] /=.
proc rewrite 4#B.:[1..2] /=.
proc rewrite /=.
proc rewrite /=.
admit.
qed.

lemma ehoare_rw : ehoare [M.f : 1%xr ==> 1%xr].
proof.
proc.
proc rewrite 1 addz0.
proc rewrite 3?1 /=.
proc rewrite 4#B.1 addz0.
proc rewrite /=.
admit.
qed.

lemma phoare_rw : phoare [M.f : true ==> 0 <= res] = 1%r.
proof.
proc.
proc rewrite 1 addz0.
proc rewrite 3.1 addz0.
proc rewrite 4#B.2 /=.
proc rewrite 5.1 addz0.
admit.
qed.

lemma equiv_rw : equiv [M.f ~ M.f : ={arg} ==> ={res}].
proof.
proc.
proc rewrite {1} 1 addz0.
proc rewrite {2} 3.1 addz0.
proc rewrite {1} 4#B.1 addz0.
proc rewrite {2} 4#B.:[1..2] /=.
proc rewrite {1} /=.
proc rewrite {2} 5.:[1..2] /=.
admit.
qed.

lemma rw_errors : hoare [M.f : true ==> 0 <= res].
proof.
proc.
fail proc rewrite 2 addz0.       (* no occurrence *)
fail proc rewrite 12 addz0.      (* invalid code position *)
fail proc rewrite {1} 1 addz0.   (* side for a non-relational goal *)
fail proc rewrite 1 fooE.        (* no occurrence *)
fail proc rewrite 1 foo.         (* not a lemma *)
admit.
qed.

lemma rw_errors_equiv : equiv [M.f ~ M.f : ={arg} ==> ={res}].
proof.
proc.
fail proc rewrite 1 addz0.       (* no side for a relational goal *)
fail proc rewrite {1} 2 addz0.   (* no occurrence *)
admit.
qed.

lemma rw_errors_fun : hoare [M.f : true ==> 0 <= res].
proof.
fail proc rewrite 1 addz0.       (* not a statement judgement *)
admit.
qed.

(* ==================================================================== *)
(* proc change                                                           *)

lemma hoare_change : hoare [M.f : 0 <= a ==> 0 <= res].
proof.
proc.
proc change 1 : { x <- a; }.
admit.
proc change 3.1 : { z <- y; }.
admit.
proc change 4#B.:[1..2] : [w : int] { w <- y; x <- w; z <- w + 1; }.
admit.
proc change 5.1 : { x <- x; }.
admit.
proc change <2 : { M.g <- 0; }.
admit.
proc change [6..6] : { while (x < 10) { x <- x + 0; y <- y + 1; } }.
admit.
admit.
qed.

lemma ehoare_change : ehoare [M.f : 1%xr ==> 1%xr].
proof.
proc.
proc change 1 : { x <- a; }.
admit.
proc change 3?1 : [w : int] { w <- 0; z <- w + 1; }.
admit.
proc change 5.2 : { y <- y + 1; }.
admit.
admit.
qed.

lemma phoare_change : phoare [M.f : 0 <= a ==> 0 <= res] = 1%r.
proof.
proc.
proc change 1 : { x <- a; }.
admit.
proc change 3.1 : [w : int] { w <- y; z <- w; }.
admit.
proc change 4#B.2 : { z <- x + 1; }.
admit.
proc change 5.:[1..2] : { y <- foo y; x <- x + 0; }.
admit.
admit.
qed.

lemma equiv_change : equiv [M.f ~ M.f : ={arg} /\ 0 <= a{1} /\ a{2} < 5 ==> ={res}].
proof.
proc.
proc change {1} 1 : { x <- a; }.
admit.
proc change {2} 1 : [w : int] { w <- a; x <- w; }.
admit.
proc change {1} 3.1 : { z <- y; }.
admit.
proc change {2} 5#B.:[1..2] : { x <- y; z <- y + 1; }.
admit.
proc change {1} 5.1 : { x <- x; }.
admit.
proc change {2} >(-1) : { y <- y; }.
admit.
admit.
qed.

(* ehoare: the frame is taken from the boolean part [P] of a
   precondition [P `|` f] (the reference build took the whole real-valued
   precondition as a conjunct of the precondition of the local
   equivalence, which was then ill-typed). *)
lemma ehoare_change_frame : ehoare [M.f : (0 <= a) `|` 1%xr ==> 1%xr].
proof.
proc.
proc change 1 : { x <- a; }.
admit.
proc change 2 : { y <- x + 1; }.
admit.
admit.
qed.

lemma change_errors : hoare [M.f : true ==> 0 <= res].
proof.
proc.
fail proc change 12 : { x <- a; }.           (* invalid code position *)
fail proc change {1} 1 : { x <- a; }.        (* side for a non-relational goal *)
fail proc change 1 : { x <- w; }.            (* unknown variable *)
admit.
qed.

lemma change_errors_equiv : equiv [M.f ~ M.f : ={arg} ==> ={res}].
proof.
proc.
fail proc change 1 : { x <- a; }.            (* no side *)
admit.
qed.

lemma change_errors_fun : hoare [M.f : true ==> 0 <= res].
proof.
fail proc change 1 : { x <- a; }.            (* not inlined *)
admit.
qed.

(* An exceptional postcondition reading a variable written by the
   fragment: the variable is observable. *)
lemma hoare_change_exn : hoare [M.e : true ==> true | oops => M.g = 0].
proof.
proc.
proc change 1 : { x <- a; M.g <- x; }.
admit.
admit.
qed.

(* ==================================================================== *)
(* proc change circuit / idassign (hoare only)                           *)

type W8.

op to_bits : W8 -> bool list.
op from_bits : bool list -> W8.
op of_int : int -> W8.
op to_uint : W8 -> int.
op to_sint : W8 -> int.

bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.
realize gt0_size by admit.
realize tolistP by admit.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.
realize size_tolist by admit.

op (+^) : W8 -> W8 -> W8.
bind op W8 (+^) "xor".
realize bvxorP by admit.

module C = {
  var gw : W8

  proc f (a : W8, b : W8, c0 : bool) = {
    var c, d : W8;
    c <- a +^ b;
    if (c0) {
      d <- b +^ a;
      c <- d +^ c;
    }
    return c;
  }

  proc g (a : W8, b : W8) = {
    var c : W8;
    c <- a +^ b;
    gw <- c;
    return c;
  }

  proc r (a : W8, b : W8) = {
    var c : W8;
    c <$ dunit a;
    return c;
  }
}.

lemma hoare_circuit (a_ b_ : W8) :
  hoare[C.f : a_ = a /\ b_ = b ==> true].
proof.
proc.
proc change circuit 1 + 1 { c <- b +^ a; }.
proc change circuit 2.1 + 2 { d <- a +^ b; c <- d +^ c; }.
proc change circuit [e : W8] 2.1 + 1 { e <- b; d <- a +^ e; }.
idassign 1 c.
idassign 3.2 d.
idassign 4 C.gw.
admit.
qed.

lemma circuit_errors (a_ b_ : W8) :
  hoare[C.f : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
proc.
fail proc change circuit 1 + 1 { c <- a; }.        (* not equivalent *)
fail proc change circuit 1 + 3 { c <- b +^ a; }.   (* too many instructions *)
fail proc change circuit 12 + 1 { c <- b +^ a; }.  (* invalid position *)
fail proc change circuit 1 + 1 { c <- e; }.        (* unknown variable *)
fail proc change circuit 1 + 1 { C.gw <- a; c <- b +^ a; }. (* global *)
fail proc change circuit [_ : W8] 1 + 1 { c <- b +^ a; }. (* no name *)
fail idassign 1 e.                                  (* unknown variable *)
fail idassign 12 c.                                 (* invalid position *)
admit.
qed.

lemma circuit_errors_global (a_ b_ : W8) :
  hoare[C.g : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
proc.
fail proc change circuit 1 + 2 { c <- b +^ a; C.gw <- c; }. (* checker error *)
admit.
qed.

lemma circuit_errors_rnd (a_ b_ : W8) :
  hoare[C.r : a_ = a /\ b_ = b ==> true].
proof.
proc.
fail proc change circuit 1 + 1 { c <- a; }.        (* checker error *)
admit.
qed.

lemma circuit_errors_exn (a_ b_ : W8) :
  hoare[C.f : a_ = a /\ b_ = b ==> true | oops => true].
proof.
proc.
fail proc change circuit 1 + 1 { c <- b +^ a; }.   (* exceptions *)
admit.
qed.

lemma circuit_errors_logic (a_ b_ : W8) :
  equiv[C.f ~ C.f : ={arg} ==> ={res}].
proof.
proc.
fail proc change circuit 1 + 1 { c <- b +^ a; }.   (* hoare only *)
fail idassign 1 c.                                  (* hoare only *)
admit.
qed.
