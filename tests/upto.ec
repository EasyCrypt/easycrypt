(* The upto rule (t_equiv_upto) and the derived forms of [byupto]. *)
require import AllCore Distr DBool StdOrder.
import RealOrder.

(* -------------------------------------------------------------------- *)
module type OT = {
  proc o(x : int) : int
}.

module type Adv (O : OT) = {
  proc main() : int
}.

module G1 = {
  var bad : bool
  var c   : int

  proc o(x : int) : int = {
    var r;
    r <- x;
    if (x = 0) {
      bad <- true;
      r <- 1;
    }
    return r;
  }

  proc main() : int = {
    var x, b;
    c <- 0;
    bad <- false;
    x <- 0;
    while (c < 10) {
      b <$ {0,1};
      match Some b with
      | None => { }
      | Some b' => { if (b') { x <@ o(c); } }
      end;
      c <- c + 1;
    }
    return x;
  }

  proc noinit(y : int) : int = {
    var x;
    x <@ o(y);
    return x;
  }
}.

module G2 = {
  import var G1

  proc o(x : int) : int = {
    var r;
    r <- x;
    if (x = 0) {
      bad <- true;
      r <- 2;
      bad <- true;
    }
    return r;
  }

  proc main() : int = {
    var x, b;
    c <- 0;
    bad <- false;
    x <- 0;
    while (c < 10) {
      b <$ {0,1};
      match Some b with
      | None => { }
      | Some b' => { if (b') { x <@ o(c); } }
      end;
      c <- c + 1;
    }
    return x;
  }

  proc noinit(y : int) : int = {
    var x;
    x <@ o(y);
    return x;
  }
}.

(* -------------------------------------------------------------------- *)
(* The rule itself: events [E /\ !bad] and [!bad]. *)
lemma L_rule &m :
  Pr[G1.main() @ &m : res = 0 /\ !G1.bad] = Pr[G2.main() @ &m : res = 0 /\ !G1.bad].
proof. byupto. qed.

lemma L_rule_nbad &m :
  Pr[G1.main() @ &m : !G1.bad] = Pr[G2.main() @ &m : !G1.bad].
proof. byupto. qed.

(* No [bad <- false] prefix; convertible arguments. *)
lemma L_rule_noinit &m :
  Pr[G1.noinit(1 + 1) @ &m : res = 2 /\ !G1.bad] = Pr[G2.noinit(2) @ &m : res = 2 /\ !G1.bad].
proof. byupto. qed.

(* Abstract procedure with oracles. *)
lemma L_rule_abs (A <: Adv {-G1}) &m :
  Pr[A(G1).main() @ &m : res = 0 /\ !G1.bad] = Pr[A(G2).main() @ &m : res = 0 /\ !G1.bad].
proof. byupto. qed.

(* -------------------------------------------------------------------- *)
(* Derived forms. *)
lemma L_sub &m :
     Pr[G1.main() @ &m : res = 0] - Pr[G2.main() @ &m : res = 0]
   = Pr[G1.main() @ &m : res = 0 /\ G1.bad] - Pr[G2.main() @ &m : res = 0 /\ G1.bad].
proof. byupto. qed.

lemma L_le &m :
  Pr[G1.main() @ &m : res = 0] <=
    Pr[G2.main() @ &m : res = 0] + Pr[G1.main() @ &m : G1.bad].
proof. byupto. qed.

lemma L_le_nbad &m :
  Pr[G1.main() @ &m : res = 0] <=
    Pr[G2.main() @ &m : res = 0 /\ !G1.bad] + Pr[G1.main() @ &m : res = 0 /\ G1.bad].
proof. byupto. qed.

lemma L_abs &m :
  `|Pr[G1.main() @ &m : res = 0] - Pr[G2.main() @ &m : res = 0]| <=
    `|Pr[G1.main() @ &m : res = 0 /\ G1.bad] - Pr[G2.main() @ &m : res = 0 /\ G1.bad]|.
proof. byupto. qed.

lemma L_maxr &m :
  `|Pr[G1.main() @ &m : res = 0] - Pr[G2.main() @ &m : res = 0]| <=
    maxr Pr[G1.main() @ &m : G1.bad] Pr[G2.main() @ &m : res = 0 /\ G1.bad].
proof. byupto. qed.

(* -------------------------------------------------------------------- *)
(* Error paths. *)
exception oops.

module H = {
  import var G1

  proc r() : unit = {
    bad <- false;
  }

  proc main() : int = {
    var x;
    c <- 0;
    bad <- false;
    x <- 1;
    return x;
  }

  proc reset() : int = {
    var x;
    c <- 0;
    bad <- false;
    x <- 0;
    if (c = 0) {
      bad <- true;
      bad <- false;
    }
    return x;
  }

  proc reset'() : int = {
    var x;
    c <- 0;
    bad <- false;
    x <- 0;
    if (c = 0) {
      bad <- true;
      bad <- true;
    }
    return x;
  }

  proc throw() : int = {
    var x;
    c <- 0;
    bad <- false;
    x <- 0;
    if (c = 0) { raise oops; }
    return x;
  }

  proc reset_call() : int = {
    var x;
    c <- 0;
    bad <- false;
    x <- 0;
    if (c = 0) {
      bad <- true;
      r();
    }
    return x;
  }
}.

lemma E_not_eq &m : Pr[G1.main() @ &m : !G1.bad] <= Pr[G2.main() @ &m : !G1.bad] + 0%r.
proof. fail byupto. abort.

lemma E_not_pr &m : Pr[G1.main() @ &m : !G1.bad] = 0%r.
proof. fail byupto. abort.

lemma E_mem &m &n : Pr[G1.main() @ &m : !G1.bad] = Pr[G2.main() @ &n : !G1.bad].
proof. fail byupto. abort.

lemma E_args &m : Pr[G1.noinit(1) @ &m : !G1.bad] = Pr[G2.noinit(2) @ &m : !G1.bad].
proof. fail byupto. abort.

lemma E_event &m : Pr[G1.main() @ &m : res = 0 /\ !G1.bad] = Pr[G2.main() @ &m : !G1.bad].
proof. fail byupto. abort.

lemma E_badform &m : Pr[G1.main() @ &m : res = 0] = Pr[G2.main() @ &m : res = 0].
proof. fail byupto. abort.

lemma E_not_upto &m : Pr[G1.main() @ &m : !G1.bad] = Pr[H.main() @ &m : !G1.bad].
proof. fail byupto. abort.

lemma E_reset &m : Pr[H.reset() @ &m : !G1.bad] = Pr[H.reset'() @ &m : !G1.bad].
proof. fail byupto. abort.

lemma E_reset_call &m : Pr[H.reset_call() @ &m : !G1.bad] = Pr[H.reset'() @ &m : !G1.bad].
proof. fail byupto. abort.

lemma E_raise &m : Pr[H.throw() @ &m : !G1.bad] = Pr[H.throw() @ &m : !G1.bad].
proof. fail byupto. abort.

lemma E_abs (A <: Adv) &m : Pr[A(G1).main() @ &m : !G1.bad] = Pr[A(G2).main() @ &m : !G1.bad].
proof. fail byupto. abort.

lemma E_shape &m : Pr[G1.main() @ &m : !G1.bad] < 1%r.
proof. fail byupto. abort.
