(* [byupto] compares the two procedures syntactically, the variables of
   one standing for the same ones of the other: their parameters must
   then be the same, in the same order. *)
require import AllCore.

module M = {
  var b : bool

  proc f1(x : int, y : int) : int = {
    b <- false;
    return x;
  }

  proc f2(y : int, x : int) : int = {
    b <- false;
    return x;
  }

  proc f3(x : int, y : int) : int = {
    b <- false;
    return x;
  }

  proc h1(x : int, y : int) : int = {
    return x;
  }

  proc h2(y : int, x : int) : int = {
    return x;
  }

  (* the same parameters, swapped in a callee *)
  proc g1() : int = {
    var r;
    b <- false;
    r <@ h1(1, 2);
    return r;
  }

  proc g2() : int = {
    var r;
    b <- false;
    r <@ h2(1, 2);
    return r;
  }
}.

(* f1(1, 2) returns 1, f2(1, 2) returns 2 *)
lemma L &m : Pr[M.f1(1, 2) @ &m : res = 1 /\ !M.b] = Pr[M.f2(1, 2) @ &m : res = 1 /\ !M.b].
proof. fail byupto. abort.

lemma Lcall &m : Pr[M.g1() @ &m : res = 1 /\ !M.b] = Pr[M.g2() @ &m : res = 1 /\ !M.b].
proof. fail byupto. abort.

(* same parameters: still accepted *)
lemma L13 &m : Pr[M.f1(1, 2) @ &m : res = 1 /\ !M.b] = Pr[M.f3(1, 2) @ &m : res = 1 /\ !M.b].
proof. by byupto. qed.
