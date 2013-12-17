(* -------------------------------------------------------------------- *)
module M1 = {
  proc f1() : int = {
    return 0;
  }
}.

module M2 = {
  proc f2() : int = {
    return 0;
  }
}.

module A1 = {
  proc g1() : int = {
    var x : int;

    x = M1.f1();
    return x;
  }
}.

module A2 = {
  proc g2() : int = {
    var x : int;

    x = M2.f2();
    return x;
  }
}.

(* -------------------------------------------------------------------- *)
lemma L : equiv[A1.g1 ~ A2.g2 : true ==> true].
proof -strict. by proc; inline *; wp; skip. qed.
