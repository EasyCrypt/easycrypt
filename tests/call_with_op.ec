require import AllCore.

module M = {
  proc f(x:int) : int = {
    return x;
  }

  proc g(x:int) : int = {
    var z;
    z <@ f(x);
    return z;
  }
}.

op f_spec x_ = hoare [M.f : x = x_ ==> res = x_].
op g_spec x_ = hoare [M.g : x = x_ ==> res = x_].

lemma f_ok1 x_ : f_spec x_.
proof.
  proc; auto.
qed.

lemma g_ok1 x_ : g_spec x_.
proof.
  proc.
  call (f_ok1 x_).
  auto.
qed.

lemma g_ok1_e x_ : g_spec x_.
proof.
  proc.
  ecall (f_ok1 x).
  auto.
qed.
 
op f_spec_all = forall x_, hoare [M.f : x = x_ ==> res = x_].

lemma f_ok2 : f_spec_all.
proof.
  move=> x_;proc; auto.
qed.

lemma g_ok2 x_ : g_spec x_.
proof.
  proc.
  call (f_ok2 x_).
  auto.
qed.

lemma g_ok2_e x_ : g_spec x_.
proof.
  proc.
  ecall (f_ok2 x).
  auto.
qed.



