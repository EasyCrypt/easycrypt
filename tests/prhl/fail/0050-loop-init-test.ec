module U = {
  proc f1 () : int = {
    var y, x;
    x = 1;
    y = 0;
    while (x <> 2) { y = y + 1; x = 2; }
    return y;
  }

  proc f2 () : int = {
    var y, x;
    x = 2;
    y = 0;
    while (x <> 2) { y = y + 1; x = 2; }
    return y;
  }
}.

equiv UU: U.f1 ~ U.f2 : true ==> ={res}.
proof.
  proc.
  while (={y}).
  wp. skip. auto.
  auto.
qed.

lemma pr_f1 &m : Pr[U.f1() @ &m : res = 1] = 1%r.
proof.
  byphoare => //.
  proc.
  rcondt 3; first by auto.
  rcondf 5;auto.
qed.

lemma pr_f2 &m : Pr[U.f2() @ &m : res = 1] = 0%r.
proof.
  byphoare => //.
  proc.
  rcondf 3;first by auto.
  wp. 
  hoare. auto.
qed.

lemma pr_f1_f2 &m : Pr[U.f1() @ &m : res = 1] = Pr[U.f2() @ &m : res = 1].
proof.
  byequiv UU => //.
qed.

lemma F : false by [].