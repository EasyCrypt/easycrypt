require import AllCore.

exception e2.

op o : exn = e2.

module M1 ={
  var i:int

  proc f1 (x:int) : int = {
    i <- 0;
    raise o;
    return x;
  }

  proc f2 (x:int) : int = {
    i <- 1;
    x <@ f1(x);
    return x;
  }
}.

lemma test (_x: int):
  hoare [M1.f2 : true ==> true |e2 => M1.i = 0].
proof.
  proc.
  call (: true ==> true | e2 => M1.i = 0).
  + proc. wp. auto.
  by auto.
qed.

lemma test2 (_x: int):
  hoare [M1.f1 : true ==> true |e2 => M1.i = 0].
proof.
  proc.
  conseq (: _ ==> _ |  e2 => M1.i = 0).
  auto.
qed.
