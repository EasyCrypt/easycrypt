require import AllCore.

exception e2.

module M2 ={

  proc f1 (x:int) : int = {
    return x;
  }

  proc f2 (x:int) : int = {
    x <- x + 1;
    x <@ f1(x);
    return x;
  }
}.

lemma test3 (_x: int):
  hoare [M2.f1 : _x = x ==> res = _x | e2 => _x = 0].
proof.
  proc.
  auto.
qed.

lemma test4 (_x: int):
  hoare [M2.f2 : _x = x ==> res = _x + 1 | e2 => _x + 1 = 0 ].
proof.
  proc.
  ecall(test3 x).
  auto.
qed.
