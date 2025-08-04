require import AllCore.

exception e1.
exception e2.
exception e3.

module M ={
  proc f1 (x:int) : int = {
    if (x <> 3) else raise e1;
    x <- 5;
    return x;
  }

 proc f2 (x:int) : int = {
    if (x = 3)  {
      x <- x;
      x <@ f1(x);
    } else {
      x <@ f1(x);
    }
    return x;
  }
}.

op pe: bool.
op pe1: bool.
op pe2: bool.
op pe3: bool.
op pe4: bool.
op pd1: bool.
op pd2: bool.
op pd3: bool.

axiom a1: pd2 => pd1.
axiom a2: pe => pd1.
axiom a3: pd2 => pe3.
axiom a4: pd2 => pe4.
axiom a5: pd1 => pd2.

lemma l_f1 (_x: int):
  hoare [M.f1 : _x = x ==> (res <= 5) | e1 => _x <= 3 | _ => pd1].
proof.
  proc.
  conseq (: _ ==> x = 5 | e1 => _x = 3 | e2 => pe | _ => pd2).
  + move => &hr h x. smt(a1 a2).
  + wp. auto.
qed.

lemma l_f2 (_x: int):
  hoare [M.f2 : _x = x ==> res < 6 | e1 => _x < 4 | e2 => pe3 | e3 => pe4 | _ => pd2 ].
proof.
  proc.
  if.
  + call (: _x = x ==> res = 5 | e1 => 3 = _x | e2 => pd2 | _ => pd2).
    + proc.
      by auto.
    auto.
    smt(a3 a4).
  call (l_f1 _x).
  auto. smt(a5 a3 a4).
qed.
