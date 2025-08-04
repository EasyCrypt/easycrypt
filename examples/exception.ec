require import AllCore.

exception assume.
exception assert.

op p1: int -> bool.
op p2: int -> bool.

module M' ={
  proc truc (x:int) : int = {
  raise (! p1 x \/ ! p2 x) assume;
  if (!p1 x \/ !p2 x) { raise assert;}
  return x;
  }
}.

print M'.

lemma assume_assert  (_x:int):
hoare [M'.truc : _x = x ==> false | assume:p1 _x | assert: !(p1 _x /\ p2 _x)].
    proof.
      proc.
      wp.
      auto => &hr <- />. smt.
     qed.

lemma assert_assume (_x:int):
hoare [M'.truc : _x = x ==> false | assume:p2 _x | assert: !(p2 _x /\ p1 _x) ].
    proof.
      proc.
      wp.
      auto => &hr <- />. smt.
     qed.

lemma assert_assume' ( _x:int)  :
hoare [M'.truc : _x = x ==> false | assume: p1 _x /\ p2 _x | assert: !(p2 _x /\ p1 _x) ].
    proof.
      conseq (assume_assert _x) (assert_assume _x).
      + auto.
      + auto.
    qed.

exception e1.
exception e2.
exception e3.

module M ={
  proc f1 (x:int) : int = {
    raise (x <> 3) e1;
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
hoare [M.f1 : _x = x ==> (res <= 5) | e1:_x <= 3 | pd1].
    proof.
      proc.
       conseq (: _ ==> x = 5 | e1: _x = 3 | e2: pe | pd2).
      + move => &hr h x. smt.
      + wp. auto.
    qed.

lemma l_f2 (_x: int):
hoare [M.f2 : _x = x ==> res < 6 | e1: _x < 4 | e2:pe3 | e3: pe4 | pd2 ].
    proof.
      proc.
      if.
      + call (: _x = x ==> res = 5 | e1 : 3 = _x | e2: pd2 | pd2).
       + proc.
         wp. auto.
      wp. auto. smt.
      call (l_f1 _x).
      auto. smt.
  qed.

module M1 ={
    var i:int

  proc f1 (x:int) : int = {
    i <- 0;
    raise e2;
    return x;
  }

 proc f2 (x:int) : int = {
      i <- 1;
      x <@ f1(x);
      return x;
  }
}.

lemma test (_x: int):
hoare [M1.f2 : true ==> true |e2: M1.i = 0].
 proof.
   proc.
   call (: true ==> true | e2 : M1.i = 0).
   + proc. wp. auto.
   auto.
qed.

lemma test2 (_x: int):
hoare [M1.f1 : true ==> true |e2: M1.i = 0].
    proof.
      proc.
      conseq (: _ ==> _ |  e2: M1.i = 0).
      auto.
qed.

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
hoare [M2.f1 : _x = x ==> res = _x | e2 : _x = 0].
proof.
  proc.
  auto.
qed.

lemma test4 (_x: int):
hoare [M2.f2 : _x = x ==> res = _x + 1 | e2 : _x + 1= 0 ].
 proof.
   proc.
   ecall(test3 x).
   auto.
qed.
