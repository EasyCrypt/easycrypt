require import AllCore.

exception assume.
exception assert.

op p1: int -> bool.
op p2: int -> bool.

module M' ={
  proc truc (x:int) : int = {
  if (! p1 x \/ ! p2 x) else raise assume;
  if (!p1 x \/ !p2 x) raise assert;
  return x;
  }
}.

lemma assume_assert (_x:int):
  hoare [M'.truc : _x = x ==>
           false | assume => p1 _x | assert => !(p1 _x /\ p2 _x)
        ].
proof.
  proc.
  wp.
  auto => &hr <- /> /#.
qed.

print assume_assert.

lemma assert_assume (_x:int):
  hoare [M'.truc : _x = x ==>
           false | assume => p2 _x | assert => !(p2 _x /\ p1 _x)
        ].
proof.
  proc.
  wp.
  auto => &hr <- /> /#.
qed.

lemma assert_assume' ( _x:int)  :
  hoare [M'.truc : _x = x ==>
           false | assume => p1 _x /\ p2 _x | assert => !(p2 _x /\ p1 _x) ].
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

exception arg1 of int.

op toto i = arg1 i.

module M3 = {
  proc f () = {
    raise (toto 3);
  }

}.

lemma test5 :
  hoare [M3.f : true ==> false | arg1 x => x = 3].
proof.
  proc. wp. skip => //.
qed.

lemma test6 :
  hoare [M3.f : true ==> false | arg1 x => x = 3].
proof.
  conseq (: _ ==> _ | arg1 x => 3 = x).
  + done.
  proc. wp. skip => //.
qed.


abstract theory Et.

  type t.

  op test : t -> bool.

  op truc : t -> exn.

  exception et of t.
  exception et2 of t * t.

  print et2.

  module Truc = {
    proc f (x:t):t = {
     if (test x) {raise (et x);}
    return x;
    }
  }.

  axiom hf :  forall (_x :t), hoare [Truc.f : _x = x ==> res = _x | et x => test x = false].
end Et.

require import List.
print list.

exception et1 of int.

clone Et as H with
type t <- int(* , *)
(* op et <- et1 *).

print H.
print H.truc.
print H.et.
print H.et2.

  (* exception arg ['a] of 'a. *)

exception evar of int.

op v : int.

module Mv ={
  var i:int

  proc f1 (x:int) : int = {
    i <- 0;
    raise (evar (v + i)) ;
    return x;
  }
}.

lemma testv :
  hoare [Mv.f1 : true ==> false | evar a => a = v].
proof.
  proc. wp. skip => //.
qed.
