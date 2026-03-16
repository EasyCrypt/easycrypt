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
