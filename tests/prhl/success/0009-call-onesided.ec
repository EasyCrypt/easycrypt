require import Int.

module OneSided = {
  var x:int
  fun init():unit = {
    x = 0;
  }

  fun main(): unit = {
    init();
    x = x + 1;
  }

  fun main2(): unit = {
    x = 1;
  }
}.

lemma bar:
  hoare [OneSided.init: true ==> OneSided.x =  0].
proof.
fun;wp;skip;trivial.
save.

lemma main:
  equiv [OneSided.main ~ OneSided.main2: true ==> OneSided.x{1} = OneSided.x{2}].
proof.
fun;
seq 1 0: (OneSided.x{1} = 0);[ | wp;skip;trivial ].
call {1} (true) (OneSided.x = 0);[ apply bar | intros _;skip;trivial ].
save.

module Framing = {
  var x:int
  var y:int

  fun update_x(v:int): unit = {
    x = v;
  }

  fun main(): unit = {
    y = 0;
    update_x(42);
  }
}.

lemma frame:
  equiv [Framing.main ~ Framing.main: true ==> Framing.y{1} = Framing.y{2} /\ Framing.y{1} = 0].
proof.
fun.
  call{1} (true) (true).
    fun;wp;skip;trivial.
  intros _;call{2} (true) (true).
    fun;wp;skip;trivial.
  intros _;wp;skip;trivial.
save.