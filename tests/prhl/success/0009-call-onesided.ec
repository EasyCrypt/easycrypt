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
  hoare [OneSided.init: true ==> OneSided.x =  0]
proof.
fun;wp;skip;trivial.
save.

lemma main:
  equiv [OneSided.main ~ OneSided.main2: true ==> OneSided.x{1} = OneSided.x{2}]
proof.
fun;
app 1 0: (OneSided.x{1} = 0);[ | wp;skip;trivial ].
call {1} (true) (OneSided.x = 0);[ apply bar | intros _;skip;trivial ].
save.