require import Int.

module OneSided = {
  var x : int

  proc init() : unit = {
    x = 0;
  }

  proc main() : unit = {
    init();
    x = x + 1;
  }

  proc main2(): unit = {
    x = 1;
  }
}.

lemma bar : hoare [OneSided.init: true ==> OneSided.x =  0].
proof -strict.
 proc; wp; skip; smt.
qed.

lemma main :
  equiv [OneSided.main ~ OneSided.main2: true ==> OneSided.x{1} = OneSided.x{2}].
proof -strict.
  proc; seq 1 0: (OneSided.x{1} = 0); last wp; skip; smt.
  call{1} (_ : true ==> OneSided.x = 0).
  apply bar.
