require import AllCore.

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
