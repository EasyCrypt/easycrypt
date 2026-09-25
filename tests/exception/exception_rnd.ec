require import AllCore Distr DBool.

exception exn1.

module M = {
  var b : bool
  var i : int

  proc f () : unit = {
    i <- 1;
    if (i < 0) raise exn1;
    b <$ dbool;
  }

  proc g () : unit = {
    b <- true;
    raise exn1;
    b <$ dunit false;
  }
  proc h () : unit = {
    b <$ dunit true;
    raise exn1;
  }
}.

lemma f_ok : hoare [M.f : true ==> true | exn1 => M.i = 1].
proof. proc. rnd. wp. skip => />. qed.

lemma g_ok : hoare [M.g : true ==> false | exn1 => M.b].
proof. proc. rnd. wp. skip. done. qed.

lemma h_ok : hoare [M.h : true ==> false | exn1 => M.b].
proof. proc. wp. rnd. skip => />. smt(supp_dunit). qed.

lemma g_wrong : hoare [M.g : true ==> false | exn1 => !M.b].
proof. proc. fail (rnd; wp; skip;done). abort.
