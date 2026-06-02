require import AllCore Int Real.

theory ConseqPrePostHoare.
module M = {
  proc f(x: int) = {
    var y : int;

    y <- x;
    x <- y + x;
    return x;
  }
}.

lemma bar (x: int) (y: int): true. proof. by done. qed.

lemma foo : hoare[M.f :  2 < arg /\ arg < 5 ==> res = 4].
proof.
conseq (_: #pre ==> #post).
proc.
conseq (_: #pre ==> #post). 
abort.
end ConseqPrePostHoare.


theory ConseqPrePostEquiv.
module M = {
  proc f(x: int) = {
    var y : int;

    y <- x;
    x <- y + x;
    return x;
  }
}.


lemma foobar : equiv[M.f ~ M.f : ={arg} /\ arg{1} = 2 ==> ={res} /\ res{1} = 3].
proof.
conseq (_: #pre /\ arg{2} = 2 ==> #post /\ res{2} = 3); auto.
proc.
conseq (_: #{/x{1}}pre ==> #{/x{1}}post). auto.
move=> ? ? ? ? ? <*>> //.
abort.
end ConseqPrePostEquiv.
