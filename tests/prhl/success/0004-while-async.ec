
require import Int.


module Test = {
  var x : int
  proc test () : unit = {
        while ( x<10) {
      x = x + 1;
    }
  }
}.

lemma foo : forall (x y:int), !(x<y) => y<= x.
smt.
save.

lemma test : 
equiv [Test.test ~ Test.test : ={Test.x} /\ Test.x{1}<= 10 /\ Test.x{2}<= 10 ==> Test.x{1}=10 /\ Test.x{2}=10].
proc.
while{1} (Test.x{1}<=10) (10-Test.x{1}).
intros &m z.
wp;skip;smt.
while{2} (Test.x{2}<=10) (10-Test.x{2}).
intros &m z.
wp; skip; smt.
wp;skip;smt.
save.

