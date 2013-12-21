

op test : int*int -> int.


op f : int -> int -> int*int.

op g : int -> int -> int*int.


require import Int.

op fst (x:int*int) = let (x,y) = x in x.
op snd (x:int*int) = let (y,x) = x in x.

require import FMap.

module Test = {

  proc foo (x y:int) : int = {
    var aux : int;
    aux = x;
    x = y;
    y = aux;
    return test(y,x);
  }

  proc bar(x y :int) : int*int = {
    (x,y) = (y,x);
    return (x,y);
  }

  
  proc test (x y:int) : int*int = {
    (y,x) = (snd (x,y), fst (x,y));
    (x,y) =  (fst (x,y), snd (x,y));
    return (x,y);
  }

  proc map (x y :int) : (int,int) map = {
    var m : (int,int) map;
    var m2 : (int,int) map;
    (x,y) = (y,x);
    (y,x) = (x,y);
    m.[x] = y;
    (x,y) = (y,x);
    m.[y] = x;
    m.[y] = x;
    (m2,m) = (m,m2);
    (m2,m) = (m,m2);
    (x,y) = (y,x);
    return m;
  }


  proc eq() : bool = {
    var x, y, z : int;
    x = z;
    y = z;
    z = 1;
    return x=y;
  }

  proc if_() : int = {
    var x : int;
    x = 0;
    if (x=0) {
      x = 1;
    } else {
      x = 0;
    }
    x =1;
    if (x=1) {
      while(x=1){ x=1;}
    }
    return x;
  }

}.

lemma if_ : hoare [Test.if_ : true ==> res=1]. proc.
sp.
if; [| skip;trivial].
while (x=1); sp; skip; trivial.
qed.

lemma eq : hoare [Test.eq : true ==> res]. proc.
sp.
skip; trivial.
qed.

lemma eq_ : hoare [Test.eq : true ==> res]. proc.
sp 1. (* splitting the sp invocations is equivalent but not syntactically equal *)
sp 1.
sp.
sp. (* sp doesn't fail when it doesn't progress *)
wp. (* neither wp does*)
skip; trivial.
qed.

lemma eq__ : equiv [Test.eq ~ Test.eq : true ==> res{1}]. proc.
sp 1 1.
sp 1 0.
sp.
skip; trivial.
qed.

lemma eq_equiv : hoare [Test.eq : true ==> res]. proc.
wp 1.
sp.
skip; trivial.
qed.

lemma map : hoare [Test.map : x=0 /\ y=1 ==> res.[0]=Some 1].
proc.
sp.
elim *; intros m0.
skip; intros &hr.
smt.
qed.

lemma foo : hoare [Test.foo : 0 <= test(x,y) ==> 0 <= res].
proc.
sp.
skip;trivial.
qed.

lemma bar_ : phoare [Test.bar :  y=1 /\ x=0  ==> snd res = 0 /\ fst res = 1] = 1%r.
proc.
sp.
skip; trivial.
qed.


lemma bar : hoare [Test.bar :  y=1 /\ x=0  ==> snd res = 0 /\ fst res = 1].
proc.
sp.
skip; trivial.
qed.

lemma test : hoare [Test.test : x+y = 0 ==> fst res + snd res = 0].
proc.
sp.
skip; trivial.
qed.





