type t.
op test : int -> t * t * t.

game G = {
  fun f (x:int) : t * t = {
    var t1,t2,t3 : t;
    (t1,t2,t3) = test(x);
    return (t1,t2);
  }

  fun g (x:int) : t * t = {
    var t2 : t * t;
    t2 = f(x);
    return let f,s = t2 in (snd(t2),f);
  }
}.

lemma test2 : forall (x1,x2,y1,y2:int),
   (x1,y1) = (x2,y2) =>
   x1 = x2 && y1 = y2.

equiv test4 : G.g ~ G.g : (true) by auto.

equiv test3 : G.g ~ G.g : ={x} ==> ={res}.
  call.
  trivial.
save.

equiv test1 : G.f ~ G.f : ={x} ==> ={res}.
 trivial.
save.

equiv test_inline1 : G.g ~ G.g : ={x} ==> ={res}.
  inline.
  trivial.
save.

equiv test_inline2  : G.g ~ G.g : ={x} ==> ={res}.
  inline{1} f.
  inline{2} last.
  trivial.
save.

equiv test_inline3  : G.g ~ G.g : ={x} ==> ={res}.
  inline at 0.
  trivial. 
save. 

equiv test2 : G.g ~ G.g : ={x} ==> ={res}.
 call using test1.
 trivial.
save.

game G1 = {
  fun f (x:int) : t * t = {
    var t1,t2,t3 : t;
    if (x = x) {
      (t1,t2,t3) = test(x);
    } else {
      (t1,t2,t3) = test(x);
    }
    return (t1,t2);
  }

  fun g (x:int) : t * t = {
    var t1,t2,t3 : t;
    if (x = x) {
      (t1,t2,t3) = test(x);
    } else {
      (t1,t2,t3) = test(x);
    }
    return (t1,t2);
  }
}.

equiv test_cond : G1.f ~ G1.f : ={x} ==> ={res}.
  condt last.
  trivial.
save.

equiv test_cond1 : G1.f ~ G1.f : ={x} ==> ={res}.
  condt{1}.
  condt{2} at 1.
  trivial.
save.

(* Test while *)

game G2 = {
  fun f (x:int) : int * int = {

    while (x <> x) {
      x = x;
    }
    return (x,x);
  }
}.

equiv test_while1 : G2.f ~ G2.f : ={x} ==> ={res}.
  condf.
  trivial.
save.

equiv test_while2 : G2.f ~ G2.f : ={x} ==> ={res}.
  condf at 1.
  trivial.
save.

equiv test_while3 : G2.f ~ G2.f : ={x} ==> ={res}.
  condf last.
  trivial.
save.






