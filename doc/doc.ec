(* The following returns an exception *)
(* game G = { *)
(*   var b : bool *)

(*   fun f (y:int) : int = { *)
(*     var x : int; *)
(*     b = {0,1}; *)
(*     if (b) { *)
(*       x = y + 1; *)
(*     } *)
(*     while (x <= 10) x = x + 2; *)
(*     return x; *)
(*   } *)

(* }. *)

(* equiv eq_res : G.f ~ G.f : ={y} ==> ={res}. *)
(* eqobs_in (={x}) (true) (={y}). *)


game G = {
  var b : bool
  var y:int
  var x : int
  var w : int
  var l : int

  fun f () : int = {
    var z : int = 1;
    b = {0,1};
    if (b) {
      x = y + z;
    } 
    while (x <= 10) x = x + 2;
    l = 2;
    return x;
  }

  fun g () : int = {
    var z : int = 1;
    b = {0,1};
    if (b) {
      w = y + z;
    } 
    while (w <= 10) { w = w + 2; b = !b;}
    l = 2;
    return w;
  }

}.

equiv eq_res : G.f ~ G.g : ={y} && x{1}=w{2} ==> ={res,l}.
(* eqobs_in (true) (true) (true). *)
eqobs_in (true) (true) (={y,l} && x{1}=w{2}).
trivial.

game Gunroll = {
  fun f (x:int) : int = {
    x = x + 1;
    while (x <= 10) x = x + 2;
    x = x + 3;
    while (x <= 20) x = x + 4;
    x = x + 5;
    return x;
  }
 
 fun g (x:int) : int = {
    x = x + 1;
    while (x <= 10) x = x + 2;
    x = x + 3;
    return x;
  } 
 fun e (x:int) : int = {
  return x;
 }
}.

equiv test_condt : Gunroll.f ~ Gunroll.e : 
  ={x} && x{1} <= 9 ==> res{2} <= res{1}.
wp.
condt{1} last.
admit.
admit.
save.

equiv test_condt : Gunroll.g ~ Gunroll.e : 
  ={x} && 10 < x{1} ==> ={res}.
wp.
condf{1} last.
admit.
admit.
save.



equiv test_splitw : Gunroll.g ~ Gunroll.g : ={x} ==> ={res}.
splitw at 2: x < 10.


equiv test_unroll : Gunroll.f ~ Gunroll.f : ={x} ==> ={res}.

unroll{1} at 2.
condt
while e do c
if e {c;while e do c}

eqobs_in (={x}) (true) (={x}).    
trivial.
save.

game Gcall1 = {
  var x:int

  fun f (y:int) : int = { 
    return y + 1;
  }

  fun g (z:int) : int = {
    var w : int;
    w = f(0);
    return w;
  }
}.

game Gcall2 = Gcall1
   where f = {
     return y + x;
   }.

pred P(x1,x2:int) = x1 = x2.

equiv f_12 : Gcall1.f ~ Gcall2.f : ={y} && x{2} = 1 ==> P(res{1},res{2})
by auto.

equiv g_12 : Gcall1.g ~ Gcall2.g :
  ={z} && x{2} = 1 ==> P(res{1}+1,res{2}+1).
call using f_12.

equiv g_12' : Gcall1.g ~ Gcall2.g :
  ={z} && x{2} = 1 ==> P(res{1}+1,res{2}+1).
call (x{2} = 1).

game Gwhile = { 
  var x,y : int
  fun f () : unit = {
    x = 0;
    while (x < 10) x = x + 1;
  }
  fun g () : unit = {
    x = 10;
  }
}.

equiv test_while_bwd : Gwhile.f ~ Gwhile.f : ={y} ==> ={x,y} && x{1}=10.
while : ={x} && x{1} <= 10.
 trivial.
trivial.
save.

equiv test_while_fwd : Gwhile.f ~ Gwhile.f : ={y} ==> ={x,y} && x{1}=10.
sp.
while >> : ={x} && x{1} <= 10.
 trivial.
trivial.
save.

equiv test_while_l_bwd : Gwhile.f ~ Gwhile.g : ={y} ==> ={x,y} && x{1}=10.
while{1} : x{1} <= 10.
 trivial.
trivial.
save.

equiv test_while_l_fwd : Gwhile.f ~ Gwhile.g: ={y} ==> ={x,y} && x{1}=10.
sp.
while{1} >> : x{1} <= 10.
 trivial.
trivial.
save.

game G1 = {
  fun f () : int = {
    var x : int = [0..10];
    if (x = 10) x = 0;
    else x = x - 1; 
    x = x + 22;
    x = x + 1;
    return x;
  }
}.

game G2 = { 
  fun f () : int = { 
    var x : int = [0..10];
    if (x = 10) {
      x = 0; 
    } else { 
      x = x - 1;
    } 
    x = x + 23;
    return x;
  }
}.

(* Example for ifneg *)
equiv test_ifneg :  G1.f ~ G2.f : true ==> ={res}.
ifneg {1} at 2.
ifneg {2} at 2.
wp 2 2.
ifneg at 2.
ifneg last.
rnd >>.
ifneg.
trivial.
save.

(* Example for asgn *)

equiv test_asgn : G1.f ~ G2.f : true ==> ={res}.
 app 1 1 ={x};[trivial | ].
 if.
 admit.
 asgn.
 trivial.
save.

(* Example for app *)
equiv test_app : G1.f ~ G2.f : true ==> ={res}.
 asgn.
 app 1 1 ={x}.
 trivial.
 trivial.
save.

game G3 = {
  var M : (int,int) map
  fun f (x:int) : int = {
     M[x] = [0 .. x];
   
    return x;
  }
}.
game G4 = {
  fun f (y:int) : int = {
    var x:int = [0 .. 10];
    return x + y;
  }
}.

game G5 = {
  fun f() : int = {
    var x : int = 0;
    var y : int = 1;
    return x + y;
  }
}.

game G6 = {
  fun f() : int = {
    var y : int = 1;
    var x : int = 0;
    return x + y;
  }
}.
checkproof.
equiv test_let : G5.f ~ G6.f : true ==> ={res}.
case : x = y.
trivial.
trivial.
save.
let{1} at 2 w : int = x + 1.



pred toto (x:int) = x = 1.
equiv test_1 : G3.f ~ G3.f : x{1}<=10  ==> res{1} <= 10.
 rnd.
 case{1} : toto(x).
(*exists (x, l : int),  x{1} = x && (0 <= x && x <= l) && l <= 10 *)
equiv test_2 : G4.f ~ G4.f : y{1}=1  ==> res{1} <= 11.
rnd>>{1}.
pre 
exists (x : int),  && (0 <= x{1} && x{1} <= x) && x <= 10 *)
 rnd<<{2}.
 trivial.
 asgn.


 condt{1} at 2.
if{1}.
 app 1 1 ={x}.
 rnd.

 (* impossible to prove *)
 admit.  
 trivial.
save.
