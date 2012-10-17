cnst l : int.
cnst b : int.
cnst L : int.
cnst q : int.

type key   = bitstring{l}.
type block = bitstring{b}.
type mac   = bitstring{l}.
type msg   = bitstring{L}.

op f    : (key, block) -> mac.
op F    : (key, msg) -> mac.
op NMAC : (key, key, msg) -> mac.
op pad  : mac -> block.

axiom pad_inj :
  forall (x1,x2:mac), pad(x1) = pad(x2) => x1 = x2.

axiom NMAC_def : 
  forall (k1,k2:key, x:msg), NMAC(k1, k2, x) = f(k1, pad(F(k2, x))).


(* Game encoding the MAC-security of NMAC *)
adversary A() : msg * mac { msg -> mac }.

game EF_MAC = {
  var k1, k2 : key
  var n : int
  var X : msg list

  fun MAC (x:msg) : mac = {
    X = x :: X;
    n = n + 1;
    return NMAC(k1, k2, x);
  }

  abs A = A {MAC}

  fun Main() : bool = {
    var x : msg;
    var y : mac;
    k1 = {0,1}^l;
    k2 = {0,1}^l;
    X = [];
    n = 0;
    (x,y) = A();
    return (y = NMAC(k1, k2, x) && !mem(x, X));
  }
}.

(* Expand definition of NMAC, store arguments of f(k1,.) *)
game EF_MAC' = {
  var k1, k2 : key
  var n : int
  var X : msg list
  var Y : mac list

  fun MAC(x:msg) : mac = {
    var y : mac = F(k2, x);
    X = x :: X;
    Y = y :: Y;
    n = n + 1;
    return f(k1, pad(y));
  }

  abs A = A {MAC}

  var x : msg
  var y : mac

  fun Main() : bool = {
    k1 = {0,1}^l;
    k2 = {0,1}^l;
    X = [];
    Y = [];
    n = 0;
    (x,y) = A();
    return (y = f(k1, pad(F(k2, x))) && !mem(x, X));
  }
}.

prover "alt-ergo".
 
equiv EF_MAC_EF_MAC' : EF_MAC.Main ~ EF_MAC'.Main : true ==> ={res}
by auto (={k1,k2,X,n}).

claim Pr_EF_MAC_EF_MAC' : 
  EF_MAC.Main[res && n <= q] = EF_MAC'.Main[res && n <= q]
auto.

(* Case analysis: 

 1) If A succeeds and there is an x' in X s.t. F(k2, x') = F(k2, x),
    then A can be used to build an algorithm AF against the WCR of F;
    (x,x') is a collision

 2) If A succeeds and there is no x' in X s.t. F(k2, x') = F(k2, x),
    then A can be used to build an algorithm Af against the
    MAC-security of f; (pad(F(k2, x')), y) is a valid forgery since 
    pad(F(k2, x')) is fresh
*)

claim Pr_split :
  EF_MAC'.Main[res && n <= q] <=
  EF_MAC'.Main[res && n <= q &&  mem(F(k2, x), Y)] +
  EF_MAC'.Main[res && n <= q && !mem(F(k2, x), Y)]
split.


(* Case 1: there is an x' in X s.t. F(k2, x') = F(k2, x) *)

(* Game encoding the weak-collision resistance of F *)
 
adversary AF() : msg * msg { msg -> mac }.

(* REMARK: there is an off-by-one error in the proof of security in
  the Crypto'96 paper: AF must call the iterated hash function F one
  more time to compute the value of F(k2,x) in order to be able to
  find a value x' that collides with x among the queries made by A.
  Thus, one must assume that F is (epsilon_F, q+1, t, L)-secure
  instead of (epsilon_F, q, t, L)-secure. 
*)
game WCR_F = {
  var k : key
  var n : int
  var YX : (mac, msg) map
 
  fun O_F (x:msg) : mac = {
    n = n + 1;
    return F(k, x);
  }

  (* BEGIN Adversary AF *)
  var k1 : key

  fun MAC (x:msg) : mac = {
    var y : mac;
    y = O_F(x);
    YX[y] = x;
    return f(k1, pad(y));
  }

  abs A = A {MAC}

  fun AF() : msg * msg = {
    var x : msg;
    var y, y' : mac;        
    k1 = {0,1}^l;
    YX = empty_map;
    n = 0;
    (x,y) = A();
    y' = O_F(x);
    return (x, YX[y']); 
  }
  (* END Adversary AF *)

  fun Main() : bool = {
    var x1 : msg;
    var x2 : msg;
    k = {0,1}^l;
    (x1, x2) = AF();
    return (F(k, x1) = F(k, x2) && !(x1 = x2));
  }
}.

equiv EF_MAC'_WCR : EF_MAC'.Main ~ WCR_F.Main : 
  true ==>
  (res{1} && n <= q && mem(F(k2, x), Y)){1} => (res && n <= q + 1){2}.
proof.
 inline{2}; wp.
 swap{2} 1.
 auto (={k1,n} && k2{1} = k{2} &&
  (forall (x:msg), in_rng(x,YX{2}) = mem(x,X{1})) &&
  (forall (y:mac), in_dom(y,YX{2}) = mem(y,Y{1})) &&
  (forall (y:mac), in_dom(y,YX{2}) => F(k{2}, YX{2}[y]) = y) &&
  (forall (x:msg), in_rng(x,YX{2}) => in_dom(F(k{2},x), YX{2}))).
 trivial.
save.

claim Pr_EF_MAC_WCR_F :
  EF_MAC'.Main[res && n <= q && mem(F(k2, x), Y)] <=
  WCR_F.Main[res && n <= q + 1]
auto.


(* Case 2: there is no x' in X s.t. F(k2, x') = F(k2, x) *)

(* Game encoding the MAC-security of the compression function f *)
game EF_MAC_f = {
  var k : key
  var X : block list
  var n : int

  fun O_f (x:block) : mac = {
    X = x :: X;
    n = n + 1;
    return f(k, x);
  }

  (* Adversary Af *)
  var k2 : key

  fun MAC (x:msg) : mac = {
    var y : mac = F(k2, x);
    var z : mac;   
    z = O_f(pad(y));
    return z;
  }

  abs A = A {MAC}

  fun Af() : block * mac = {
    var x : msg;
    var y : mac;        
    k2 = {0,1}^l;
    (x,y) = A();
    return (pad(F(k2, x)), y); 
  }

  fun Main() : bool = {
    var x : block;
    var y : mac;   
    k = {0,1}^l;
    X = [];
    n = 0;
    (x,y) = Af();
    return (y = f(k, x) && !mem(x, X));
  }
}.

equiv EF_MAC_EF_MAC_f : EF_MAC'.Main ~ EF_MAC_f.Main : 
 true ==> ={n} && ((res && !mem(F(k2, x), Y)){1} => res{2}).
proof.
 inline{2}; wp.
 auto (={k2,n} && k1{1} = k{2} && forall (x:mac), mem(x,Y{1}) = mem(pad(x),X{2})). 
 trivial.
save.

claim Pr_EF_MAC_EF_MAC_f :  
  EF_MAC'.Main[res && n <= q && !mem(F(k2, x), Y)] <=
  EF_MAC_f.Main[res && n <= q]
using EF_MAC_EF_MAC_f.

(* Conclusion *)
claim security_bound : 
  EF_MAC.Main[res && n <= q] <= 
  WCR_F.Main[res && n <= q + 1] + EF_MAC_f.Main[res && n <= q].
