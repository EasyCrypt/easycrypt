cnst p : int.
cnst l : int.
cnst n : int.

type key        = bitstring{p}.
type random     = bitstring{l}.
type message    = bitstring{n}.
type ciphertext = bitstring{l} * bitstring{n}.
type func.

cnst zero : bitstring{n} = bs0_n.

adversary A() : bool { (key, random) -> message;  (int, func) -> ciphertext }.

adversary Eval(g:func) : message { (key, random) -> message }.

pop KG : () -> (int, key) map.

game Real = {
 var K : (int, key) map
 var L : (key * random, message) map

 fun H(k:key, r:random) : message = {
   if (!in_dom((k,r), L)) {
     L[(k,r)] = {0,1}^n;
   }
   return L[(k,r)];
 }

 abs Eval = Eval {H}

 fun Enc(j:int, g:func) : ciphertext = {
   var m : message;
   var c, h : bitstring{n};
   var r : random;
   m = Eval(g);
   r = {0,1}^l;
   h = H(K[j], r);
   c = h ^^ m;
   return (r, c);
 }

 abs A = A {H, Enc}

 fun Main() : bool = {
   var b : bool;
   K = KG();
   L = empty_map;
   b = A();
   return b;
 }  
}.

game Real' = {
 var K : (int, key) map
 var L : (key * random, message) map
 var X : (key * random) list
 var bad : bool

 fun H(k:key, r:random) : message = {
   if (!in_dom((k,r), L)) {
     L[(k,r)] = {0,1}^n;
   }
   return L[(k,r)];
 }

 abs Eval = Eval {H}

 fun Enc(j:int, g:func) : ciphertext = {
   var m : message;
   var c, h : bitstring{n};
   var r : random;
   m = Eval(g);
   r = {0,1}^l;
   if (in_dom((K[j], r), L)) {
     bad = true;
     c = L[(K[j], r)] ^^ m;
   }
   else {
     c = {0,1}^n;
     L[(K[j], r)] = c ^^ m;
     X = (K[j], r) :: X;
   }
   return (r, c);
 }

 fun H'(k:key, r:random) : message = {
   if (mem((k,r), X)) { bad = true; }
   if (!in_dom((k,r), L)) {
     L[(k,r)] = {0,1}^n;
   }
   return L[(k,r)];
 }

 abs A = A {H', Enc}

 fun Main() : bool = {
   var b : bool;
   K = KG();
   L = empty_map;
   X = [];
   bad = false;
   b = A();
   return b;
 }  
}.

game Hybrid = {
 var K : (int, key) map
 var L : (key * random, message) map
 var X : (key * random) list
 var bad : bool

 fun H(k:key, r:random) : message = {
   if (!in_dom((k,r), L)) {
     L[(k,r)] = {0,1}^n;
   }
   return L[(k,r)];
 }

 abs Eval = Eval {H}

 fun Enc(j:int, g:func) : ciphertext = {
   var m : message;
   var c : bitstring{n};
   var r : random;
   m = Eval(g);
   r = {0,1}^l;
   c = {0,1}^n;
   if (in_dom((K[j], r), L) || mem((K[j], r), X)) {
     bad = true;
   }
   else {
     X = (K[j], r) :: X;
   }
   return (r, c);
 }

 fun H'(k:key, r:random) : message = {
   if (mem((k,r), X)) { bad = true; }
   if (!in_dom((k,r), L)) {
     L[(k,r)] = {0,1}^n;
   }
   return L[(k,r)];
 }

 abs A = A {H', Enc}

 fun Main() : bool = {
   var b : bool;
   K = KG();
   L = empty_map;
   X = [];
   bad = false;
   b = A();
   return b;
 }  
}.

game Fake' = {
 var K : (int, key) map
 var L : (key * random, message) map
 var X : (key * random) list
 var bad : bool

 fun H(k:key, r:random) : message = {
   if (!in_dom((k,r), L)) {
     L[(k,r)] = {0,1}^n;
   }
   return L[(k,r)];
 }

 abs Eval = Eval {H}

 fun Enc(j:int, g:func) : ciphertext = {
   var m : message;
   var c, h : bitstring{n};
   var r : random;
   m = Eval(g);
   r = {0,1}^l;
   if (in_dom((K[j], r), L)) {
     bad = true;
     c = L[(K[j], r)] ^^ zero;
   }
   else {
     c = {0,1}^n;
     L[(K[j], r)] = c ^^ zero;
     X = (K[j], r) :: X;
   }
   return (r, c);
 }

 fun H'(k:key, r:random) : message = {
   if (mem((k,r), X)) { bad = true; }
   if (!in_dom((k,r), L)) {
     L[(k,r)] = {0,1}^n;
   }
   return L[(k,r)];
 }

 abs A = A {H', Enc}

 fun Main() : bool = {
   var b : bool;
   K = KG();
   L = empty_map;
   X = [];
   bad = false;
   b = A();
   return b;
 }  
}.

game Fake = {
 var K : (int, key) map
 var L : (key * random, message) map

 fun H(k:key, r:random) : message = {
   if (!in_dom((k,r), L)) {
     L[(k,r)] = {0,1}^n;
   }
   return L[(k,r)];
 }

 abs Eval = Eval {H}

 fun Enc(j:int, g:func) : ciphertext = {
   var m : message;
   var c, h : bitstring{n};
   var r : random;
   m = Eval(g);
   r = {0,1}^l;
   h = H(K[j], r);
   c = h ^^ zero;
   return (r, c);
 }

 abs A = A {H, Enc}

 fun Main() : bool = {
   var b : bool;
   K = KG();
   L = empty_map;
   b = A();
   return b;
 }  
}.

prover "alt-ergo".
timeout 3.

axiom KG() : K1 = KG() ~ K2 = KG() : true ==> K1 = K2.

equiv Real_Real'_Enc : Real.Enc ~ Real'.Enc : (={K,L}).
proof.
 app 2 2 ={j,g,K,L,m,r}; [trivial; auto | ].
 inline H; derandomize; wp.
 case{2} : in_dom((K[j], r), L).
 trivial.
 rnd (c_0{1} ^^ m{1}); trivial.
save.

equiv Real_Real' : Real.Main ~ Real'.Main : true ==> ={res}.
proof.
 auto; apply : KG(); trivial.
save.


equiv Fake_Fake'_Enc : Fake.Enc ~ Fake'.Enc : (={K,L}).
proof.
 app 2 2 ={j,g,K,L,r}; [trivial; auto | ].
 inline H; derandomize; trivial.
save.

equiv Fake_Fake' : Fake.Main ~ Fake'.Main : true ==> ={res}.
proof.
 auto; apply : KG(); trivial.
save.


(* 
** Need to use a lazy-sampling argument: 
** Resample the queries made by the plaintext constructor g  
*)
equiv Real'_Hybrid_H : Real'.H ~ Hybrid.H : 

 upto (bad)
 with 
  (={K,X,bad} &&
   (forall (k:key,r:random), 
     in_dom((k,r), L{1}) = (in_dom((k,r), L{2}) || mem((k,r), X{2}))) &&
   (forall (k:key,r:random), 
     in_dom((k,r), L{2}) => in_dom((k,r), L{1}) && L{1}[(k,r)] = L{2}[(k,r)])).
proof.
  admit.
save.
