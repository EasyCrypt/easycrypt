cnst l : int.

type key = bitstring{l}.
type message = bitstring{l}.
type ciphertext = bitstring{l}.

pop M : () -> message.

game OTP = {
 var m : message
 var c : ciphertext

 fun KG() : key = { var k : key = {0,1}^l; return k; }

 fun Enc(k:key, m':message) : ciphertext = { return (k ^^ m'); }

 fun Main() : unit = { var k : key; m = M(); k = KG(); c = Enc(k, m); }
}.

game Uniform = {
 var m : message
 var c : ciphertext
 
 fun Main() : unit = { m = M(); c = {0,1}^l; }
}.

equiv Secrecy : OTP.Main ~ Uniform.Main : true ==> (c,m){1} = (c,m){2}.
proof.
 inline KG, Enc; wp.
 rnd (c ^^ m{2}); trivial.
save.


type state.

adversary A1() : bitstring{l} * bitstring{l} * state {}.

adversary A2(s:state, c:bitstring{l}) : bool {}.

game INDCPA = {
 fun KG() : bitstring{l} = {
   var k : bitstring{l} = {0,1}^l;
   return k;
 }

 fun Enc(k:bitstring{l}, m:bitstring{l}) : bitstring{l} = {
   return (k ^^ m);
 }

 abs A1 = A1 {}
 abs A2 = A2 {}

 fun Main() : bool = {
   var s : state;
   var k, c, m0, m1 : bitstring{l};
   var b, b' : bool;
   k = KG();
   (m0,m1,s) = A1();
   b = {0,1};
   c = Enc(k, b ? m0 : m1);
   b' = A2(s,c);
   return (b = b');
 }
}.

game Independent = {
 abs A1 = A1 {}
 abs A2 = A2 {}

 fun Main() : bool = {
   var s : state;
   var c, m0, m1 : bitstring{l};
   var b, b' : bool;
   (m0,m1,s) = A1();
   c = {0,1}^l;
   b' = A2(s,c);
   b = {0,1};
   return (b = b');
 }
}.

prover "alt-ergo".

equiv PerfectSecrecy : INDCPA.Main ~ Independent.Main : true ==> ={res}.
proof.
 swap{1} 2; swap{2} -2.
 inline KG, Enc; call; wp.
 rnd (c ^^ (b ? m0 : m1){2}).
 rnd; call.
 trivial.
save.

claim Fact1 : Independent.Main[res] = 1%r/2%r 
compute.

claim Fact2 : INDCPA.Main[res] = Independent.Main[res] using PerfectSecrecy.

claim Conclusion : INDCPA.Main[res] = 1%r/2%r.
