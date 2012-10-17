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
 inline KG, Enc.
 rnd >>.
 rnd >> (c ^^ m{2}).
 trivial.
save.

