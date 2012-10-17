type key.
type plaintext.
type ciphertext.

pop gen : () -> key.
pop enc : (key, plaintext) -> ciphertext.
op  dec : (key, ciphertext) -> plaintext.

aspec dec_spec(k:key,m:plaintext) : c = enc(k, m) : true ==> dec(k, c) = m.

game G = {
  var m : plaintext

  fun f() : plaintext ={
    var c : ciphertext;
    var k : key = gen();
    c = enc(k, m);
    return dec(k, c);
  }
 
  fun void() : unit = { }
}.

equiv test : G.f ~ G.void : true ==> res{1} = m{1}.
proof.
 apply{1}: dec_spec(k{1}, m{1}).
 trivial.
save.
