(* This type matches the CAO mod[n] type *)

type modN = int * int.

op [+] : (modN,modN) -> modN as add_modN.
op [*] : (modN,modN) -> modN as mul_modN.
op [^] : (modN,int) -> modN as exp_modN.
op inv_modN : modN -> modN.

op int2modN : (int,int) -> modN.
op modN2int : modN -> int.

(* We need a hash function mapping {0,1}^* to {0,1}^hBits *)
(* We use polymorphism (over bit strings) for the domain *)
cnst hBits : int. 
op hash : 'a -> bitstring{hBits}.

(* Various lengths *)
cnst nLen : int.                          (* Size of modulus in octets *)
cnst nBits : int = nLen * 8.              (* Bit length of modulus octet representation *)
cnst dbBits : int  = nBits - hBits - 8.   (* EM = 0x00 || Masked Seed || Masked DB *)
cnst msgBits : int = dbBits - hBits - 8.  (* DB = lHash || PS || 0x01 || M *)
                                          (* We will assume PS is empty *)
cnst TBits : int. (* Smallest multiple of hBits >= dbBits *)

axiom allPositive : nLen > 0 && nBits > 0 && dbBits > 0 && msgBits > 0 && hBits > 0.

axiom TBits_value : exists (k : int), k > 0 && k*hBits >= dbBits && 
                    forall (k' : int), k' < k => k*hBits < dbBits.

(* We introduce the fancy CAO range set/get operators *)
(* Integer parameters indicate starting position and length *)
op rangeSet : ('a,int,int,'b) -> 'a.
op rangeGet : ('a,int,int) -> 'b.

(* We need the cast operations of CAO as well *)
op int2bitstring : int -> 'a. 
op bitstring2int : 'a -> int.

(* Free variables for quantification of the correctness definition. *)
cnst mFree : bitstring{msgBits}.
cnst seedFree : bitstring{hBits}.
cnst lHashFree : bitstring{hBits}.

(* The RSA parameter generator *)
pop RSAGen : () -> int * int * int.

op valid_keys : (int, int, int) -> bool.

axiom validkeys() : 
  a=RSAGen() ~ b = RSAGen() : true ==> a=b && (forall (n : int, e : int, d : int),
                            (n,e,d) = a => valid_keys(n,e,d)).

game Trivial = { fun Main() : bool = { return true; } }.

game RSA_OAEP_Correctness = {

fun RSAFun(e : int, n : int, msg : int) : int = {
  var c : modN;
  c = int2modN(msg,n)^e;
  return modN2int(c);
}

fun RSAInv(d : int, n : int, c : int) : int = {
  var msg : modN;
  msg = (c,n)^d;
  return modN2int(msg);
}

fun H(maskedDB : bitstring{dbBits}) : bitstring{hBits} = {
  var hashin : bitstring{dbBits + 32};
  var hashout : bitstring{hBits};
  var C : bitstring{32};
  hashin = rangeSet(hashin,32,dbBits,maskedDB);
  C = int2bitstring(0);
  hashin = rangeSet(hashin,0,32,C);
  hashout = hash(hashin);
  return hashout;
}

fun G(seed : bitstring{hBits}) :  bitstring{dbBits} = {
  var mask : bitstring{dbBits};
  var hashin : bitstring{hBits + 32};
  var hashout : bitstring{hBits};
  var C : bitstring{32};
  var T : bitstring{TBits};
  var counter : int = 0;
  var pos : int;
  hashin = rangeSet(hashin,32,hBits,seed);
  pos = TBits - hBits;
  while (pos >= 0) {
    C = int2bitstring(counter);
    hashin = rangeSet(hashin,0,32,C);
    hashout = hash(hashin);
    T = rangeSet(T,pos,hBits,hashout);
    counter = counter + 1;
    pos = pos - hBits;
  }
  mask = rangeGet(T,TBits-dbBits,dbBits);
  return mask;
}

fun Enc(e : int, n : int, msg : bitstring{msgBits}, lHash : bitstring{hBits}, seed : bitstring{hBits}) : int = {
  var c : int;
  var DB, dbMask, maskedDB : bitstring{dbBits};
  var seedMask, maskedSeed : bitstring{hBits};
  var payload : bitstring{nBits};
  var m : int;
  var byte0 : bitstring{8} = int2bitstring(0);
  var byte1 : bitstring{8} = int2bitstring(1);

  DB = rangeSet(DB,0,msgBits,msg);
  DB = rangeSet(DB,msgBits,8,byte1);
  DB = rangeSet(DB,msgBits + 8,hBits,lHash);
  dbMask = G(seed);
  maskedDB = DB ^^ dbMask;
  seedMask = H(maskedDB);
  maskedSeed = seed ^^ seedMask;
  payload = rangeSet(payload, 0, dbBits, maskedDB);
  payload = rangeSet(payload, dbBits, hBits, maskedSeed);
  payload = rangeSet(payload, dbBits + hBits, 8, byte0);
  m = bitstring2int(payload);
  c = RSAFun(e, n, m);
  return c;
}

fun Dec(d : int, n : int, c : int, lHash : bitstring{hBits}) : bool * bitstring{msgBits} = {
  var DB, dbMask, maskedDB : bitstring{dbBits};
  var seedMask, maskedSeed, lHash2,seed : bitstring{hBits};
  var payload : bitstring{nBits};
  var m : int;
  var msg : bitstring{msgBits};
  var result, result1, result2,result3 : bool;
  var err_msg : bitstring{msgBits} = int2bitstring(0);
  var byte0 : bitstring{8} = int2bitstring(0);
  var byte1 : bitstring{8} = int2bitstring(1);

  if (c < 0 || c > n-1) { result = false; }
  else {
     m = RSAInv(d, n, c);
     payload = int2bitstring(m);
     maskedDB = rangeGet(payload,0,dbBits);
     maskedSeed = rangeGet(payload,dbBits,hBits);
     seedMask = H(maskedDB);
     seed = maskedSeed ^^ seedMask;
     dbMask = G(seed);
     DB = maskedDB ^^ dbMask;
     lHash2 = rangeGet(DB,msgBits + 8,hBits);
     result1 = (rangeGet(payload,dbBits+hBits,8) = byte0);
     result2 = (lHash = lHash2);
     result3 = (rangeGet(DB,msgBits, 8) = byte1);
     result = result1 && result2 && result3;
  }
  if (result) { msg = rangeGet(DB,0,msgBits); }
  else { msg = rangeGet(err_msg,0,msgBits); }
  return (result, msg);
}

fun Main() : bool = {
   var n : int;
   var e : int;
   var d : int;
   var c :  int;
   var rec : bitstring{msgBits};
   var err : bool;
   var prms : int * int * int;

  prms = RSAGen();
  (n,e,d) = prms;
  c = Enc(e, n, mFree, lHashFree, seedFree);
  (err,rec) = Dec(d, n, c, lHashFree);
  return (err && mFree = rec);
}
}.

equiv correctness : RSA_OAEP_Correctness.Main ~ Trivial.Main : true ==> ={res}.
