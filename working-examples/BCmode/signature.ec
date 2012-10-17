cnst n : int.
axiom n_pos : 0 <= n.
type block = bitstring{n}.  

type nonce = block.

op gen_nonce : (int, block) -> block. 
(* [gen_nonce(i,b)] generate a new nonce. [i] is a counter, it will be 
different for each call to [gen_nonce]. [b] is a random block *)

type skey. (* the type of the secret key used in the block cipher *)
type okey. (* the type of the other secret key potentially used to generate
              the secret *)
pop gen_skey : () -> skey.
pop gen_okey : () -> okey.
(* [gen_skey()] is a random operator generating a new [skey]
   [gen_okey()] is a random operator generating a new [okey] *)

type secret = block list. (* the type of the secrets used in the scheme *)

op init_global_secret : () -> secret.
cnst sg : int.
axiom sg_pos : 0 <= sg.
op gen_global_presecret : secret -> block.

op init_secret : (nonce, okey) -> secret.
cnst sl : int.      (* the number of call to F needed to generate the secret *)
axiom sl_pos : 0 <= sl.
op gen_presecret : (nonce, secret) -> block.


type intermediate = block list.

op gen : (nonce, secret, intermediate) -> block.
(* [gen(nc,s,inter)] build a new block [E_|inter|] *)

op oper : (block,block) -> block.
op F    : (skey, block) -> block.

(** How to instanciate this for the different schemes :
    forall schemes:
      skey and gen_skey and F can still abstract 

    - CBC:

      gen_nonce(i,r) = r
      okey = unit
      gen_okey() = ()
      init_secrect (nc,ok) = []  
      sl = 0
      gen_presecret (nc,sec) = bs0_n   (It is not important since sl = 0)
      gen(nc,sec) = gen(nc,sec,inter) = if inter = [] then nc else hd(inter)
      oper = ^^

    - IAPM:   

      gen_nonce(i,r) = r
      okey = skey
      gen_okey ()= gen_skey()
      init_secrect (nc,ok) = 
          W1 = F(ok,nc);
          W2 = F(ok,W1);
          W1, W2
      sl = 0
      gen_presecret (nc,sec) = bs0_n
      gen(nc,sec,inter) = 
         i = length(inter);
         W2 = nth(0,sec);
         W1 = nth(1,sec); 
         (W1 + W2 * i) mod p; 
      remark : we will need coercion from int to bitstring{n} and from bitstring{n} to int
      oper = ^^

    - OCB:
 
      gen_nonce(i,r) = i
      okey = unit
      gen_okey () = ()
      init_secrect (nc,ok) = []
      sl = 2
      gen_presecret (nc,sec) = 
         if length(sec) = 0 then bs0_n else nc ^^ hd(sec) 
      gen(nc,sec,inter) = 
         i = length(inter);
         R = nth(0,sec);
         L = nth(1,sec); 
         gamma_(length(inter)).L ^^ R
      oper = ^^

     - XECBc              
       gen_nonce(i,r) = r
       okey = unit
       gen_okey () = ()
       init_secrect (nc,ok) = []
       sl = 1
       gen_presecret (nc,sec) = nc
       gen(nc,sec,inter) = 
         i = length(inter);
         y = hd(sec);
         y.i mod p
       oper = modular addition modulo 2^n ?
*)




