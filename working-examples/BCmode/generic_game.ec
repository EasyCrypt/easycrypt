
type keys = skey * okey.
type message = block array.
type cipher = nonce * block array.

(** - q is the maximum number of encryption 
    - sigma is the sum of the messages length
    - sl is the number of block cipher call needed 
      to generate the local secret of one encryption
    - sg is the number of block cipher call needed 
      to generate the global secret of the encryption
    - max_call is the maximun number of call to the block cipher 
      during the game
*)

cnst q : int.
axiom q_pos : 0 <= q.

cnst sigma : int.
axiom sigma_pos : 0 <= sigma.

cnst max_call : int = sg + sigma + q*sl.
axiom max_call_pos : 0 < max_call.

lemma qsl_pos : 0 <= q * sl.

(** We use the definition of CPA where the adversary has access 
    to an LR oracle and can make more than one query *)

adversary A()  : bool { (message,message) -> cipher }.

game CPA = {
  var global_secret : secret

  (* key generation *)
  fun KG () : keys = {
    var kg_sk : skey = gen_skey();
    var kg_ok : okey = gen_okey();
    return (kg_sk, kg_ok);
  }

  var p : int (* The number of encrypted messages *)

  fun Enc(Ke:keys, m:message) : cipher = {
    var nc, rnc:nonce;
    var ok : okey;
    var sk : skey; 
    var sec : secret;
    var c : block array = make(length(m), bs0_n);
    var E,X,C : block;
    var inter : block list = [];
    var j,k : int = 0;
    var aux : block;

    (sk,ok) = Ke;
    (* Initialization of the nonce *)
    rnc = {0,1}^n;
    nc = gen_nonce(p,rnc);
    (* Initialization of the secret *)
    sec = init_secret (nc, ok) ++ global_secret;
    while (k < sl) {
      aux = gen_presecret(nc,sec);
      sec = F(sk,aux) :: sec;
      k = k + 1;
    }
    while (j < length(m)) {
      E = gen(nc,sec, inter);
      X = oper(E,m~>(j));
      C = F(sk,X);
      inter = C :: inter;
      c = c <~(j,C);
      j = j + 1;
    }
    p = p + 1;
    return (nc, c);
  }
 
  var b : bool
  var K : keys
  var count : int

  fun LR(m0,m1:message) : cipher = {
    var cb : cipher;
    if (length(m0) = length(m1) && p < q && count + length(m0) <= sigma) {
      cb = Enc(K, b ? m0 : m1);
      count = count + length(m0);
    } else {
      cb = (bs0_n,make(0,bs0_n));
    }
    return cb;
  }
  
  (* Declaration of the adversary *)

  abs A = A {LR}

  (* The main game *)

  fun Main () : bool = {
    var b' : bool;
    var k : int;
    var aux : block;
    var sk:skey;
    var ok:okey;

    K = KG();
    (sk,ok) = K;
    b = {0,1};
    p = 0; count = 0;
    (* Initialization of the secret *)
    global_secret = init_global_secret ();
    k = 0;
    while (k < sg) {
      aux = gen_global_presecret(global_secret);
      global_secret = F(sk,aux) :: global_secret;
      k = k + 1;
    }
    (* Call to the adversary *)
    b' = A ();
    return b = b';
  } 
}.

game PRP0 = {
  var SK : skey (* Should not be used by the adversary *)
  var LB : block list

  fun BC (bl:block) : block = {
    var be : block;
    if (length(LB) < max_call) {
      be = F(SK,bl);
      LB = be :: LB;
    } else {
      be = bs0_n;
    }
    return be;
  }

  (** Definition of the adversary B *)
  var global_secret : secret
  var p : int 
  var b : bool
  var OK : okey
  var count : int

  fun LR(m0,m1:message) : cipher = {
    var cb : cipher;
    var nc, rnc:nonce;
    var sec : secret;
    var Mp : message;
    var c : block array;
    var E,X,C,aux,aux' : block;
    var inter : block list;
    var j,k : int;

    if (length(m0) = length(m1) && p < q && count + length(m0) <= sigma) {
      Mp = b ? m0 : m1;
      c = make(length(m0), bs0_n);
      inter = [];
      j = 0;
      k = 0;
      rnc = {0,1}^n;
      nc = gen_nonce(p,rnc);
      sec = init_secret (nc, OK) ++ global_secret;
      while (k < sl) {
        aux = gen_presecret(nc,sec);
        aux' = BC(aux);
        sec = aux' :: sec;
        k = k + 1;
      }
      while (j < length(m0)) {
        E = gen(nc,sec, inter);
        X = oper(E,Mp~>(j));
        C = BC(X);
        inter = C :: inter;
        c = c <~(j,C);
        j = j + 1;
      }
      p = p + 1;
      cb = (nc, c);      
      count = count + length(m0);
    } else {
      cb = (bs0_n,make(0,bs0_n));
    }
    return cb;
  }  
 
  abs A = A {LR}
 
  fun B () : bool = {
    var b' : bool;
    var k : int;
    var aux,aux' : block;
    b = {0,1};
    OK = gen_okey ();
    p = 0; count = 0;
    (* Initialization of the secret *)
    global_secret = init_global_secret ();
    k = 0;
    while (k < sg) {
      aux = gen_global_presecret(global_secret);
      aux' = BC(aux);
      global_secret = aux' :: global_secret;
      k = k + 1;
    }
    b' = A ();
    return b = b';
  }

  (* The main game of PRF *)

  fun Main () : bool = {
    var d : bool;
    SK =  gen_skey();
    LB = [];
    d = B ();
    return d;
  } 
}.

game PRP1 = PRP0 
   remove SK
   var BCm : (block,block) map
   var bad_prp : bool

   where BC = {
     var be, be_LB: block;
     be = {0,1}^n;
     be_LB = ({0,1}^n \ LB);
     if (length(LB) < max_call) {
       if (!in_dom(bl,BCm)) { 
         if (mem(be,LB)) { bad_prp = true; be = be_LB; }
         BCm[bl] = be;
       } else { 
         be = BCm[bl]; 
       }
       LB = be :: LB;
     } else {
       be = bs0_n;
     }
     return be;
   }
   and Main = {
     var d : bool;
     BCm = empty_map;
     LB = [];
     bad_prp = false;
     d = B ();
     return d;
   }.

game G2 = {
  var global_secret : secret
  var p,count : int
  var b,bad : bool
  var OK : okey
  var BCm : (block,block)map
  var LB : block list

  fun LR(m0, m1 : message) : cipher = {
    var cb : cipher;
    var nc, rnc:nonce;
    var sec : secret;
    var Mp : message;
    var c : block array;
    var E,X,C,aux,aux' : block;
    var inter : block list;
    var j,k : int;

    if (length(m0) = length(m1) && p < q && count + length(m0) <= sigma) {
      Mp = b ? m0 : m1;
      c = make(length(m0), bs0_n);
      inter = [];
      j = 0; k = 0;
      rnc = {0,1}^n;
      nc = gen_nonce(p,rnc);
      sec = init_secret (nc, OK) ++ global_secret;
      while (k < sl) {
        aux = gen_presecret(nc,sec);
        bad = bad || mem(aux,LB);
        LB = aux::LB;
        aux' = {0,1}^n;
        sec = aux' :: sec;
        k = k + 1;
      }
      while (j < length(m0)) {
        E = gen(nc,sec, inter);
        X = oper(E,Mp~>(j));
        bad = bad || (mem(X,LB));
        LB=X::LB;
        C = {0,1}^n;
        inter = C :: inter;
        c = c <~(j,C);
        j = j + 1;
      }
      p = p + 1;
      cb = (nc, c);      
      count = count + length(m0);
    } else {
      cb = (bs0_n,make(0,bs0_n));
    }
    return cb;
  }  

  abs A = A{LR}

  fun Main () : bool = {
    var b' : bool;
    var k : int;
    var aux,aux' : block;
    bad = false;
    BCm = empty_map;
    LB = [];
    b = {0,1};
    OK = gen_okey ();
    p = 0; count = 0;
    global_secret = init_global_secret ();
    k = 0;
    while (k < sg)
    {
      aux = gen_global_presecret (global_secret);
      if (!in_dom(aux,BCm)) {
        BCm[aux] = {0,1}^n;
        LB = aux :: LB;
      }
      global_secret = BCm[aux] :: global_secret;
      k = k + 1;
    }
    b' = A ();
    return b = b';
  }
}.
