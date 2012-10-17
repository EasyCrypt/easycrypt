type group
type ogroup
type session

cnst q : int
cnst g : group
cnst k : int
cnst qG : int // maximal number of G queries
cnst qH : int // maximal number of H queries
cnst qS : int // maximal number of signatures
cnst qP : int // maximal number of participants
cnst qIR : int // maximal number of initiated and responded sessions
cnst bottom : bitstring{k}

type secret_key = int
type public_key = group
type key        = secret_key * public_key
type message    = bitstring{k}
type part 	= int
type group_pair = group * group
type session_num_and_partner = int * part 
type session_init            = session_num_and_partner * group
type session_complete        = session_init * group
type session_list            = session list
type session_complete_with_status = session_complete * bool // tested or corrupted

op (*) : group, group -> group    = group_mult
op (^) : group, int -> group      = group_pow
op dlg : group -> int             = dlg
op nth : group list, int -> group = nth
op inl : session_init -> session  = inl
op inr : session_complete_with_status -> session = inr
op session_complete      : session_list, part, group, group -> session_list = scu
op session_status_update : session_list, part, group, group -> session_list = su
op session_test          : session_list, part, group, group -> bool         = st

axiom session_test_true: 
 forall (sl: session_list, A:part, X: group, Y:group). 
  { session_test(sl,A,X,Y) == true}

axiom session_status_update_id: 
 forall (sl: session_list, A:part, X: group, Y:group). 
  { session_status_update (sl,A,X,Y) == sl}

/*
 [session_complete] takes a session list, a participant B, two group
 elements X and Y and a boolean b and looks for the first session of
 the form inl(i,B,X) and modifies it to inr((i,B,X,Y),false) 
 
 [session_status_update] takes a session list, a participant B, two
 group elements X and Y and a boolean b and looks for the first
 session of the form inl(i,B,X,Y, true) and modifies it to
 inr(i,B,X,Y,false)

 [session_test] takes a session list, a participant B, two group
 elements X and Y and a boolean b and returns false if there is a
 session of the form inr((i,B,X,Y),false) 
*/


adversary A1(pK:(part,public_key) map) : part * part * group * group
 { 
   group, group -> int;
   group -> message; 
   part, part -> group;
   part, part, group -> group;
   part, part, group, group -> unit;
   part, part, group, group -> bitstring{k};
   part -> int
 }

adversary A2(pK:(part,public_key) map, w:bitstring{k}) : bool 
 { 
   group, group -> int;
   group -> message; 
   part, part -> group;
   part, part, group -> group;
   part, part, group, group -> unit;
   part, part, group, group -> bitstring{k};
   part -> int
 };;


game HMQV = {
 var ni, nr, ns, np, nsig : int
 var b : bool
 var s : group
 var sessions : (part, session list) map
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var LH       : (group, bitstring{k}) map
 var DA       : group list
 var LG       : (group_pair, int) map
 var DG       : group_pair list

 fun KG() : unit = {
  var sk : int = [0..q-1];
  pkey = empty_map();
  skey = empty_map();
  ns = ns + 1;
  skey[ns] = sk;
  pkey[ns] = g ^ sk;
  corrupt[ns] = false;
  return;
 } 

 fun G(x:group, pk:public_key) : int = {
  var i : int = [0..q]; 
  if (length(DG) < qG && !in_dom((x,pk), LG)) { 
   LG[(x,pk)] = i; 
   DG = (x,pk) :: DG; 
  };
  return LG[(x,pk)];
 }

 fun H(lam:group) : bitstring{k} = {
  var h : bitstring{k} = {0,1}^k;
  if (!in_dom(lam, LH)) { LH[lam] = h; };
  return LH[lam];
 }

 fun H_adv(lam:group) : bitstring{k} = {
  var msg : bitstring{k};
  if (length(DA) < qH) { 
   DA = lam :: DA;
   msg = H(lam);
  } 
  else { msg = bottom; }  
  return msg;
 }

 fun Dsig(sk:secret_key, pk:public_key, esk:secret_key, ge:group) : group = {  
  var c, d : int;
  nsig = nsig + 1;
/*
  c = G(ge, g ^ sk);
  d = G(g ^ esk, pk);
  return (pk ^ c * ge) ^ (esk + d * sk);
*/
  return pk;
 }

 fun Init(A:part, B:part) : group = {
  var x : int = [1..q];
  sessions[A] = inl(((ni,B), g ^ x)) :: sessions[A];
  ni = ni + 1 ; 
  return (g ^ x);
 }

 fun Respond(B:part, A:part, X: group) : group = {
  var y : int = [1..q];
  var Y : group;
  Y = g ^ y;
  sessions[B] = inr(((((nr,A),X),Y),false)) :: sessions[B];
  nr = nr + 1;
  return Y;
 }

 fun Complete(A:part, B:part, X:group, Y:group) : unit = {
  sessions[A] = session_complete(sessions[A],B,X,Y);
  return;
 }

 fun Test(A:part, B:part, X: group, Y: group) : bitstring{k} = { 
  var w : bitstring{k} = {0,1}^k;
  sessions[A] = session_status_update(sessions[A],B,X,Y);
  sessions[B] = session_status_update(sessions[B],A,X,Y);
  if (b && !(A == B) && (!corrupt[A]) && (!corrupt[B]) && 
      session_test(sessions[A],B,X,Y) && session_test(sessions[B],A,X,Y) ) {
   s = Dsig(skey[A],pkey[B],dlg(X),Y); 
   w = H(s);
  }; 
  return w;
 }

 fun KeyReveal(A:part, B:part, X:group, Y:group) : bitstring{k} = {
  var w : bitstring{k};
  var ss : group;
  sessions[A] = session_status_update(sessions[A],B,X,Y);
  sessions[B] = session_status_update(sessions[B],A,X,Y);
  if (session_test(sessions[A],B,X,Y) && session_test(sessions[B],A,X,Y)) {
   ss = Dsig(skey[A],pkey[B],dlg(X),Y); 
   w = H_adv(ss);
  }
  else { w = {0,1}^k; }
  return w;
 }  	    
  
 fun Corrupt(A: part) : int = { 
  corrupt[A] = true;
  return skey[A];
 }

 abs A1 = A1 {G, H_adv, Init, Respond, Complete, KeyReveal, Corrupt}
 abs A2 = A2 {G, H_adv, Init, Respond, Complete, KeyReveal, Corrupt}
  
 fun Main () : bool = {
  var w : bitstring{k};
  var ABXY : part * part * group * group;
  var A, B : part;
  var X, Y : group;
  var b' : bool;
  var tt : unit;
  ni = 0; 
  nr = 0; 
  ns = 0; 
  np = 0;
  nsig = 0; 
  LH = empty_map();
  DA = [];
  DG = [];
  LG = empty_map();
  sessions = empty_map();
  corrupt = empty_map();
  tt = KG();
  b = {0,1};
  ABXY = A1(pkey);
  A = fst(fst(fst(ABXY)));
  B = snd(fst(fst(ABXY)));
  X = snd(fst(ABXY));
  Y = snd(ABXY);
  w = Test(A, B, X, Y); 
  b' = A2(pkey, w);
  return (b == b');
 }
};;


claim Pr0 : HMQV.Main[res] == 
            HMQV.Main[res && in_dom(s,LH)] + HMQV.Main[res && !in_dom(s,LH)] 
 split;;


claim Pr1 : HMQV.Main[res && in_dom(s,LH)] <= HMQV.Main[in_dom(s,LH)] 
 same;;

claim Pr2 : HMQV.Main[res] <= 
            HMQV.Main[in_dom(s,LH)] + HMQV.Main[res && !in_dom(s,LH)]


/* Inline Test in Main */
game HMQV0 = HMQV
 where Main = {
  var logz : int = [1..q];
  var w : bitstring{k};
  var ABXY : part * part * group * group;
  var A, B : part;
  var X, Y : group;
  var b' : bool;
  var tt : unit;
  ni = 0; 
  nr = 0; 
  ns = 0; 
  np = 0;
  nsig = 0; 
  LH = empty_map();
  DA = [];
  DG = [];
  LG = empty_map();
  sessions = empty_map();
  corrupt = empty_map();
  tt = KG();
  b = {0,1};
  ABXY = A1(pkey);
  A = fst(fst(fst(ABXY)));
  B = snd(fst(fst(ABXY)));
  X = snd(fst(ABXY));
  Y = snd(ABXY);
  sessions[A] = session_status_update(sessions[A],B,X,Y);
  sessions[B] = session_status_update(sessions[B],A,X,Y);
  w = {0,1}^k;
  if ( b && ! (A == B) && (! corrupt[A]) && (! corrupt[B]) && 
       session_test(sessions[A],B,X,Y) && session_test(sessions[B],A,X,Y) ) {
   s = Dsig(skey[A],pkey[B],dlg(X),Y); 
   w = H(s);
  }; 
  b' = A2(pkey, w);
  return (b == b');
}

/*
equiv Fact1 : HMQV.Main ~ HMQV0.Main : {true} ==> ={res}
 inline;;
 derandomize;;
 auto;;
 repeat rnd;;
 trivial;;
save;;
*/

/* Fix value of H(z), apply fundamental lemma */
/* Which z? 
   If it refers to g^logz, then the games don't satisfy the hypotheses of the FL
   If it refers to s = Dsig(....), it is not known in advance, cannot be fixed
*/
game HMQV1 = HMQV
 where Main = {
  var w : bitstring{k};
  var ABXY : part * part * group * group;
  var A, B : part;
  var X, Y : group;
  var b' : bool;
  var tt : unit;
  ni = 0; 
  nr = 0; 
  ns = 0; 
  np = 0;
  nsig = 0; 
  LH = empty_map();
  DA = [];
  DG = [];
  LG = empty_map();
  sessions = empty_map();
  corrupt = empty_map();
  tt = KG();
  b = {0,1};
  ABXY = A1(pkey);
  A = fst(fst(fst(ABXY)));
  B = snd(fst(fst(ABXY)));
  X = snd(fst(ABXY));
  Y = snd(ABXY);
  w = {0,1}^k;  
  sessions[A] = session_status_update(sessions[A],B,X,Y);
  sessions[B] = session_status_update(sessions[B],A,X,Y);
  if ( b && ! (A == B) && (! corrupt[A]) && (! corrupt[B]) && 
       session_test(sessions[A],B,X,Y) && session_test(sessions[B],A,X,Y) ) {
   s = Dsig(skey[A],pkey[B],dlg(X),Y); 
  }; 
  b' = A2(pkey, w);
  return (b == b');
}

prover "alt-ergo";;

equiv auto HMQV0_HMQV1_A1 : HMQV0.A1 ~ HMQV1.A1 :
 ={ni, nr, ns, np, nsig, b, sessions, corrupt, pkey, skey, DA, LH, DG, LG} /\ 
 ({(in_dom(z,LH)){1}} => {(in(z,DA)){1}});;

prover simplify;;

equiv Fact2 : HMQV0.Main ~ HMQV1.Main :
 {true} ==>
 { (in(z,DA)){1} == (in(z,DA)){2} } /\
 ({ (!in(z,DA)){1} } => ={res} );;
 inline;;
 derandomize;;
 auto inv
 upto {in(z,DA)}
 with
  (forall (ww:group). {!(ww == z{1})} => 
   {LH{1}[ww] == LH{2}[ww]} /\
   {in_dom(ww,LH{1}) == in_dom(ww,LH{2})}) /\
   ={ni, nr, ns, np, nsig, b, z, sessions, corrupt, pkey, skey, DA, DG, LG}
 using HMQV0_HMQV1_A1;;
 rnd {1};;
 repeat rnd;; trivial;;
save;;

claim Pr3 : | HMQV0.Main[res] - HMQV1.Main[res] | <= HMQV1.Main[in(z,DA)]
 using Fact2;;


/* Game2: Test and Reveal return session string instead of its hash,
 adversary must also return session string */

game HMQV2 = {
 var b, b' : bool
 var m, n : int
 var z : group
 var ss : group
 var sessions : (part, session list) map
 var corrupt    : (part, bool) map
 var pkey       : (part, public_key) map
 var skey       : (part, secret_key) map
 var LH         : (group, bitstring{k}) map
 var DH         : group list
 var LG         : (group_pair, int) map
 var DG         : group_pair list


 /* forall A:part do {var x : int = [0..q-1]; K[A] = (x,g ^ x); pK[A]=g^x}; */
 fun KG() : (part, public_key) map = {
  var xa : int = [0..q-1];
  var xb : int = [0..q-1];
  var xm : int = [0..q-1];
  
  pkey = empty_map();
  skey = empty_map();

  skey[alice] = xa; 
  pkey[alice] = g ^ xa;
 
  skey[bob] = xb; 
  pkey[bob] = g ^ xb;
  
  skey[mallory] = xm; 
  pkey[mallory] = g ^ xm;

  corrupt[alice]   = false;
  corrupt[bob]     = false;
  corrupt[mallory] = false;

  return pkey;
 } 

 fun G(x:group, pk:public_key) : int = {
   var i : int = [0..q];
   if (length(DG) < qG && !in_dom((x,pk), LG)) { 
    LG[(x,pk)] = i; 
    DG = (x,pk) :: DG; 
   };
   return LG[(x,pk)];
 }

 fun H(lam:group) : bitstring{k} = {
   var h : bitstring{k} = {0,1}^k;
   if (length(DH) < qH && !in_dom(lam, LH)) { LH[lam] = h; DH = lam :: DH; };
   return LH[lam];
 }

 fun Dsig(sk:secret_key, pk:public_key, esk:secret_key, ge:group) : group = {  
  var c, d : int;
  c = G(ge, g ^ sk);
  d = G(g ^ esk, pk);
  return (pk ^ c * ge) ^ (esk + d * sk);
 }

 fun Init(A:part, B:part) : group = {
  var x : int = [1..q];
  if (! (A == B))  {
   sessions[A] = inl(((n,B), g ^ x)) :: sessions[A];
   n = n + 1 ; 
  };
  return (g ^ x);
 }

 fun Respond(B:part, A:part, X: group) : group = {
  var y : int = [1..q];
  var Y : group = g;
  if (!(A == B)) {
    Y = g ^ y;
    sessions[B] = inr(((((m,A),X),Y),false)) :: sessions[B];
    m = m + 1;
  };
  return Y;
 }

 fun Complete(A:part, B:part, X:group, Y:group) : unit = {
  sessions[A] = session_complete(sessions[A],B,X,Y);
  return;
 }

 fun Test(A:part, B:part, X: group, Y: group) : unit = {
  if (b && (! corrupt[A]) && (! corrupt[B]) && 
      session_test(sessions[A],B,X,Y) &&
      session_test(sessions[B],A,X,Y)) {
   sessions[A] = session_status_update(sessions[A],B,X,Y);
   sessions[B] = session_status_update(sessions[B],A,X,Y);
  };
  return;
 }

 fun KeyReveal(A:part, B:part, X:group, Y:group) : group = {
  var sig : group;
  if (session_test(sessions[A],B,X,Y) &&
      session_test(sessions[B],A,X,Y)) {
   sessions[A] = session_status_update(sessions[A],B,X,Y);
   sessions[B] = session_status_update(sessions[B],A,X,Y);
   sig = Dsig(skey[A],pkey[B],dlg(X),Y); 
  };
  return sig;
 }  	  
  
 fun Corrupt(A: part) : int = { 
  corrupt[A] = true;
  return skey[A];
 }

 fun Test_A(A:part, B:part, X: group, Y: group) : bitstring{k} = {
  var zlog : int = [0..q-1];
  var w : bitstring{k};
  w = H(g ^ zlog);
  return w;
 }

 fun KeyReveal_A(A:part, B:part, X:group, Y:group) : bitstring{k} = {
  var w : bitstring{k};
  var zz : group;
  zz = KeyReveal(A, B, X, Y);
  w = H(zz);
  return w;
 }

 abs A1 = A1 {G, H, Init, Respond, Complete, KeyReveal_A, Corrupt}
 abs A2 = A2 {G, H, Init, Respond, Complete, KeyReveal_A, Corrupt}

 fun B(pkey':(part, public_key) map): group = {
  var index : int;
  var w : bitstring{k};
  var ABXY : part * part * group * group;
  ABXY = A1(pkey');
  w = Test_A(fst(fst(fst(ABXY))), snd(fst(fst(ABXY))), snd(fst(ABXY)), snd(ABXY)); 
  b' = A2(pkey', w);
  index = [0..qH-1];
  return nth(DH, index);
 }

 fun Main() : bool = {
  var logz : int = [1..q];
  m = 0; 
  n = 0; 
  DH = [];
  LH = empty_map();
  DG = [];
  LG = empty_map();
  sessions = empty_map();
  corrupt = empty_map();
  z = g ^ logz;
  pkey = KG();
  b = {0,1};
  ss = B(pkey);
  return (ss == z);
 }
}


prover "alt-ergo";;

equiv HMQV_HMQV1 : HMQV.Main ~ HMQV1.Main :
 {true} ==>
 { !b{1} && in_dom(z{1},LH{1}) } => { in_dom(z{2},LH{2}) }
inline{2} B;
wp;;

app 12 13 (={logz,n,m,LG,LH,DG,DH,z,skey,pkey,b,sessions,corrupt} /\ 
 { pkey'{2} == pkey{1} });;
inline KG;
derandomize;;
wp;;
repeat rnd;;
trivial;;

rnd {2};;

app 1 1 (={logz,n,m,LG,LH,DG,DH,z,skey,pkey,b,sessions,corrupt}
         /\ { pkey'{2} == pkey{1} });;
auto inv 
 (={n,m,DH,LH,LG,DG,z,pkey,b,sessions,corrupt,skey} );;

save;;


claim Pr3 : HMQV.Main[res] <= HMQV1.Main[res] * (1%r / qH%r)

claim Pr3 : HMQV.Main[in_dom(z,LH)] <= HMQV1.Main[res] * (1%r / qH%r)
