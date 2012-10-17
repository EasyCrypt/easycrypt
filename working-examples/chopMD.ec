cnst bl : int    /* block length */
cnst hl : int    /* hash length */
cnst sl : int    /* state length */

type block  = bitstring{bl}
type msg    = bool list
type padmsg = block list
type state  = bitstring{sl}
type hash   = bitstring{hl}

cnst IV : state

op f     : state, block  -> state = f
op g'     : state -> hash = g'
op fstar : state, padmsg -> state = fstar
op chopMD    : msg -> hash = chopMD
op pad   : msg -> padmsg = pad

type farg = state * block
op fstarlast : state, padmsg -> farg = fstarlast
op fstarfind : state, padmsg, state, padmsg -> farg * farg = fstarfind

axiom fstar_def_1 :
  forall (h:state).
  { fstar(h, []) == h }

axiom fstar_def_2 :
  forall (h:state, m:block, M:block list).
  { fstar(h, m::M) == fstar(f(h, m), M) }

axiom chopMD_def :
  forall (M:msg).
  { chopMD(M) == g'(fstar(IV, pad(M))) }

axiom pad_inj :
  forall (m : msg, m' : msg).
  { pad(m) == pad(m') } =>  { m == m' }

axiom fstarlast_def_1 :
  forall (h:state, m:block).
  { fstarlast(h, m::[]) == (h, m) }

axiom fstarlast_def_2 :
  forall (h:state, m1:block, m2:block, M:block list).
  { fstarlast(h, m1::m2::M) == fstarlast(f(h, m1), m2::M) }

axiom fstarfind_def_1 :
  forall (h1:state, m1:block, h2:state, m2:block).
  { fstarfind(h1, m1::[], h2, m2::[]) == ((h1, m1), (h2, m2)) }

axiom fstarfind_def_2 :
  forall (h1:state, m1:block, m1':block, M1:block list, h2:state, m2:block, m2':block, M2:block list).
  {f(h1,m1) == f(h2,m2)} => { fstarfind(h1, m1::m1'::M1, h2, m2::m2'::M2) == ((h1,m1),(h2,m2)) }

axiom fstarfind_def_3 :
  forall (h1:state, m1:block, m1':block, M1:block list, h2:state, m2:block, m2':block, M2:block list).
  {!(f(h1,m1) == f(h2,m2))} => { fstarfind(h1, m1::m1'::M1, h2, m2::m2'::M2) == fstarfind(f(h1, m1), m1'::M1, f(h2, m2), m2'::M2) }

axiom fstarfind_prop :
  forall (m1:padmsg, m2:padmsg, c1:farg, c2:farg).
  { (fstar(IV,m1) == fstar(IV,m2)) && !(m1 == m2) && (length(m1) == length(m2)) && ((c1,c2) == fstarfind(IV,m1,IV,m2))} 
  => {(f(fst(c1),snd(c1)) == f(fst(c2),snd(c2))) && !(c1 == c2)}

axiom fstarlast_prop :
  forall (m1:msg, m2:msg, c1:farg, c2:farg).
  {(fstar(IV,pad(m1)) == fstar(IV,pad(m2))) && !(length(m1) == length(m2)) && (c1 == fstarlast(IV,pad(m1))) && (c2 == fstarlast(IV,pad(m2)))} 
  => {(f(fst(c1),snd(c1)) == f(fst(c2),snd(c2))) && !(c1 == c2)}

adversary A () : msg * msg {msg -> hash}

game chopMD_coll = {
  fun O_F(m:msg) : hash = {
    return chopMD(m);
  }

  abs A = A {O_F}

  fun Main () : bool = {
    var m, m' : msg;  

    (m, m') = A();
    return (chopMD(m) == chopMD(m') && !(m == m'));
  }
}

game chopMD_inline = {
  fun O_fstar(m:padmsg) : state = {
    return fstar(IV, m);
  }

  fun O_F(m:msg) : hash = {
    var pm : padmsg;
    var s : state;
    var h : hash;
    pm = pad(m);
    s = O_fstar(pm);
    h = g'(s);
    return h;
  }

  abs A = A {O_F}

  fun Main () : msg*msg = {
    var m, m' : msg;  

    (m, m') = A();
    return (m, m');
  }
}

game g'_coll = {
  fun O_fstar(m:padmsg) : state = {
    return fstar(IV, m);
  }

  fun O_F(m:msg) : hash = {
    var pm : padmsg;
    var s : state;
    var h : hash;
    pm = pad(m);
    s = O_fstar(pm);
    h = g'(s);
    return h;
  }

  abs A = A {O_F}

  fun B () : state*state = {
    var m, m' : msg;  
    (m, m') = A();
    return (fstar(IV,pad(m)), fstar(IV,pad(m')));
  }
     
  fun Main () : bool = {
    var s, s' : state;  
    (s, s') = B();
    return (g'(s) == g'(s') && !(s == s'));
  }
}

game fstar_coll = {
  fun O_fstar(m:padmsg) : state = {
    return fstar(IV, m);
  }

  fun O_F(m:msg) : hash = {
    var pm : padmsg;
    var s : state;
    var h : hash;
    pm = pad(m);
    s = O_fstar(pm);
    h = g'(s);
    return h;
  }

  abs A = A {O_F}

  fun Main () : bool = {
    var m, m' : msg;  
    (m, m') = A();
    return ((fstar(IV,pad(m)) == fstar(IV,pad(m'))) && !(pad(m) == pad(m')));
  }
}


equiv auto chopMD_inline : chopMD_coll.Main ~ chopMD_inline.Main : {true} ==> { res{1} == (chopMD(fst(res{2})) == chopMD(snd(res{2})) && !(fst(res{2}) == snd(res{2}))) } ;;

claim pr_chopMD_inline : chopMD_coll.Main[res] == chopMD_inline.Main[ chopMD(fst(res)) == chopMD(snd(res)) && !(fst(res) == snd(res)) ]
using chopMD_inline

claim pr_chopMD_split : chopMD_inline.Main[ chopMD(fst(res)) == chopMD(snd(res)) && !(fst(res) == snd(res)) ] == 
      chopMD_inline.Main[ (chopMD(fst(res)) == chopMD(snd(res)) && !(fst(res) == snd(res))) &&  (fstar(IV,pad(fst(res))) == fstar(IV,pad(snd(res))))] +
      chopMD_inline.Main[ (chopMD(fst(res)) == chopMD(snd(res)) && !(fst(res) == snd(res))) && !(fstar(IV,pad(fst(res))) == fstar(IV,pad(snd(res))))]
      split;;

prover "alt-ergo";;

equiv auto eq_g'_coll : chopMD_inline.Main ~ g'_coll.Main : {true} ==> {(chopMD(fst(res{1})) == chopMD(snd(res{1})) && !(fst(res{1}) == snd(res{1})) && !(fstar(IV,pad(fst(res{1}))) == fstar(IV,pad(snd(res{1}))))) == res{2}}

claim pr_g'_coll : 
       chopMD_inline.Main[ (chopMD(fst(res)) == chopMD(snd(res)) && !(fst(res) == snd(res))) && !(fstar(IV,pad(fst(res))) == fstar(IV,pad(snd(res))))] ==
       g'_coll.Main[ res ]
       using eq_g'_coll;;

equiv auto eq_fstar_coll : chopMD_inline.Main ~ fstar_coll.Main : {true} ==> {(chopMD(fst(res{1})) == chopMD(snd(res{1})) && !(fst(res{1}) == snd(res{1})) && (fstar(IV,pad(fst(res{1}))) == fstar(IV,pad(snd(res{1}))))) == res{2}}

claim pr_fstar_coll : 
       chopMD_inline.Main[ (chopMD(fst(res)) == chopMD(snd(res)) && !(fst(res) == snd(res))) && (fstar(IV,pad(fst(res))) == fstar(IV,pad(snd(res))))] ==
       fstar_coll.Main[ res ]
       using eq_fstar_coll;;

claim pr_chopMD_coll_cases : chopMD_coll.Main[res] == g'_coll.Main[ res ] + fstar_coll.Main[ res ]
       

game f_coll = {
  fun O_fstar(m:padmsg) : state = {
    return fstar(IV, m);
  }

  fun O_F(m:msg) : hash = {
    var pm : padmsg;
    var s : state;
    var h : hash;
    pm = pad(m);
    s = O_fstar(pm);
    h = g'(s);
    return h;
  }

  abs A = A {O_F}

  fun B() : farg * farg = {
    var m,m' : msg;
    var b,b' : padmsg;
    var c,c' : farg;
    (m,m') = A();
    b  = pad(m);
    b' = pad(m');

    if (!(length(b) == length(b'))) {
      c = fstarlast(IV,b);
      c'= fstarlast(IV,b');
    }
    else {
      (c,c') = fstarfind(IV,b, IV,b');
    }
    return (c,c');
  }

  fun Main () : bool = {
    var c, c' : farg;  
    (c, c') = B();
    return (f(fst(c),snd(c)) == f(fst(c'),snd(c')) && !(c == c'));
  }
}

equiv auto fstar_f : fstar_coll.Main ~ f_coll.Main : {true} ==> {res{1}} => {res{2}}

claim fstar_le_f : fstar_coll.Main[ res ] <= f_coll.Main[ res ]
      using fstar_f

claim collision_resistance : chopMD_coll.Main[res] <= (g'_coll.Main[ res ] + f_coll.Main[ res ])

