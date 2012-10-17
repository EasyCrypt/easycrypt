(*skA -- skB *)
(*true = A, false = B*)
(* first casa: initA, respondB*)
include "ake_game5a.ec".

adversary E () : session_string
{
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool; (* same_session_string *)
 () -> public_key * secret_key; (*KG*)
 () -> message; (*initA*)
  message -> message (* respondB *)
}.

game AKE10' = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var cantKG : int
 var initA_done : int
 var respondB_done : int
 var eph_key_initA : eph_key
 var eph_key_respondB : eph_key
 var initMsg : message
 var respMsg : message
  (* var seed     : (message , eph_key) map*)
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG () : public_key * secret_key = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (cantKG = 0) {
   sk = gen_secret_key(0);
   pk = gen_public_key(sk);
   skA = sk;
   pkA = pk;
   cantKG = 1;
  } else {
   if (cantKG = 1) {
    sk = gen_secret_key(0);
    pk = gen_public_key(sk);
    skB = sk;
    pkB = pk;
    cantKG = 2;
   }
  }
  return (pk,sk);
 }


 fun InitA () : message ={
  var X : message = dummy_message;
  if (cantKG > 1 && initA_done = 0) {
   eph_key_initA = gen_eph_key(0);
   X = out_noclash(skA,eph_key_initA);
   initMsg = X;
   initA_done = 1;
  }
  return X;
 }

 fun RespondB (X : message) : message ={
  var Y : message = dummy_message;
  if (cantKG > 1 && respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   Y = inp(skB,eph_key_respondB);
   respMsg = Y;
   respondB_done = 1;
  }
  return Y;
 }


 abs E = E { eqS, same_session_string, KG, InitA, RespondB }


 fun Main () : session_string = {
  var str : session_string;
  skA = dummy;
  pkA = gen_public_key(skA);
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  str = E();
  return (str);
 }
}.

op wingame10_1
(pkA     : public_key, 
 skA     : secret_key,
 pkB     : public_key, 
 skB     : secret_key, 
 initA_done : int,
 respondB_done : int,
 eph_key_initA : eph_key,
 eph_key_respondB : eph_key,
 str : session_string) =
str = gen_session_string(skA,eph_key_initA,pkB,inp(skB,eph_key_respondB)) &&
initA_done = 1 && respondB_done = 1.

game AKE10_eager1 = 
AKE10' 
var okA : bool
var okB : bool
where
KG = {
 var sk : secret_key = dummy;
 var pk : public_key = gen_public_key(sk);
 if (!okA && cantKG = 0) 
  {
   skA = gen_secret_key(0);
   pkA = gen_public_key(skA);
   okA = true;
  } else {
   if (!okB && cantKG = 1) {
    skB = gen_secret_key(0);
    pkB = gen_public_key(skB);
    okB = true;
   } 
  }
  if (cantKG = 0){
   pk = pkA;
   sk = skA;
   cantKG = 1; 
  } else
  {
  if (cantKG = 1) {
   pk = pkB;
   sk = skB;
   cantKG = 2;
  }
 }
 return (pk,sk);
} and
Main ={
  var str : session_string;
  skA = dummy;
  pkA = gen_public_key(skA);
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  okA = false;
  okB = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  str = E();
  return (str);
 }.


equiv Eq1 : AKE10'.KG ~  AKE10_eager1.KG :
(={pkA,skA,pkB,skB,initA_done,respondB_done,eph_key_initA,eph_key_respondB,cantKG} &&
(okA{2} <=> cantKG{1} > 0) && (okB{2} <=> cantKG{1} > 1)
&& (cantKG{1} = 0 || cantKG{1} = 1 || cantKG{1} = 2)).
sp 2 2.
if.
rnd>>;sp 0 2.
condt{2}.
trivial.
if.
rnd>>;sp 0 2.
condf{2};condt{2}.
trivial.
trivial.
save.

equiv Eq1 : AKE10'.Main ~  AKE10_eager1.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2}
by auto
(={pkA,skA,pkB,skB,initA_done,respondB_done,eph_key_initA,eph_key_respondB,cantKG} &&
(okA{2} <=> cantKG{1} > 0) && (okB{2} <=> cantKG{1} > 1)
&& (cantKG{1} = 0 || cantKG{1} = 1 || cantKG{1} = 2)).

game AKE10_eager2 = 
AKE10_eager1 where
Main ={
  var str : session_string;
  skA = dummy;
  pkA = gen_public_key(skA);
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  okA = false;
  okB = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  str = E();
  if (!okA && cantKG = 0) 
  {
   skA = gen_secret_key(0);
   pkA = gen_public_key(skA);
   okA = true;
  } 
  return (str);
 }.

equiv Eq2 : AKE10_eager1.Main ~  AKE10_eager2.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2} by auto
(={pkA,skA,pkB,skB,initA_done,respondB_done,
  eph_key_initA,eph_key_respondB,cantKG, okA, okB} &&
(initA_done{1} = 1 => cantKG{1} > 1 ) && (cantKG{1} > 0 => okA{1}) ).

game AKE10_eager3 = 
AKE10_eager2 where
Main ={
  var str : session_string;
  skA = dummy;
  pkA = gen_public_key(skA);
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  okA = false;
  okB = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  if (!okA && cantKG = 0) 
  {
   skA = gen_secret_key(0);
   pkA = gen_public_key(skA);
   okA = true;
  } 
  str = E();
  return (str);
 }.

equiv Eq3 : AKE10_eager2.Main ~  AKE10_eager3.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2} by eager
{if (!okA && cantKG = 0) 
{
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 okA = true;
}}.

derandomize.
swap{1} 1 1.
trivial.
save.

derandomize.
swap{1} 3 -1.
trivial.
save.

trivial.
trivial.
save.

game AKE10_eager4 = 
AKE10_eager3 where
KG = {
 var sk : secret_key = dummy;
 var pk : public_key = gen_public_key(sk);
 if (!okB && cantKG = 1) {
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  okB = true;
 } 
 if (cantKG = 0){
  pk = pkA;
  sk = skA;
  cantKG = 1; 
 } else
 {
  if (cantKG = 1) {
   pk = pkB;
   sk = skB;
   cantKG = 2;
  }
 }
 return (pk,sk);
} and
Main ={
  var str : session_string;
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  okB = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  str = E();
  return (str);
 }.


equiv Eq3 : AKE10_eager3.Main ~  AKE10_eager4.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2} by auto 
(={pkA,skA,pkB,skB,initA_done,respondB_done,
  eph_key_initA,eph_key_respondB,cantKG, okB} && okA{1}).


adversary E' (_ : secret_key) : session_string
{
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool; (* same_session_string *)
 () -> public_key * secret_key; (*KG*)
 () -> message; (*initA*)
  message -> message (* respondB *)
}.


game AKE10_eager5_ctxt = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var cantKG : int
 var initA_done : int
 var respondB_done : int
 var eph_key_initA : eph_key
 var eph_key_respondB : eph_key
 var initMsg : message
 var respMsg : message
 var okB : bool
 (* context variables *)

 var cantKG_C : int
 var pkA_C : public_key
 var skA_C : secret_key

  (* var seed     : (message , eph_key) map*)
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG () : public_key * secret_key = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (!okB && cantKG = 0) {
   skB = gen_secret_key(0);
   pkB = gen_public_key(skB);
   okB = true;
  } 
  if (cantKG = 0){
   pk = pkA;
   sk = skA;
   cantKG = 1; 
  } else
  {
   if (cantKG = 1) {
    pk = pkB;
    sk = skB;
    cantKG = 2;
   }
 }
 return (pk,sk);
}

 fun InitA () : message ={
  var X : message = dummy_message;
  if (cantKG > 1 && initA_done = 0) {
   eph_key_initA = gen_eph_key(0);
   X = out_noclash(skA,eph_key_initA);
   initMsg = X;
   initA_done = 1;
  }
  return X;
 }

 fun RespondB (X : message) : message ={
  var Y : message = dummy_message;
  if (cantKG > 1 && respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   Y = inp(skB,eph_key_respondB);
   respMsg = Y;
   respondB_done = 1;
  }
  return Y;
 }
 
 fun KG_C() : public_key * secret_key = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (cantKG_C = 0) {
   pk = pkA_C;
   sk = skA_C;
   cantKG_C = 1;
  } else {
   if (cantKG_C = 1) {
    (pk,sk) = KG();
    (pk,sk) = KG();
    cantKG_C = 2;
   }
  }
  return (pk,sk); 
 }

 fun InitA_C() : message ={
  var msg :message;
  msg = InitA();
  return msg;
 }

 fun RespondB_C(X : message) : message ={
  var msg :message;
  msg = RespondB(X);
  return msg;
 }


 abs E = E { eqS, same_session_string, KG_C, InitA_C, RespondB_C }
 
 fun E'(skA_ : secret_key) : session_string = {
  var str : session_string;
  skA_C = skA_;
  pkA_C = gen_public_key(skA_C);
  cantKG_C = 0;
  str = E();
  return str;
 }

fun Main() : session_string ={
  var str : session_string;
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  okB = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  str = E'(skA);
  return (str);
 }
}.

equiv Eq4KG : AKE10_eager4.KG ~  AKE10_eager5_ctxt.KG_C :
 (={pkA,skA,pkB,skB,initA_done,respondB_done,
  eph_key_initA,eph_key_respondB, okB} &&
(skA_C{2} = skA{2}&& pkA_C{2} = pkA{2} && cantKG{1} = cantKG_C{2}) &&
(cantKG_C{2} = 0 => cantKG{2} = 0) &&
(cantKG_C{2} = 1 => cantKG{2} = 0) && (cantKG{2} = 0 => (cantKG_C{2} = 0 || cantKG_C{2} = 1))&&
(cantKG_C{2} = 2 <=> cantKG{2} = 2 && (cantKG = 0 ||cantKG = 1 ||cantKG = 2){2}) &&
(cantKG = 0 ||cantKG = 1 ||cantKG = 2){1}).
sp 2 2.
if{2}.
condf{1}.
condt{1}.
trivial.
if{2}.
inline KG.
sp 0 2.
if.
rnd>>;sp 2 2.
condf{1}.
condt{1}.
condt{2}.
sp 0 6.
condf{2}.
condf{2}.
condt{2}.
trivial.
condt{2}.
condf{1}.
condt{1}.
sp 0 6.
condf{2}.
condf{2}.
condt{2}.
trivial.
condf{1}.
condf{1}.
condf{1}.
trivial.
save.


equiv Eq4 : AKE10_eager4.Main ~  AKE10_eager5_ctxt.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2}
by auto(={pkA,skA,pkB,skB,initA_done,respondB_done,
  eph_key_initA,eph_key_respondB, okB} &&
(skA_C{2} = skA{2}&& pkA_C{2} = pkA{2} && cantKG{1} = cantKG_C{2}) &&
(cantKG_C{2} = 0 => cantKG{2} = 0) &&
(cantKG_C{2} = 1 => cantKG{2} = 0) && (cantKG{2} = 0 => (cantKG_C{2} = 0 || cantKG_C{2} = 1))&&
(cantKG_C{2} = 2 <=> cantKG{2} = 2 && (cantKG = 0 ||cantKG = 1 ||cantKG = 2){2}) &&
(cantKG = 0 ||cantKG = 1 ||cantKG = 2){1}).

game AKE10_eager5 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var cantKG : int
 var initA_done : int
 var respondB_done : int
 var eph_key_initA : eph_key
 var eph_key_respondB : eph_key
 var initMsg : message
 var respMsg : message
 var okB : bool
  (* var seed     : (message , eph_key) map*)
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG () : public_key * secret_key = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (!okB && cantKG = 0) {
   skB = gen_secret_key(0);
   pkB = gen_public_key(skB);
   okB = true;
  } 
  if (cantKG = 0){
   pk = pkA;
   sk = skA;
   cantKG = 1; 
  } else
  {
   if (cantKG = 1) {
    pk = pkB;
    sk = skB;
    cantKG = 2;
   }
 }
 return (pk,sk);
}

 fun InitA () : message ={
  var X : message = dummy_message;
  if (cantKG > 1 && initA_done = 0) {
   eph_key_initA = gen_eph_key(0);
   X = out_noclash(skA,eph_key_initA);
   initMsg = X;
   initA_done = 1;
  }
  return X;
 }

 fun RespondB (X : message) : message ={
  var Y : message = dummy_message;
  if (cantKG > 1 && respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   Y = inp(skB,eph_key_respondB);
   respMsg = Y;
   respondB_done = 1;
  }
  return Y;
 }


 abs E' = E' { eqS, same_session_string, KG, InitA, RespondB }

fun Main() : session_string ={
  var str : session_string;
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  okB = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  str = E'(skA);
  return (str);
 }
}.

game AKE10_eager6 = 
AKE10_eager5
where
Main = { 
  var str : session_string;
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  okB = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  str = E'(skA);
  if (!okB && cantKG = 0) {
   skB = gen_secret_key(0);
   pkB = gen_public_key(skB);
   okB = true;
  } 
  return (str);
 }.


equiv Eq5 : AKE10_eager5.Main ~  AKE10_eager6.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2}
by auto
(={pkA,skA,pkB,skB,initA_done,respondB_done,
  eph_key_initA,eph_key_respondB, okB, cantKG} &&
(initA_done{1} > 0 => cantKG{1} > 1) &&
(cantKG{1} > 0 => okB{1})).

game AKE10_eager7 = 
AKE10_eager6
where
Main = { 
  var str : session_string;
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  okB = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  if (!okB && cantKG = 0) {
   skB = gen_secret_key(0);
   pkB = gen_public_key(skB);
   okB = true;
  } 
  str = E'(skA);
  return (str);
 }.

equiv Eq5 : AKE10_eager6.Main ~  AKE10_eager7.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2}
by eager
{
 if (!okB && cantKG = 0) {
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  okB = true;
 } 
}.
derandomize.
swap{1} 1 1.
trivial.
save.

derandomize.
trivial.
save.

trivial.
trivial.
save.


game AKE10_eager8 = 
AKE10_eager7
where
Main = { 
  var str : session_string;
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  str = E'(skA);
  return (str);
 } and 
KG = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (cantKG = 0){
   pk = pkA;
   sk = skA;
   cantKG = 1; 
  } else
  {
   if (cantKG = 1) {
    pk = pkB;
    sk = skB;
    cantKG = 2;
   }
  }
  return (pk,sk);
 }.
 

equiv Eq5 : AKE10_eager7.Main ~  AKE10_eager8.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2}
by auto
(={pkA,skA,pkB,skB,initA_done,respondB_done,
  eph_key_initA,eph_key_respondB, cantKG} && okB{1}).

game AKE10_eager9_ctxt = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var initA_done : int
 var respondB_done : int
 var eph_key_initA : eph_key
 var eph_key_respondB : eph_key
 var initMsg : message
 var respMsg : message
 (* context variables *)
 var cantKG_C : int
 var pkA_C     : public_key 
 var skA_C     : secret_key 
 var pkB_C     : public_key 
 var skB_C     : secret_key 
 
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun InitA () : message ={
  var X : message = dummy_message;
  if (initA_done = 0) {
   eph_key_initA = gen_eph_key(0);
   X = out_noclash(skA,eph_key_initA);
   initMsg = X;
   initA_done = 1;
  }
  return X;
 }

 fun RespondB (X : message) : message ={
  var Y : message = dummy_message;
  if (respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   Y = inp(skB,eph_key_respondB);
   respMsg = Y;
   respondB_done = 1;
  }
  return Y;
 }
fun KG_C() : public_key * secret_key = {
 var sk : secret_key = dummy;
 var pk : public_key = gen_public_key(sk);
 if (cantKG_C = 0){
  pk = pkA_C;
  sk = skA_C;
  cantKG_C = 1; 
 } else
 {
  if (cantKG_C = 1) {
   pk = pkB_C;
   sk = skB_C;
   cantKG_C = 2;
  }
 }
 return (pk,sk);
}


 fun InitA_C() : message ={
  var msg :message = dummy_message;
  if (cantKG_C > 1) {
   msg = InitA();
  }
  return msg;
 }
 
 fun RespondB_C(X : message) : message ={
  var msg :message = dummy_message;
  if (cantKG_C > 1) {
   msg = RespondB(X);
  }
  return msg;
 }


 abs E' = E' { eqS, same_session_string, KG_C, InitA_C, RespondB_C }
 
 fun E''(skA_ : secret_key, skB_ : secret_key) : session_string =
 {
  var res : session_string;
  cantKG_C = 0;
  skA_C = skA_;
  pkA_C = gen_public_key(skA);
  skB_C = skB_;
  pkB_C = gen_public_key(skB);
  res = E'(skA);
  return res;
 }
 
 fun Main() : session_string ={
  var str : session_string;
  initA_done = 0;
  respondB_done = 0;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  str = E''(skA,skB);
  return (str);
 }
}.


equiv Eq6 : AKE10_eager8.Main ~  AKE10_eager9_ctxt.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2}
by auto(={pkA,skA,pkB,skB,initA_done,respondB_done,
  eph_key_initA,eph_key_respondB} &&
(skA_C{2} = skA{2}&& pkA_C{2} = pkA{2} && 
 skB_C{2} = skB{2}&& pkB_C{2} = pkB{2} && cantKG{1} = cantKG_C{2}) &&
(cantKG = 0 ||cantKG = 1 ||cantKG = 2){1}).

adversary E'' (skA : secret_key ,skB : secret_key) : session_string
{
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool; (* same_session_string *)
 () -> message; (*initA*)
  message -> message (* respondB *)
}.


game AKE10_eager9 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var initA_done : int
 var respondB_done : int
 var eph_key_initA : eph_key
 var eph_key_respondB : eph_key
 var initMsg : message
 var respMsg : message
  (* var seed     : (message , eph_key) map*)
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun InitA () : message ={
  var X : message = dummy_message;
  if (initA_done = 0) {
   eph_key_initA = gen_eph_key(0);
   X = out_noclash(skA,eph_key_initA);
   initMsg = X;
   initA_done = 1;
  }
  return X;
 }

 fun RespondB (X : message) : message ={
  var Y : message = dummy_message;
  if (respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   Y = inp(skB,eph_key_respondB);
   respMsg = Y;
   respondB_done = 1;
  }
  return Y;
 }


 abs E'' = E'' { eqS, same_session_string,InitA, RespondB }

fun Main() : session_string ={
  var str : session_string;
  initA_done = 0;
  respondB_done = 0;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  str = E''(skA,skB);
  return (str);
 }
}.

game AKE10_eager10 = 
 AKE10_eager9 
 var ephAOk : bool
 var ephBOk : bool
 where  
InitA = {
 var X : message = dummy_message;
 if (!ephAOk && initA_done = 0) {
  eph_key_initA = gen_eph_key(0);
  ephAOk = true;
 }
 if (initA_done = 0) {
  X = out_noclash(skA,eph_key_initA);
  initMsg = X;
  initA_done = 1;
 }
 return X;
} and 
RespondB = {
 var Y : message = dummy_message;
 if (!ephBOk && respondB_done = 0) {
  eph_key_respondB = gen_eph_key(0);
  ephBOk = true;
 }
 if (respondB_done = 0) {
  Y = inp(skB,eph_key_respondB);
  respMsg = Y;
  respondB_done = 1;
 }
 return Y;
} and Main = {
  var str : session_string;
  initA_done = 0;
  respondB_done = 0;
  ephAOk = false;
  ephBOk = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  str = E''(skA,skB);
  if (!ephAOk && initA_done = 0) {
   eph_key_initA = gen_eph_key(0);
   ephAOk = true;
  }
  if (!ephBOk && respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   ephBOk = true;
  }
  return (str);
}.

equiv Eq7 : AKE10_eager9.Main ~ AKE10_eager10.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2} by auto
(={pkA,skA,pkB,skB,initA_done,respondB_done,
  eph_key_initA,eph_key_respondB} && 
(initA_done{1} = 1 <=> ephAOk {2})&&
(respondB_done{1} = 1 <=> ephBOk {2})).

game AKE10_eager11 = 
 AKE10_eager10 where 
Main = {
  var str : session_string;
  initA_done = 0;
  respondB_done = 0;
  ephAOk = false;
  ephBOk = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  if (!ephAOk && initA_done = 0) {
   eph_key_initA = gen_eph_key(0);
   ephAOk = true;
  }
  str = E''(skA,skB);
  if (!ephBOk && respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   ephBOk = true;
  }
  return (str);
}.

equiv Eq7 : AKE10_eager10.Main ~ AKE10_eager11.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2} by eager
{  if (!ephAOk && initA_done = 0) {
   eph_key_initA = gen_eph_key(0);
   ephAOk = true;
  }
}.
derandomize.
trivial.
save.

trivial.
if.
trivial.
trivial.
save.

game AKE10_eager12 = 
 AKE10_eager11 where 
Main = {
  var str : session_string;
  initA_done = 0;
  respondB_done = 0;
  ephAOk = false;
  ephBOk = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  if (!ephAOk && initA_done = 0) {
   eph_key_initA = gen_eph_key(0);
   ephAOk = true;
  }
  if (!ephBOk && respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   ephBOk = true;
  }
  str = E''(skA,skB);
  return (str);
}.

equiv Eq8 : AKE10_eager11.Main ~ AKE10_eager12.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2} by eager
{ 
  if (!ephBOk && respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   ephBOk = true;
  }
}.

derandomize.
trivial.
save.

derandomize;trivial.
trivial.
save.

game AKE10_eager13 = 
 AKE10_eager12 where 
Main = {
  var str : session_string;
  initA_done = 0;
  respondB_done = 0;
  ephAOk = false;
  ephBOk = false;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  initMsg = dummy_message;
  respMsg = dummy_message;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA); 
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  eph_key_initA = gen_eph_key(0);
  eph_key_respondB = gen_eph_key(0);
  str = E''(skA,skB);
  return (str);
} and InitA = {
 var X : message = dummy_message;
 if (initA_done = 0) {
  X = out_noclash(skA,eph_key_initA);
  initMsg = X;
  initA_done = 1;
 }
 return X;
} and 
RespondB = {
 var Y : message = dummy_message;
 if (respondB_done = 0) {
  Y = inp(skB,eph_key_respondB);
  respMsg = Y;
  respondB_done = 1;
 }
 return Y;
}.

equiv Eq7 : AKE10_eager12.Main ~ AKE10_eager13.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} <=>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){2} by auto
(={pkA,skA,pkB,skB,initA_done,respondB_done,
  eph_key_initA,eph_key_respondB} &&  ephAOk{1} && ephBOk{1}).

game AKE10_ctxt = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var ephKA_Y : eph_key
 var ephKB_X : eph_key
 var ephKB_Y : eph_key  
 var XA : message
 var YA : message
 var XB : message
 var YB : message
 (* context variables *)
 var initA_done_C : int
 var respondB_done_C : int
 var initMsg_C : message
 var respMsg_C : message
 var skA_C     : secret_key 
 var skB_C     : secret_key 

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 (* Context implementations *)
 fun InitA_C() : message = {
  var X : message = dummy_message;
  if (initA_done_C = 0) {
   X = initMsg_C;
   initA_done_C = 1;
  }
  return X;
 }
 fun RespondB_C (X : message) : message = {
 var Y : message = dummy_message;
 if (respondB_done_C = 0) {
  Y = respMsg_C;
  respondB_done_C = 1;
 }
 return Y;
}

 abs E'' = E'' { eqS, same_session_string,InitA_C, RespondB_C }
 
 fun E'''(skA_, skB_ : secret_key, AX_ : message, 
     AY_ : message, BX_ : message, BY_ : message) : session_string = {
  var str : session_string;
  initA_done_C = 0;
  respondB_done_C = 0;
  initMsg_C = AX_;
  respMsg_C = BY_;
  skA_C = skA_;
  skB_C = skB_;
  str = E''(skA_C,skB_C);
  return str;
 }


 fun Main () : session_string = {
  var b : bool; 
  var ek : eph_key;
  var X : message; 
  var Y : message; 
  var str : session_string;
  var test : bool;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  skB = gen_secret_key(0); 
  pkB = gen_public_key(skB);
  ephKA_X = gen_eph_key(0);
  ephKA_Y = gen_eph_key(0);
  ephKB_X = gen_eph_key(0);
  ephKB_Y = gen_eph_key(0);
  XA = out_noclash(skA,ephKA_X);
  YA = inp(skA,ephKA_Y);
  XB = out_noclash(skB,ephKB_X);
  YB = inp(skB,ephKB_Y);
  str = E'''(skA,skB, XA, YA, XB, YB);
  return (str);
 }
}.

op wingame10
(pkA     : public_key, 
 skA     : secret_key,
 pkB     : public_key, 
 skB     : secret_key, 
 ephKA_X : eph_key,
 ephKA_Y : eph_key,
 ephKB_X : eph_key,
 ephKB_Y : eph_key,  
 XA : message,
 YA : message,
 XB : message,
 YB : message,
 str : session_string) =
str = gen_session_string(skA,ephKA_X,pkB,YB) ||
str = gen_session_string(skA,ephKA_X,pkB,XB) ||
str = gen_session_string(skB,ephKB_X,pkA,XA) ||
str = gen_session_string(skB,ephKB_X,pkA,YA).

equiv Eq8 :  AKE10_eager13.Main ~ AKE10_ctxt.Main : true ==>
wingame10_1(pkA,skA,pkB, skB,initA_done,respondB_done,
 eph_key_initA,eph_key_respondB,res){1} =>
wingame10(pkA,skA,pkB, skB,ephKA_X,
 ephKA_Y,ephKB_X,ephKB_Y,XA,YA,XB,YB,res){2}.
inline.
wp.
call
(={pkA,skA,pkB,skB} &&
initA_done{1} = initA_done_C{2} &&
respondB_done{1} = respondB_done_C{2} &&
eph_key_initA{1} = ephKA_X{2} &&
eph_key_respondB{1} = ephKB_Y{2} && 
initMsg_C{2} = out_noclash (skA,eph_key_initA){1} &&
respMsg_C{2} = inp (skB,eph_key_respondB){1}).
derandomize.
!2 rnd>>.
swap{2} 4 -2.
!2 rnd>>.
trivial.
save.

equiv Eq8 :  AKE10_eager13.InitA ~ AKE10_ctxt.InitA_C :
(={pkA,skA,pkB,skB} &&
initA_done{1} = initA_done_C{2} &&
respondB_done{1} = respondB_done_C{2} &&
eph_key_initA{1} = ephKA_X{2} &&
eph_key_respondB{1} = ephKB_Y{2} && 
initMsg_C{2} = out_noclash (skA,eph_key_initA){1} &&
respMsg_C{2} = out_noclash (skB,eph_key_respondB){1}).
sp 1 1.
if.
trivial.
trivial.
save.

adversary E''' (skA, skB : secret_key, AX : message, AY : message, BX : message, BY : message) : session_string
{
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

game AKE10 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var ephKA_Y : eph_key
 var ephKB_X : eph_key
 var ephKB_Y : eph_key  
 var XA : message
 var YA : message
 var XB : message
 var YB : message

(* var seed     : (message , eph_key) map*)
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 abs E''' = E''' { eqS, same_session_string }

 fun Main () : session_string = {
  var b : bool; 
  var ek : eph_key;
  var X : message; 
  var Y : message; 
  var str : session_string;
  var test : bool;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  skB = gen_secret_key(0); 
  pkB = gen_public_key(skB);
  ephKA_X = gen_eph_key(0);
  ephKA_Y = gen_eph_key(0);
  ephKB_X = gen_eph_key(0);
  ephKB_Y = gen_eph_key(0);
  XA = inp(skA,ephKA_X);
  YA = inp(skA,ephKA_Y);
  XB = inp(skB,ephKB_X);
  YB = inp(skB,ephKB_Y);
  str = E'''(skA,skB, XA, YA, XB, YB);
  return (str);
 }
}.


