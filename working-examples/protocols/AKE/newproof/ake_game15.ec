include "ake_reduction13_14.ec".

game AKE15 =
AKE14
var posPart : (part, int) map
where Main = {
 var res : session_id * session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 corrupt = empty_map;
 pkey = empty_map;
 skey = empty_map;
 seed = empty_map;
 msg_seeds = empty_map;
 sess = 0;
 part = 0;
 posPart = empty_map;
 res = B();
 return res;
 } and
 KG  =  {
  var sk : secret_key = gen_secret_key();
  var pk : public_key = gen_public_key(sk);
  var res : public_key option = None;
  if (!in_dom(pk,skey) && part < qPart) 
  {
   res = Some(pk);
   corrupt[pk] = false;
   skey[pk] = sk;
   posPart[pk] = part;
   part = part + 1;
  }
  return res;
 }.

 
