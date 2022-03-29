require import CyclicGroup DBool SmtMap FSet DList Int List.

(* Multiple Oracle-DH *)

type range.
type secret = t.

(* A hash function with domain consistent with group type *)
op hash : group -> range.

(* Generate a random value from the hash range. *)
op genRange : range distr.

module type ODH_OrclT = {
  proc init(b : bool) : unit
  proc gen() : group
  proc ror(gys : group fset) : (group * (group * range)) list option
  proc hash(gy: group, m : group) : range option
}.

module type ODH_Adv(O : ODH_OrclT) = {
  proc guess() : bool
}.

op q_gen : int.
op q_ror : int.

axiom posbounds : 0 < q_gen /\ 0 < q_ror.

module ODH_Orcl : ODH_OrclT = {
  var b : bool
  var genMap : (group, secret) fmap
  var rorList : (group * group) fset

  var count_gen : int
  var count_ror : int

  proc init(bval : bool) = {
    b <- bval;
    genMap <- empty;
    rorList <- fset0;
    count_gen <- 0;
    count_ror <- 0;
 }

 proc gen() = {
    var y,gy;
    
    y <$FDistr.dt;
    gy <- witness;

    if (count_gen < q_gen) {
       gy <- g ^ y;
 
       if (! gy \in genMap) {
          genMap.[gy] <- y;
       }

       count_gen <- count_gen + 1;
    }

    return gy;
 }

 proc ror(gys : group fset) : (group * (group * range)) list option = {
   var rhs, hs, gylist, gygxlist, keys, n_keys, x, gx;

   rhs <- None;

   gylist <- elems gys;
   n_keys <- size gylist;

   x <$ FDistr.dt;
   keys <$ dlist genRange n_keys;

   gx <- g ^ x;

   if (count_ror < q_ror) {
     if (gys \subset (fdom genMap)) {
        gygxlist <- map (fun gy => (gy,gx)) gylist;
        rorList <- rorList `|` oflist gygxlist;
        hs <- amap (fun k v => if b then (gx, v) else (gx, hash (k^x)))
                   (zip gylist keys);
        rhs <- Some hs;
     }
     count_ror <- count_ror + 1;
   }
   return rhs;
 }

 proc hash(gy: group, val : group) : range option = {
   var h, y;
   h <- None;

   if (gy \in genMap /\ (!(gy,val) \in rorList)) {
     y <- oget genMap.[gy];
     h <- Some (hash (val^y));
   }
   return h;
 }
}.

module ODH_Sec (A : ODH_Adv) = {
  module O = ODH_Orcl

  proc game (b: bool)  = {
    var b';

    O.init(b);
    b' <@ A(O).guess();
    
    return (b = b');
  }

  proc main () : bool = {
    var b, b';

    b <$ {0,1};
    b' <@ game(b);

    return (b');
  }
}.
