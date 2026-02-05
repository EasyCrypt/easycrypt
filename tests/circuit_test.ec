require import AllCore List QFABV IntDiv.


theory FakeWord.
type W.
op size : int.

op to_bits : W -> bool list.
op from_bits : bool list -> W.
op of_int : int -> W.
op to_uint : W -> int.
op to_sint : W -> int.

bind bitstring
  to_bits 
  from_bits 
  to_uint 
  to_sint
  of_int 
  W
  size.

realize gt0_size by admit.
realize tolistP by admit.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.
realize size_tolist by admit.

op zero : W = of_int 0.
op one  : W = of_int 1.

op bool2bits (b : bool) : bool list = [b].
op bits2bool (b: bool list) : bool = List.nth false b 0.

op i2b : int -> bool.
op b2si (b: bool) = 0.

bind bitstring bool2bits bits2bool b2i b2si i2b bool 1.
realize size_tolist by auto.
realize tolistP by auto.

realize oflistP by rewrite /bool2bits /bits2bool;smt(size_eq1).
realize ofintP by admit.
realize touintP by admit.
realize tosintP by move => bv => //. 
realize gt0_size by done.
    
op (+^) : W -> W -> W.

bind op W (+^) "xor".
realize bvxorP by admit.

end FakeWord.

type W8.

clone include FakeWord with
  op size <- 8,
  type W <- W8.

module M = {
  proc test (a: W8, b: W8) = {
    var c : W8;
    c <- a +^ b;
    return c;
  }
}.

op "_.[_]" : W8 -> int -> bool.

op non_translate : W8 -> W8.

bind op [W8 & bool] "_.[_]" "get".
realize le_size by auto.
realize eq1_size by auto.
realize bvgetP by admit.

lemma W8_ext (a: W8) : List.all (fun i => a.[i] = a.[i]) (iota_ 0 8).
proof.
extens : circuit.
qed.



lemma W8_xor_ext (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
proc.
extens [a] : (wp; skip; smt()). 
(* FIXME : while debugging fhash  admit. *)
qed.


lemma W8_xor_simp (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
proc.
circuit simplify. trivial. (* admit. *)
qed.



lemma W8_xor_fail_equiv (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ zero].
proof.
proc.
circuit. (* Fails *)
qed.

lemma W8_xor_fail_translate (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ non_translate zero].
proof.
proc.
circuit. (* Fails *)
qed.


lemma W8_xor_ext2 (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
proc.
admit.
(* extens [a] : circuit.  *)
qed.

lemma W8_xor_ext_simp (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
proc.
(* extens [a] : by circuit simplify; trivial. (* FIXME: without by does not work *) *) admit.
qed.


(*
lemma xor_0 (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b /\ a_ = b_ ==> res = of_int 0].
proof.
  proc.
  proc change 1 : { c <- b +^ a; }.
  wp. skip. move => &h1 &h2.
  have : a{h1} = a_ by admit.
  have : b{h1} = b_ by admit.
  move => A B [] C D.
  have : a{h2} = a_ by smt().
  have : b{h2} = b_ by smt().
  (* move : A B C D. (* Comment or uncomment this line for different modes of working *) *)
  bdep solve.
bdep solve.
qed.
*)
    

lemma xor_com (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b /\ a_ = b_ ==> res = b_ +^ a_].
proof.
  proc.
  proc change 1 : [ d : W8 ] { d <- of_int 0; d <- a +^ d; c <- d +^ b; }.
  circuit.
  circuit.
qed.

theory Array8.
type 'a t.

op tolist : 'a t -> 'a list.
op oflist : 'a list -> 'a t.
op "_.[_]" : 'a t -> int -> 'a.
op "_.[_<-_]" : 'a t -> int -> 'a -> 'a t.

end Array8.

bind array Array8."_.[_]" Array8."_.[_<-_]" Array8.tolist Array8.oflist Array8.t 8.
realize gt0_size by auto.
realize tolistP by admit.
realize eqP by admit.
realize get_setP by admit.
realize get_out by admit.


op init_8_8 (f: int -> W8) : W8 Array8.t.

bind op [W8 & Array8.t] init_8_8 "ainit".
realize bvainitP by admit.

print Array8."_.[_]".

op get : W8 Array8.t -> int -> W8 = Array8."_.[_]".

lemma init_test (_aw: W8 Array8.t) : 
  init_8_8 (fun i => get _aw ((i * -1) %% 8)) = 
    init_8_8 (fun i => 
      get (init_8_8  
        (get (init_8_8 (fun k =>  
          get (init_8_8 (fun (l: int) => 
            get _aw ((l*5)%%8))) ((k * 3) %% 8))))) i ).
proof.
circuit.
qed.

