module type O = {
  fun f () : unit
}.

module type Adv (O1:O) = { 
  fun g () : unit 
}.

lemma test : forall (O2<:O) (A<:Adv),
  equiv [A(O2).g ~ A(O2).g : (glob O2){1} = (glob O2){2} /\  (glob A){1} = (glob A){2} ==> 
                        (glob O2){1} = (glob O2){2} /\  (glob A){1} = (glob A){2}].
intros O2 A.
fun ((glob O2){1} = (glob O2){2}).


