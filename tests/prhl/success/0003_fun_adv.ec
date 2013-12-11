module type O = {
  proc f () : unit
}.

module type Adv (O1:O) = { 
  proc g () : unit 
}.

lemma test : forall (O2<:O) (A<:Adv{O2}),
  equiv [A(O2).g ~ A(O2).g : (glob O2){1} = (glob O2){2} /\  (glob A){1} = (glob A){2} ==> 
                        (glob O2){1} = (glob O2){2} /\  (glob A){1} = (glob A){2}].
proof.
intros O2 A.
proc ((glob O2){1} = (glob O2){2});try progress.
(*
Works with proc ((glob A){1} = (glob A){2}).
Do we want to add this automatically?
*)
proc true;progress.
qed.
