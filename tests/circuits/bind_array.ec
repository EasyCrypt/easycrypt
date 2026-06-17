(* Extracted from doc/tactics/bindings.rst -- "Array Binding Example". *)

require import AllCore List QFABV.

theory Array8.
type 'a t.

op tolist : 'a t -> 'a list.
op oflist : 'a -> 'a list -> 'a t.
op "_.[_]" : 'a t -> int -> 'a.
op "_.[_<-_]" : 'a t -> int -> 'a -> 'a t.

end Array8.

bind array Array8."_.[_]" Array8."_.[_<-_]" Array8.tolist Array8.oflist Array8.t 8.
realize gt0_size by auto.
realize tolistP by admit.
realize oflistP by admit.
realize eqP by admit.
realize get_setP by admit.
realize get_out by admit.
