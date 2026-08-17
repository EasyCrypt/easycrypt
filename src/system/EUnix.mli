
(* -------------------------------------------------------------------- *)
val setpgid : int -> int -> unit

(* -------------------------------------------------------------------- *)
(* Unix only: on this platform, file descriptors are integers *)
val int_of_filedescr : Unix.file_descr -> int