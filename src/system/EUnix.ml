(* -------------------------------------------------------------------- *)
external setpgid : int -> int -> unit = "caml_eunix_setpgid"

(* -------------------------------------------------------------------- *)
external int_of_filedescr : Unix.file_descr -> int = "caml_eunix_int_of_filedescr"
