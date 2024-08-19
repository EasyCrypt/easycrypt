/* -------------------------------------------------------------------- */
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/unixsupport.h>

#include <unistd.h>

/* -------------------------------------------------------------------- */
CAMLprim value caml_eunix_setpgid(value pid, value pgid) {
  CAMLparam2(pid, pgid);
  if (setpgid(Int_val(pid), Int_val(pgid)) != 0)
    uerror("setpgid", Nothing);
  CAMLreturn(Val_unit);
}
