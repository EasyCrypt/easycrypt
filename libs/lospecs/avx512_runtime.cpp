/* ==================================================================== */
#include "avx2_runtime.h"

/* -------------------------------------------------------------------- */
#include <stdint.h>

/* -------------------------------------------------------------------- */
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>

/* -------------------------------------------------------------------- */
extern "C"{
BIND_256x2_256(mm256_permutexvar_epi32);
}
