/* ==================================================================== */
#if !defined(AVX2_RUNTIME__)
# define AVX2_RUNTIME__ 1

#if defined(__x86_64__) || defined(_M_X64)
# define HAS_AVX 1
# include <immintrin.h>
#endif

/* -------------------------------------------------------------------- */
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>

/* -------------------------------------------------------------------- */
extern "C" {
CAMLprim value m64_of_32x2(value);
CAMLprim value m64_to_32x2(value);
CAMLprim value m32_of_16x2(value lohi);
CAMLprim value m32_to_16x2(value lohi);
CAMLprim value m16_of_8x2(value lohi);
CAMLprim value m16_to_8x2(value lohi);

CAMLprim value caml_mm256_and_si256(value, value);
CAMLprim value caml_mm256_andnot_si256(value, value);
CAMLprim value caml_mm256_add_epi16(value, value);
CAMLprim value caml_mm256_sub_epi16(value, value);
CAMLprim value caml_mm256_maddubs_epi16(value, value);
CAMLprim value caml_mm256_packus_epi16(value, value);
CAMLprim value caml_mm256_mulhi_epu16(value, value);
CAMLprim value caml_mm256_mulhrs_epi16(value, value);
CAMLprim value caml_mm256_permutexvar_epi32(value, value);
}

/* ==================================================================== */
#if defined(HAS_AVX)

/* -------------------------------------------------------------------- */
extern value value_of_w256(__m256i x);
extern __m256i w256_of_value(value x);

struct M256i {
  typedef __m256i type;

  static inline type ofocaml(value v) {
    return w256_of_value(v);
  }

  static inline value toocaml(type v) {
    return value_of_w256(v);
  }
};

/* -------------------------------------------------------------------- */
struct Long {
  typedef long type;

  static inline type ofocaml(value v) {
    return Long_val(v);
  }

  static inline value toocaml(type v) {
    return Val_long(v);
  }
};

/* -------------------------------------------------------------------- */
template <auto F, typename U, typename T1, typename T2>
static value bind(value arg1, value arg2) {
  CAMLparam2(arg1, arg2);
  typename T1::type varg1 = T1::ofocaml(arg1);
  typename T2::type varg2 = T2::ofocaml(arg2);
  CAMLreturn(U::toocaml(F(varg1, varg2)));
}

/* -------------------------------------------------------------------- */
# define BIND1(F, U, T)                       \
CAMLprim value caml_##F(value a) {            \
  return bind<_##F, U, T>(a);                 \
}

/* -------------------------------------------------------------------- */
# define BIND2(F, U, T1, T2)                  \
CAMLprim value caml_##F(value a, value b) {   \
  return bind<_##F, U, T1, T2>(a, b);         \
}

/* ==================================================================== */
#else

/* -------------------------------------------------------------------- */
# define BIND1(F, U, T)                       \
CAMLprim value caml_##F(value a) {            \
  CAMLparam1(a);                              \
  caml_failwith("not implemented: " #F);      \
  CAMLreturn(Val_unit);                       \
}

/* -------------------------------------------------------------------- */
# define BIND2(F, U, T1, T2)                  \
CAMLprim value caml_##F(value a, value b) {   \
  CAMLparam2(a, b);                           \
  caml_failwith("not implemented: " #F);      \
  CAMLreturn(Val_unit);                       \
}

#endif /* defined(HAS_AVX) */

#define BIND_256x2_256(F) BIND2(F, M256i, M256i, M256i)

#endif /* !AVX2_RUNTIME__ */
