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
CAMLprim value caml_mm256_permutevar8x32_epi32(value, value);
CAMLprim value caml_mm256_permute4x64_epi64_dyn(value, value);
CAMLprim value caml_mm256_permute2x128_si256_dyn(value, value, value);
CAMLprim value m64_of_32x2(value);
CAMLprim value m64_to_32x2(value);
CAMLprim value m32_of_16x2(value lohi);
CAMLprim value m32_to_16x2(value lohi);
CAMLprim value m16_of_8x2(value lohi);
CAMLprim value m16_to_8x2(value lohi);

CAMLprim value caml_mm256_and_si256(value, value);
CAMLprim value caml_mm256_andnot_si256(value, value);
CAMLprim value caml_mm256_add_epi8(value, value);
CAMLprim value caml_mm256_add_epi16(value, value);
CAMLprim value caml_mm256_sub_epi8(value, value);
CAMLprim value caml_mm256_sub_epi16(value, value);
CAMLprim value caml_mm256_maddubs_epi16(value, value);
CAMLprim value caml_mm256_packus_epi16(value, value);
CAMLprim value caml_mm256_packs_epi16(value, value);
CAMLprim value caml_mm256_mulhi_epu16(value, value);
CAMLprim value caml_mm256_mulhrs_epi16(value, value);
CAMLprim value caml_mm256_shuffle_epi8(value, value);
CAMLprim value caml_mm256_srai_epi16(value, value);
CAMLprim value caml_mm256_srli_epi16(value, value);
CAMLprim value caml_mm256_cmpgt_epi16(value, value);
CAMLprim value caml_mm256_movemask_epi8(value);
CAMLprim value caml_mm256_unpacklo_epi8(value, value);
CAMLprim value caml_mm256_unpacklo_epi64(value, value);
CAMLprim value caml_mm256_unpackhi_epi64(value, value);
CAMLprim value caml_mm256_inserti128_si256_dyn(value, value, value);
CAMLprim value caml_mm256_extracti128_si256_dyn(value, value);
CAMLprim value caml_mm256_blend_epi16_dyn(value, value, value);
CAMLprim value caml_mm256_blend_epi32_dyn(value, value, value);
CAMLprim value caml_mm256_moveldup_ps(value);
}

/* ==================================================================== */
#if defined(HAS_AVX)

/* -------------------------------------------------------------------- */
extern value value_of_w256(__m256i x);
extern __m256i w256_of_value(value x);

/* -------------------------------------------------------------------- */
extern value value_of_w128(__m128i x);
extern __m128i w128_of_value(value x);

/* -------------------------------------------------------------------- */
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
struct M128i {
  typedef __m128i type;

  static inline type ofocaml(value v) {
    return w128_of_value(v);
  }

  static inline value toocaml(type v) {
    return value_of_w128(v);
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
struct Int32 {
  typedef long type;

  static inline type ofocaml(value v) {
    return Int32_val(v);
  }

  static inline value toocaml(type v) {
    return caml_copy_int32(v);
  }
};

/* -------------------------------------------------------------------- */
struct Int64 {
  typedef long type;

  static inline type ofocaml(value v) {
    return Int64_val(v);
  }

  static inline value toocaml(type v) {
    return caml_copy_int64(v);
  }
};

/* -------------------------------------------------------------------- */
template <auto F, typename U, typename T>
static value bind(value arg) {
  CAMLparam1(arg);
  typename T::type varg = T::ofocaml(arg);
  CAMLreturn(U::toocaml(F(varg)));
}

/* -------------------------------------------------------------------- */
template <auto F, typename U, typename T1, typename T2>
static value bind(value arg1, value arg2) {
  CAMLparam2(arg1, arg2);
  typename T1::type varg1 = T1::ofocaml(arg1);
  typename T2::type varg2 = T2::ofocaml(arg2);
  CAMLreturn(U::toocaml(F(varg1, varg2)));
}

/* -------------------------------------------------------------------- */
template <auto F, typename U, typename T1, typename T2, typename T3>
static value bind(value arg1, value arg2, value arg3) {
  CAMLparam3(arg1, arg2, arg3);
  typename T1::type varg1 = T1::ofocaml(arg1);
  typename T2::type varg2 = T2::ofocaml(arg2);
  typename T3::type varg3 = T3::ofocaml(arg3);
  CAMLreturn(U::toocaml(F(varg1, varg2, varg3)));
}

/* -------------------------------------------------------------------- */
# define BIND1(F, U, T)                                \
CAMLprim value caml_##F(value a) {                     \
  return bind<_##F, U, T>(a);                          \
}

/* -------------------------------------------------------------------- */
# define BIND2(F, U, T1, T2)                           \
CAMLprim value caml_##F(value a, value b) {            \
  return bind<_##F, U, T1, T2>(a, b);                  \
}

/* -------------------------------------------------------------------- */
# define BIND3(F, U, T1, T2, T3)                       \
CAMLprim value caml_##F(value a, value b, value c) {   \
  return bind<_##F, U, T1, T2, T3>(a, b, c);           \
}

/* ==================================================================== */
#else

/* -------------------------------------------------------------------- */
# define BIND1(F, U, T)                                \
CAMLprim value caml_##F(value a) {                     \
  CAMLparam1(a);                                       \
  caml_failwith("not implemented: " #F);               \
  CAMLreturn(Val_unit);                                \
}

/* -------------------------------------------------------------------- */
# define BIND2(F, U, T1, T2)                           \
CAMLprim value caml_##F(value a, value b) {            \
  CAMLparam2(a, b);                                    \
  caml_failwith("not implemented: " #F);               \
  CAMLreturn(Val_unit);                                \
}

/* -------------------------------------------------------------------- */
# define BIND3(F, U, T1, T2, T3)                       \
CAMLprim value caml_##F(value a, value b, value c) {   \
  CAMLparam3(a, b, c);                                 \
  caml_failwith("not implemented: " #F);               \
  CAMLreturn(Val_unit);                                \
}

#endif /* defined(HAS_AVX) */

#define BIND_256x2_256(F) BIND2(F, M256i, M256i, M256i)
#define BIND_256x3_256(F) BIND3(F, M256i, M256i, M256i, M256i)

#endif /* !AVX2_RUNTIME__ */
