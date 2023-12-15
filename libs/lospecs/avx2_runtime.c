/* -------------------------------------------------------------------- */
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>

/* -------------------------------------------------------------------- */
#include <stdint.h>
#include <immintrin.h>

/* -------------------------------------------------------------------- */
CAMLprim value m64_of_32x2(value lohi) {
  CAMLparam1(lohi);

  const uint32_t lo = (uint32_t) Int32_val(Field(lohi, 0));
  const uint32_t hi = (uint32_t) Int32_val(Field(lohi, 1));

  const uint64_t out = ((uint64_t) lo) | (((uint64_t) hi) << 32);

  CAMLreturn(caml_copy_int64((int64_t) out));
}

/* -------------------------------------------------------------------- */
CAMLprim value m64_to_32x2(value lohi) {
  CAMLparam1(lohi);
  CAMLlocal1(out);

  const uint64_t v = (uint64_t) Int64_val(lohi);

  const uint32_t lo = (v >>  0) & 0xffffffff;
  const uint32_t hi = (v >> 32) & 0xffffffff;

  out = caml_alloc_tuple(2);
  Field(out, 0) = caml_copy_int32(lo);
  Field(out, 1) = caml_copy_int32(hi);

  CAMLreturn(out);
}

/* -------------------------------------------------------------------- */
CAMLprim value m32_of_16x2(value lohi) {
  CAMLparam1(lohi);

  const uint16_t lo = (uint16_t) Int_val(Field(lohi, 0));
  const uint16_t hi = (uint16_t) Int_val(Field(lohi, 1));

  const uint32_t out = ((uint32_t) lo) | (((uint32_t) hi) << 16);

  CAMLreturn(caml_copy_int32((int32_t) out));
}

/* -------------------------------------------------------------------- */
CAMLprim value m32_to_16x2(value lohi) {
  CAMLparam1(lohi);
  CAMLlocal1(out);

  const uint32_t v = (uint32_t) Int32_val(lohi);

  const uint16_t lo = (v >>  0) & 0xffff;
  const uint16_t hi = (v >> 16) & 0xffff;

  out = caml_alloc_tuple(2);
  Field(out, 0) = Val_int(lo);
  Field(out, 1) = Val_int(hi);

  CAMLreturn(out);
}

/* -------------------------------------------------------------------- */
CAMLprim value m16_of_8x2(value lohi) {
  CAMLparam1(lohi);

  const uint8_t lo = (uint8_t) Int_val(Field(lohi, 0));
  const uint8_t hi = (uint8_t) Int_val(Field(lohi, 1));

  const uint16_t out = ((uint16_t) lo) | (((uint16_t) hi) << 8);

  CAMLreturn(Val_int(out));
}

/* -------------------------------------------------------------------- */
CAMLprim value m16_to_8x2(value lohi) {
  CAMLparam1(lohi);
  CAMLlocal1(out);

  const uint16_t v = (uint16_t) Int_val(lohi);

  const uint8_t lo = (v >> 0) & 0xff;
  const uint8_t hi = (v >> 8) & 0xff;

  out = caml_alloc_tuple(2);
  Field(out, 0) = Val_int(lo);
  Field(out, 1) = Val_int(hi);

  CAMLreturn(out);
}

/* -------------------------------------------------------------------- */
static value value_of_w256(__m256i x) {
  CAMLparam0();
  CAMLlocal1(out);

  out = caml_alloc_tuple(4);
  Store_field(out, 0, caml_copy_int64(_mm256_extract_epi64(x, 0)));
  Store_field(out, 1, caml_copy_int64(_mm256_extract_epi64(x, 1)));
  Store_field(out, 2, caml_copy_int64(_mm256_extract_epi64(x, 2)));
  Store_field(out, 3, caml_copy_int64(_mm256_extract_epi64(x, 3)));

  CAMLreturn(out);
}

/* -------------------------------------------------------------------- */
static __m256i w256_of_value(value x) {
  CAMLparam1(x);

  __m256i out = _mm256_set_epi64x(
    Int64_val(Field(x, 3)),
    Int64_val(Field(x, 2)),
    Int64_val(Field(x, 1)),
    Int64_val(Field(x, 0))
  );

  CAMLreturnT(__m256i, out);
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_mm256_add_epi16(value a, value b) {
  CAMLparam2(a, b);

  __m256i av = w256_of_value(a);
  __m256i bv = w256_of_value(b);

  CAMLreturn(value_of_w256(_mm256_add_epi16(av, bv)));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_mm256_sub_epi16(value a, value b) {
  CAMLparam2(a, b);

  __m256i av = w256_of_value(a);
  __m256i bv = w256_of_value(b);

  CAMLreturn(value_of_w256(_mm256_sub_epi16(av, bv)));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_mm256_and_si256(value a, value b) {
  CAMLparam2(a, b);

  __m256i av = w256_of_value(a);
  __m256i bv = w256_of_value(b);

  CAMLreturn(value_of_w256(_mm256_and_si256(av, bv)));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_mm256_mulhi_epu16(value a, value b) {
  CAMLparam2(a, b);

  __m256i av = w256_of_value(a);
  __m256i bv = w256_of_value(b);

  CAMLreturn(value_of_w256(_mm256_mulhi_epu16(av, bv)));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_mm256_mulhrs_epi16(value a, value b) {
  CAMLparam2(a, b);

  __m256i av = w256_of_value(a);
  __m256i bv = w256_of_value(b);

  CAMLreturn(value_of_w256(_mm256_mulhrs_epi16(av, bv)));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_mm256_packus_epi16(value a, value b) {
  CAMLparam2(a, b);

  __m256i av = w256_of_value(a);
  __m256i bv = w256_of_value(b);

  CAMLreturn(value_of_w256(_mm256_packus_epi16(av, bv)));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_mm256_maddubs_epi16(value a, value b) {
  CAMLparam2(a, b);

  __m256i av = w256_of_value(a);
  __m256i bv = w256_of_value(b);

  CAMLreturn(value_of_w256(_mm256_maddubs_epi16(av, bv)));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_mm256_permutexvar_epi32(value a, value b) {
  CAMLparam2(a, b);

  __m256i av = w256_of_value(a);
  __m256i bv = w256_of_value(b);

  CAMLreturn(value_of_w256(_mm256_permutexvar_epi32(av, bv)));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_mm256_srai_epi16(value a, value b) {
  CAMLparam2(a, b);

  __m256i av = w256_of_value(a);

  CAMLreturn(value_of_w256(_mm256_srai_epi16(av, Int_val(b))));
}
