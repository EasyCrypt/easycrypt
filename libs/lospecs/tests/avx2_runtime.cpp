/* ==================================================================== */
#include <x86/avx2.h>
#include "avx2_runtime.h"

/* -------------------------------------------------------------------- */
#include <stdint.h>

/* -------------------------------------------------------------------- */
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>

/* ==================================================================== */
extern "C" CAMLprim value m64_of_32x2(value lohi) {
  CAMLparam1(lohi);

  const uint32_t lo = (uint32_t) Int32_val(Field(lohi, 0));
  const uint32_t hi = (uint32_t) Int32_val(Field(lohi, 1));

  const uint64_t out = ((uint64_t) lo) | (((uint64_t) hi) << 32);

  CAMLreturn(caml_copy_int64((int64_t) out));
}

/* -------------------------------------------------------------------- */
extern "C" CAMLprim value m64_to_32x2(value lohi) {
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
extern "C" CAMLprim value m32_of_16x2(value lohi) {
  CAMLparam1(lohi);

  const uint16_t lo = (uint16_t) Int_val(Field(lohi, 0));
  const uint16_t hi = (uint16_t) Int_val(Field(lohi, 1));

  const uint32_t out = ((uint32_t) lo) | (((uint32_t) hi) << 16);

  CAMLreturn(caml_copy_int32((int32_t) out));
}

/* -------------------------------------------------------------------- */
extern "C" CAMLprim value m32_to_16x2(value lohi) {
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
extern "C" CAMLprim value m16_of_8x2(value lohi) {
  CAMLparam1(lohi);

  const uint8_t lo = (uint8_t) Int_val(Field(lohi, 0));
  const uint8_t hi = (uint8_t) Int_val(Field(lohi, 1));

  const uint16_t out = ((uint16_t) lo) | (((uint16_t) hi) << 8);

  CAMLreturn(Val_int(out));
}

/* -------------------------------------------------------------------- */
 extern "C" CAMLprim value m16_to_8x2(value lohi) {
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

/* ==================================================================== */
#if defined(HAS_AVX)
/* -------------------------------------------------------------------- */
value value_of_w256(simde__m256i x) {
  CAMLparam0();
  CAMLlocal1(out);

  out = caml_alloc_tuple(4);
  Store_field(out, 0, caml_copy_int64(simde_mm256_extract_epi64(x, 0)));
  Store_field(out, 1, caml_copy_int64(simde_mm256_extract_epi64(x, 1)));
  Store_field(out, 2, caml_copy_int64(simde_mm256_extract_epi64(x, 2)));
  Store_field(out, 3, caml_copy_int64(simde_mm256_extract_epi64(x, 3)));

  CAMLreturn(out);
}

/* -------------------------------------------------------------------- */
simde__m256i w256_of_value(value x) {
  CAMLparam1(x);

  simde__m256i out = simde_mm256_set_epi64x(
    Int64_val(Field(x, 3)),
    Int64_val(Field(x, 2)),
    Int64_val(Field(x, 1)),
    Int64_val(Field(x, 0))
  );

  CAMLreturnT(simde__m256i, out);
}

/* -------------------------------------------------------------------- */
value value_of_w128(simde__m128i x) {
  CAMLparam0();
  CAMLlocal1(out);

  out = caml_alloc_tuple(2);
  Store_field(out, 0, caml_copy_int64(simde_mm_extract_epi64(x, 0)));
  Store_field(out, 1, caml_copy_int64(simde_mm_extract_epi64(x, 1)));

  CAMLreturn(out);
}

/* -------------------------------------------------------------------- */
simde__m128i w128_of_value(value x) {
  CAMLparam1(x);

  simde__m128i out = simde_mm_set_epi64x(
    Int64_val(Field(x, 1)),
    Int64_val(Field(x, 0))
  );

  CAMLreturnT(simde__m128i, out);
}

/* -------------------------------------------------------------------- */
simde__m256i simde_mm256_inserti128_si256_dyn(simde__m256i a, simde__m128i b, const int imm8) {
  switch (imm8 & 0x01) {
    case 0:
    return simde_mm256_inserti128_si256(a, b, 0);
    case 1:
    return simde_mm256_inserti128_si256(a, b, 1);
  }
  abort();
}

/* -------------------------------------------------------------------- */
simde__m128i simde_mm256_extracti128_si256_dyn(simde__m256i a, const int imm8) {
  switch (imm8 & 0x01) {
    case 0:
    return simde_mm256_extracti128_si256(a, 0);
    case 1:
    return simde_mm256_extracti128_si256(a, 1);
  }
  abort();
}

/* -------------------------------------------------------------------- */
simde__m256i simde_mm256_blend_epi16_dyn(simde__m256i a, simde__m256i b, const int imm8) {
#define CASE(I) case I: return simde_mm256_blend_epi16(a, b, I)

  /*
   * for i in range(0, 256, 4):
   *   print('; '.join(f'CASE(0x{j:02x})' for j in range(i, i+4)) + ';')
   */
  switch (imm8 & 0xff) {
    CASE(0x00); CASE(0x01); CASE(0x02); CASE(0x03);
    CASE(0x04); CASE(0x05); CASE(0x06); CASE(0x07);
    CASE(0x08); CASE(0x09); CASE(0x0a); CASE(0x0b);
    CASE(0x0c); CASE(0x0d); CASE(0x0e); CASE(0x0f);
    CASE(0x10); CASE(0x11); CASE(0x12); CASE(0x13);
    CASE(0x14); CASE(0x15); CASE(0x16); CASE(0x17);
    CASE(0x18); CASE(0x19); CASE(0x1a); CASE(0x1b);
    CASE(0x1c); CASE(0x1d); CASE(0x1e); CASE(0x1f);
    CASE(0x20); CASE(0x21); CASE(0x22); CASE(0x23);
    CASE(0x24); CASE(0x25); CASE(0x26); CASE(0x27);
    CASE(0x28); CASE(0x29); CASE(0x2a); CASE(0x2b);
    CASE(0x2c); CASE(0x2d); CASE(0x2e); CASE(0x2f);
    CASE(0x30); CASE(0x31); CASE(0x32); CASE(0x33);
    CASE(0x34); CASE(0x35); CASE(0x36); CASE(0x37);
    CASE(0x38); CASE(0x39); CASE(0x3a); CASE(0x3b);
    CASE(0x3c); CASE(0x3d); CASE(0x3e); CASE(0x3f);
    CASE(0x40); CASE(0x41); CASE(0x42); CASE(0x43);
    CASE(0x44); CASE(0x45); CASE(0x46); CASE(0x47);
    CASE(0x48); CASE(0x49); CASE(0x4a); CASE(0x4b);
    CASE(0x4c); CASE(0x4d); CASE(0x4e); CASE(0x4f);
    CASE(0x50); CASE(0x51); CASE(0x52); CASE(0x53);
    CASE(0x54); CASE(0x55); CASE(0x56); CASE(0x57);
    CASE(0x58); CASE(0x59); CASE(0x5a); CASE(0x5b);
    CASE(0x5c); CASE(0x5d); CASE(0x5e); CASE(0x5f);
    CASE(0x60); CASE(0x61); CASE(0x62); CASE(0x63);
    CASE(0x64); CASE(0x65); CASE(0x66); CASE(0x67);
    CASE(0x68); CASE(0x69); CASE(0x6a); CASE(0x6b);
    CASE(0x6c); CASE(0x6d); CASE(0x6e); CASE(0x6f);
    CASE(0x70); CASE(0x71); CASE(0x72); CASE(0x73);
    CASE(0x74); CASE(0x75); CASE(0x76); CASE(0x77);
    CASE(0x78); CASE(0x79); CASE(0x7a); CASE(0x7b);
    CASE(0x7c); CASE(0x7d); CASE(0x7e); CASE(0x7f);
    CASE(0x80); CASE(0x81); CASE(0x82); CASE(0x83);
    CASE(0x84); CASE(0x85); CASE(0x86); CASE(0x87);
    CASE(0x88); CASE(0x89); CASE(0x8a); CASE(0x8b);
    CASE(0x8c); CASE(0x8d); CASE(0x8e); CASE(0x8f);
    CASE(0x90); CASE(0x91); CASE(0x92); CASE(0x93);
    CASE(0x94); CASE(0x95); CASE(0x96); CASE(0x97);
    CASE(0x98); CASE(0x99); CASE(0x9a); CASE(0x9b);
    CASE(0x9c); CASE(0x9d); CASE(0x9e); CASE(0x9f);
    CASE(0xa0); CASE(0xa1); CASE(0xa2); CASE(0xa3);
    CASE(0xa4); CASE(0xa5); CASE(0xa6); CASE(0xa7);
    CASE(0xa8); CASE(0xa9); CASE(0xaa); CASE(0xab);
    CASE(0xac); CASE(0xad); CASE(0xae); CASE(0xaf);
    CASE(0xb0); CASE(0xb1); CASE(0xb2); CASE(0xb3);
    CASE(0xb4); CASE(0xb5); CASE(0xb6); CASE(0xb7);
    CASE(0xb8); CASE(0xb9); CASE(0xba); CASE(0xbb);
    CASE(0xbc); CASE(0xbd); CASE(0xbe); CASE(0xbf);
    CASE(0xc0); CASE(0xc1); CASE(0xc2); CASE(0xc3);
    CASE(0xc4); CASE(0xc5); CASE(0xc6); CASE(0xc7);
    CASE(0xc8); CASE(0xc9); CASE(0xca); CASE(0xcb);
    CASE(0xcc); CASE(0xcd); CASE(0xce); CASE(0xcf);
    CASE(0xd0); CASE(0xd1); CASE(0xd2); CASE(0xd3);
    CASE(0xd4); CASE(0xd5); CASE(0xd6); CASE(0xd7);
    CASE(0xd8); CASE(0xd9); CASE(0xda); CASE(0xdb);
    CASE(0xdc); CASE(0xdd); CASE(0xde); CASE(0xdf);
    CASE(0xe0); CASE(0xe1); CASE(0xe2); CASE(0xe3);
    CASE(0xe4); CASE(0xe5); CASE(0xe6); CASE(0xe7);
    CASE(0xe8); CASE(0xe9); CASE(0xea); CASE(0xeb);
    CASE(0xec); CASE(0xed); CASE(0xee); CASE(0xef);
    CASE(0xf0); CASE(0xf1); CASE(0xf2); CASE(0xf3);
    CASE(0xf4); CASE(0xf5); CASE(0xf6); CASE(0xf7);
    CASE(0xf8); CASE(0xf9); CASE(0xfa); CASE(0xfb);
    CASE(0xfc); CASE(0xfd); CASE(0xfe); CASE(0xff);
  }
  abort();
#undef CASE
}

/* -------------------------------------------------------------------- */
simde__m256i simde_mm256_blend_epi32_dyn(simde__m256i a, simde__m256i b, const int imm8) {
#define CASE(I) case I: return simde_mm256_blend_epi32(a, b, I)

  /*
   * for i in range(0, 256, 4):
   *   print('; '.join(f'CASE(0x{j:02x})' for j in range(i, i+4)) + ';')
   */
  switch (imm8 & 0xff) {
    CASE(0x00); CASE(0x01); CASE(0x02); CASE(0x03);
    CASE(0x04); CASE(0x05); CASE(0x06); CASE(0x07);
    CASE(0x08); CASE(0x09); CASE(0x0a); CASE(0x0b);
    CASE(0x0c); CASE(0x0d); CASE(0x0e); CASE(0x0f);
    CASE(0x10); CASE(0x11); CASE(0x12); CASE(0x13);
    CASE(0x14); CASE(0x15); CASE(0x16); CASE(0x17);
    CASE(0x18); CASE(0x19); CASE(0x1a); CASE(0x1b);
    CASE(0x1c); CASE(0x1d); CASE(0x1e); CASE(0x1f);
    CASE(0x20); CASE(0x21); CASE(0x22); CASE(0x23);
    CASE(0x24); CASE(0x25); CASE(0x26); CASE(0x27);
    CASE(0x28); CASE(0x29); CASE(0x2a); CASE(0x2b);
    CASE(0x2c); CASE(0x2d); CASE(0x2e); CASE(0x2f);
    CASE(0x30); CASE(0x31); CASE(0x32); CASE(0x33);
    CASE(0x34); CASE(0x35); CASE(0x36); CASE(0x37);
    CASE(0x38); CASE(0x39); CASE(0x3a); CASE(0x3b);
    CASE(0x3c); CASE(0x3d); CASE(0x3e); CASE(0x3f);
    CASE(0x40); CASE(0x41); CASE(0x42); CASE(0x43);
    CASE(0x44); CASE(0x45); CASE(0x46); CASE(0x47);
    CASE(0x48); CASE(0x49); CASE(0x4a); CASE(0x4b);
    CASE(0x4c); CASE(0x4d); CASE(0x4e); CASE(0x4f);
    CASE(0x50); CASE(0x51); CASE(0x52); CASE(0x53);
    CASE(0x54); CASE(0x55); CASE(0x56); CASE(0x57);
    CASE(0x58); CASE(0x59); CASE(0x5a); CASE(0x5b);
    CASE(0x5c); CASE(0x5d); CASE(0x5e); CASE(0x5f);
    CASE(0x60); CASE(0x61); CASE(0x62); CASE(0x63);
    CASE(0x64); CASE(0x65); CASE(0x66); CASE(0x67);
    CASE(0x68); CASE(0x69); CASE(0x6a); CASE(0x6b);
    CASE(0x6c); CASE(0x6d); CASE(0x6e); CASE(0x6f);
    CASE(0x70); CASE(0x71); CASE(0x72); CASE(0x73);
    CASE(0x74); CASE(0x75); CASE(0x76); CASE(0x77);
    CASE(0x78); CASE(0x79); CASE(0x7a); CASE(0x7b);
    CASE(0x7c); CASE(0x7d); CASE(0x7e); CASE(0x7f);
    CASE(0x80); CASE(0x81); CASE(0x82); CASE(0x83);
    CASE(0x84); CASE(0x85); CASE(0x86); CASE(0x87);
    CASE(0x88); CASE(0x89); CASE(0x8a); CASE(0x8b);
    CASE(0x8c); CASE(0x8d); CASE(0x8e); CASE(0x8f);
    CASE(0x90); CASE(0x91); CASE(0x92); CASE(0x93);
    CASE(0x94); CASE(0x95); CASE(0x96); CASE(0x97);
    CASE(0x98); CASE(0x99); CASE(0x9a); CASE(0x9b);
    CASE(0x9c); CASE(0x9d); CASE(0x9e); CASE(0x9f);
    CASE(0xa0); CASE(0xa1); CASE(0xa2); CASE(0xa3);
    CASE(0xa4); CASE(0xa5); CASE(0xa6); CASE(0xa7);
    CASE(0xa8); CASE(0xa9); CASE(0xaa); CASE(0xab);
    CASE(0xac); CASE(0xad); CASE(0xae); CASE(0xaf);
    CASE(0xb0); CASE(0xb1); CASE(0xb2); CASE(0xb3);
    CASE(0xb4); CASE(0xb5); CASE(0xb6); CASE(0xb7);
    CASE(0xb8); CASE(0xb9); CASE(0xba); CASE(0xbb);
    CASE(0xbc); CASE(0xbd); CASE(0xbe); CASE(0xbf);
    CASE(0xc0); CASE(0xc1); CASE(0xc2); CASE(0xc3);
    CASE(0xc4); CASE(0xc5); CASE(0xc6); CASE(0xc7);
    CASE(0xc8); CASE(0xc9); CASE(0xca); CASE(0xcb);
    CASE(0xcc); CASE(0xcd); CASE(0xce); CASE(0xcf);
    CASE(0xd0); CASE(0xd1); CASE(0xd2); CASE(0xd3);
    CASE(0xd4); CASE(0xd5); CASE(0xd6); CASE(0xd7);
    CASE(0xd8); CASE(0xd9); CASE(0xda); CASE(0xdb);
    CASE(0xdc); CASE(0xdd); CASE(0xde); CASE(0xdf);
    CASE(0xe0); CASE(0xe1); CASE(0xe2); CASE(0xe3);
    CASE(0xe4); CASE(0xe5); CASE(0xe6); CASE(0xe7);
    CASE(0xe8); CASE(0xe9); CASE(0xea); CASE(0xeb);
    CASE(0xec); CASE(0xed); CASE(0xee); CASE(0xef);
    CASE(0xf0); CASE(0xf1); CASE(0xf2); CASE(0xf3);
    CASE(0xf4); CASE(0xf5); CASE(0xf6); CASE(0xf7);
    CASE(0xf8); CASE(0xf9); CASE(0xfa); CASE(0xfb);
    CASE(0xfc); CASE(0xfd); CASE(0xfe); CASE(0xff);
  }
  abort();
#undef CASE
}

/* -------------------------------------------------------------------- */
simde__m256i simde_mm256_permute4x64_epi64_dyn(simde__m256i a, const int imm8) {
#define CASE(I) case I: return simde_mm256_permute4x64_epi64(a, I)

  /*
   * for i in range(0, 256, 4):
   *   print('; '.join(f'CASE(0x{j:02x})' for j in range(i, i+4)) + ';')
   */
  switch (imm8 & 0xff) {
    CASE(0x00); CASE(0x01); CASE(0x02); CASE(0x03);
    CASE(0x04); CASE(0x05); CASE(0x06); CASE(0x07);
    CASE(0x08); CASE(0x09); CASE(0x0a); CASE(0x0b);
    CASE(0x0c); CASE(0x0d); CASE(0x0e); CASE(0x0f);
    CASE(0x10); CASE(0x11); CASE(0x12); CASE(0x13);
    CASE(0x14); CASE(0x15); CASE(0x16); CASE(0x17);
    CASE(0x18); CASE(0x19); CASE(0x1a); CASE(0x1b);
    CASE(0x1c); CASE(0x1d); CASE(0x1e); CASE(0x1f);
    CASE(0x20); CASE(0x21); CASE(0x22); CASE(0x23);
    CASE(0x24); CASE(0x25); CASE(0x26); CASE(0x27);
    CASE(0x28); CASE(0x29); CASE(0x2a); CASE(0x2b);
    CASE(0x2c); CASE(0x2d); CASE(0x2e); CASE(0x2f);
    CASE(0x30); CASE(0x31); CASE(0x32); CASE(0x33);
    CASE(0x34); CASE(0x35); CASE(0x36); CASE(0x37);
    CASE(0x38); CASE(0x39); CASE(0x3a); CASE(0x3b);
    CASE(0x3c); CASE(0x3d); CASE(0x3e); CASE(0x3f);
    CASE(0x40); CASE(0x41); CASE(0x42); CASE(0x43);
    CASE(0x44); CASE(0x45); CASE(0x46); CASE(0x47);
    CASE(0x48); CASE(0x49); CASE(0x4a); CASE(0x4b);
    CASE(0x4c); CASE(0x4d); CASE(0x4e); CASE(0x4f);
    CASE(0x50); CASE(0x51); CASE(0x52); CASE(0x53);
    CASE(0x54); CASE(0x55); CASE(0x56); CASE(0x57);
    CASE(0x58); CASE(0x59); CASE(0x5a); CASE(0x5b);
    CASE(0x5c); CASE(0x5d); CASE(0x5e); CASE(0x5f);
    CASE(0x60); CASE(0x61); CASE(0x62); CASE(0x63);
    CASE(0x64); CASE(0x65); CASE(0x66); CASE(0x67);
    CASE(0x68); CASE(0x69); CASE(0x6a); CASE(0x6b);
    CASE(0x6c); CASE(0x6d); CASE(0x6e); CASE(0x6f);
    CASE(0x70); CASE(0x71); CASE(0x72); CASE(0x73);
    CASE(0x74); CASE(0x75); CASE(0x76); CASE(0x77);
    CASE(0x78); CASE(0x79); CASE(0x7a); CASE(0x7b);
    CASE(0x7c); CASE(0x7d); CASE(0x7e); CASE(0x7f);
    CASE(0x80); CASE(0x81); CASE(0x82); CASE(0x83);
    CASE(0x84); CASE(0x85); CASE(0x86); CASE(0x87);
    CASE(0x88); CASE(0x89); CASE(0x8a); CASE(0x8b);
    CASE(0x8c); CASE(0x8d); CASE(0x8e); CASE(0x8f);
    CASE(0x90); CASE(0x91); CASE(0x92); CASE(0x93);
    CASE(0x94); CASE(0x95); CASE(0x96); CASE(0x97);
    CASE(0x98); CASE(0x99); CASE(0x9a); CASE(0x9b);
    CASE(0x9c); CASE(0x9d); CASE(0x9e); CASE(0x9f);
    CASE(0xa0); CASE(0xa1); CASE(0xa2); CASE(0xa3);
    CASE(0xa4); CASE(0xa5); CASE(0xa6); CASE(0xa7);
    CASE(0xa8); CASE(0xa9); CASE(0xaa); CASE(0xab);
    CASE(0xac); CASE(0xad); CASE(0xae); CASE(0xaf);
    CASE(0xb0); CASE(0xb1); CASE(0xb2); CASE(0xb3);
    CASE(0xb4); CASE(0xb5); CASE(0xb6); CASE(0xb7);
    CASE(0xb8); CASE(0xb9); CASE(0xba); CASE(0xbb);
    CASE(0xbc); CASE(0xbd); CASE(0xbe); CASE(0xbf);
    CASE(0xc0); CASE(0xc1); CASE(0xc2); CASE(0xc3);
    CASE(0xc4); CASE(0xc5); CASE(0xc6); CASE(0xc7);
    CASE(0xc8); CASE(0xc9); CASE(0xca); CASE(0xcb);
    CASE(0xcc); CASE(0xcd); CASE(0xce); CASE(0xcf);
    CASE(0xd0); CASE(0xd1); CASE(0xd2); CASE(0xd3);
    CASE(0xd4); CASE(0xd5); CASE(0xd6); CASE(0xd7);
    CASE(0xd8); CASE(0xd9); CASE(0xda); CASE(0xdb);
    CASE(0xdc); CASE(0xdd); CASE(0xde); CASE(0xdf);
    CASE(0xe0); CASE(0xe1); CASE(0xe2); CASE(0xe3);
    CASE(0xe4); CASE(0xe5); CASE(0xe6); CASE(0xe7);
    CASE(0xe8); CASE(0xe9); CASE(0xea); CASE(0xeb);
    CASE(0xec); CASE(0xed); CASE(0xee); CASE(0xef);
    CASE(0xf0); CASE(0xf1); CASE(0xf2); CASE(0xf3);
    CASE(0xf4); CASE(0xf5); CASE(0xf6); CASE(0xf7);
    CASE(0xf8); CASE(0xf9); CASE(0xfa); CASE(0xfb);
    CASE(0xfc); CASE(0xfd); CASE(0xfe); CASE(0xff);
  }
  abort();
#undef CASE
}

/* -------------------------------------------------------------------- */
simde__m256i simde_mm256_permute2x128_si256_dyn(simde__m256i a, simde__m256i b, const int imm8) {
#define CASE(I) case I: return simde_mm256_permute2x128_si256(a, b, I)

  /*
   * for i in range(0, 256, 4):
   *   print('; '.join(f'CASE(0x{j:02x})' for j in range(i, i+4)) + ';')
   */
  switch (imm8 & 0xff) {
    CASE(0x00); CASE(0x01); CASE(0x02); CASE(0x03);
    CASE(0x04); CASE(0x05); CASE(0x06); CASE(0x07);
    CASE(0x08); CASE(0x09); CASE(0x0a); CASE(0x0b);
    CASE(0x0c); CASE(0x0d); CASE(0x0e); CASE(0x0f);
    CASE(0x10); CASE(0x11); CASE(0x12); CASE(0x13);
    CASE(0x14); CASE(0x15); CASE(0x16); CASE(0x17);
    CASE(0x18); CASE(0x19); CASE(0x1a); CASE(0x1b);
    CASE(0x1c); CASE(0x1d); CASE(0x1e); CASE(0x1f);
    CASE(0x20); CASE(0x21); CASE(0x22); CASE(0x23);
    CASE(0x24); CASE(0x25); CASE(0x26); CASE(0x27);
    CASE(0x28); CASE(0x29); CASE(0x2a); CASE(0x2b);
    CASE(0x2c); CASE(0x2d); CASE(0x2e); CASE(0x2f);
    CASE(0x30); CASE(0x31); CASE(0x32); CASE(0x33);
    CASE(0x34); CASE(0x35); CASE(0x36); CASE(0x37);
    CASE(0x38); CASE(0x39); CASE(0x3a); CASE(0x3b);
    CASE(0x3c); CASE(0x3d); CASE(0x3e); CASE(0x3f);
    CASE(0x40); CASE(0x41); CASE(0x42); CASE(0x43);
    CASE(0x44); CASE(0x45); CASE(0x46); CASE(0x47);
    CASE(0x48); CASE(0x49); CASE(0x4a); CASE(0x4b);
    CASE(0x4c); CASE(0x4d); CASE(0x4e); CASE(0x4f);
    CASE(0x50); CASE(0x51); CASE(0x52); CASE(0x53);
    CASE(0x54); CASE(0x55); CASE(0x56); CASE(0x57);
    CASE(0x58); CASE(0x59); CASE(0x5a); CASE(0x5b);
    CASE(0x5c); CASE(0x5d); CASE(0x5e); CASE(0x5f);
    CASE(0x60); CASE(0x61); CASE(0x62); CASE(0x63);
    CASE(0x64); CASE(0x65); CASE(0x66); CASE(0x67);
    CASE(0x68); CASE(0x69); CASE(0x6a); CASE(0x6b);
    CASE(0x6c); CASE(0x6d); CASE(0x6e); CASE(0x6f);
    CASE(0x70); CASE(0x71); CASE(0x72); CASE(0x73);
    CASE(0x74); CASE(0x75); CASE(0x76); CASE(0x77);
    CASE(0x78); CASE(0x79); CASE(0x7a); CASE(0x7b);
    CASE(0x7c); CASE(0x7d); CASE(0x7e); CASE(0x7f);
    CASE(0x80); CASE(0x81); CASE(0x82); CASE(0x83);
    CASE(0x84); CASE(0x85); CASE(0x86); CASE(0x87);
    CASE(0x88); CASE(0x89); CASE(0x8a); CASE(0x8b);
    CASE(0x8c); CASE(0x8d); CASE(0x8e); CASE(0x8f);
    CASE(0x90); CASE(0x91); CASE(0x92); CASE(0x93);
    CASE(0x94); CASE(0x95); CASE(0x96); CASE(0x97);
    CASE(0x98); CASE(0x99); CASE(0x9a); CASE(0x9b);
    CASE(0x9c); CASE(0x9d); CASE(0x9e); CASE(0x9f);
    CASE(0xa0); CASE(0xa1); CASE(0xa2); CASE(0xa3);
    CASE(0xa4); CASE(0xa5); CASE(0xa6); CASE(0xa7);
    CASE(0xa8); CASE(0xa9); CASE(0xaa); CASE(0xab);
    CASE(0xac); CASE(0xad); CASE(0xae); CASE(0xaf);
    CASE(0xb0); CASE(0xb1); CASE(0xb2); CASE(0xb3);
    CASE(0xb4); CASE(0xb5); CASE(0xb6); CASE(0xb7);
    CASE(0xb8); CASE(0xb9); CASE(0xba); CASE(0xbb);
    CASE(0xbc); CASE(0xbd); CASE(0xbe); CASE(0xbf);
    CASE(0xc0); CASE(0xc1); CASE(0xc2); CASE(0xc3);
    CASE(0xc4); CASE(0xc5); CASE(0xc6); CASE(0xc7);
    CASE(0xc8); CASE(0xc9); CASE(0xca); CASE(0xcb);
    CASE(0xcc); CASE(0xcd); CASE(0xce); CASE(0xcf);
    CASE(0xd0); CASE(0xd1); CASE(0xd2); CASE(0xd3);
    CASE(0xd4); CASE(0xd5); CASE(0xd6); CASE(0xd7);
    CASE(0xd8); CASE(0xd9); CASE(0xda); CASE(0xdb);
    CASE(0xdc); CASE(0xdd); CASE(0xde); CASE(0xdf);
    CASE(0xe0); CASE(0xe1); CASE(0xe2); CASE(0xe3);
    CASE(0xe4); CASE(0xe5); CASE(0xe6); CASE(0xe7);
    CASE(0xe8); CASE(0xe9); CASE(0xea); CASE(0xeb);
    CASE(0xec); CASE(0xed); CASE(0xee); CASE(0xef);
    CASE(0xf0); CASE(0xf1); CASE(0xf2); CASE(0xf3);
    CASE(0xf4); CASE(0xf5); CASE(0xf6); CASE(0xf7);
    CASE(0xf8); CASE(0xf9); CASE(0xfa); CASE(0xfb);
    CASE(0xfc); CASE(0xfd); CASE(0xfe); CASE(0xff);
  }
  abort();
#undef CASE
}

/* -------------------------------------------------------------------- */
simde__m256i simde_mm256_moveldup_ps_dyn(simde__m256i a) {
   return (simde__m256i)simde_mm256_moveldup_ps((simde__m256)a);
}


#endif

extern "C" {
BIND_256x2_256(simde_mm256_permutevar8x32_epi32);
BIND2(simde_mm256_permute4x64_epi64_dyn, M256i, M256i, Long);
BIND3(simde_mm256_permute2x128_si256_dyn, M256i, M256i, M256i, Long);

BIND_256x2_256(simde_mm256_and_si256);
BIND_256x2_256(simde_mm256_andnot_si256);
BIND_256x2_256(simde_mm256_add_epi8);
BIND_256x2_256(simde_mm256_add_epi16);
BIND_256x2_256(simde_mm256_sub_epi8);
BIND_256x2_256(simde_mm256_sub_epi16);
BIND_256x2_256(simde_mm256_maddubs_epi16);
BIND_256x2_256(simde_mm256_packus_epi16);
BIND_256x2_256(simde_mm256_packs_epi16);
BIND_256x2_256(simde_mm256_mulhi_epi16);
BIND_256x2_256(simde_mm256_mulhi_epu16);
BIND_256x2_256(simde_mm256_mulhrs_epi16);

BIND_256x2_256(simde_mm256_shuffle_epi8);
BIND_256x2_256(simde_mm256_cmpgt_epi16);
BIND_256x2_256(simde_mm256_unpacklo_epi8);
BIND_256x2_256(simde_mm256_unpacklo_epi64);
BIND_256x2_256(simde_mm256_unpackhi_epi64);

BIND2(simde_mm256_srai_epi16, M256i, M256i, Long);
BIND2(simde_mm256_srli_epi16, M256i, M256i, Long);

BIND1(simde_mm256_movemask_epi8, Int32, M256i);
BIND1(simde_mm256_moveldup_ps_dyn, M256i, M256i); 

BIND3(simde_mm256_blend_epi16_dyn, M256i, M256i, M256i, Long);
BIND3(simde_mm256_blend_epi32_dyn, M256i, M256i, M256i, Long);


BIND3(simde_mm256_inserti128_si256_dyn, M256i, M256i, M128i, Long);
BIND2(simde_mm256_extracti128_si256_dyn, M128i, M256i, Long);
}
