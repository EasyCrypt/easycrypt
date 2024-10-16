(* -------------------------------------------------------------- *)
type m128
type m256

(* -------------------------------------------------------------- *)
type size = [`U8 | `U16 | `U32 | `U64]
type endianess = [`Little | `Big]

val pp_bytes : size:size -> Format.formatter -> bytes -> unit

(* -------------------------------------------------------------- *)
type 'a pair = 'a * 'a
type 'a quad = 'a * 'a * 'a * 'a

(* -------------------------------------------------------------- *)
type m64x2 = int64 pair
type m64x4 = int64 quad
type m32x4 = int32 pair pair
type m32x8 = int32 pair quad
type m16x8 = int pair pair pair
type m16x16 = int pair pair quad
type m8x16 = char pair pair pair pair
type m8x32 = char pair pair pair quad

(* -------------------------------------------------------------- *)
val m64_to_32x2 : int64 -> int32 pair
val m32_to_16x2 : int32 -> int pair
val m16_to_8x2  : int -> char pair

(* -------------------------------------------------------------- *)
val m64_of_32x2 : int32 pair -> int64
val m32_of_16x2 : int pair -> int32
val m16_of_8x2  : char pair -> int

(* -------------------------------------------------------------- *)
module M256 : sig
  val oftuple_64 : m64x4 -> m256
  val totuple_64 : m256 -> m64x4

  val oftuple_32 : m32x8 -> m256
  val totuple_32 : m256 -> m32x8

  val oftuple_16 : m16x16 -> m256
  val totuple_16 : m256 -> m16x16

  val oftuple_8 : m8x32 -> m256
  val totuple_8 : m256 -> m8x32      

  val to_bytes : endianess:endianess -> m256 -> bytes
  val of_bytes : endianess:endianess -> bytes -> m256

  val random : unit -> m256

  val pp : size:size -> endianess:endianess -> Format.formatter -> m256 -> unit
end

(* -------------------------------------------------------------- *)
module M128 : sig
  val oftuple_64 : m64x2 -> m128
  val totuple_64 : m128 -> m64x2

  val oftuple_32 : m32x4 -> m128
  val totuple_32 : m128 -> m32x4

  val oftuple_16 : m16x8 -> m128
  val totuple_16 : m128 -> m16x8

  val oftuple_8 : m8x16 -> m128
  val totuple_8 : m128 -> m8x16      

  val to_bytes : endianess:endianess -> m128 -> bytes
  val of_bytes : endianess:endianess -> bytes -> m128

  val random : unit -> m128

  val pp : size:size -> endianess:endianess -> Format.formatter -> m128 -> unit
end

(* -------------------------------------------------------------- *)
val mm256_and_si256 : m256 -> m256 -> m256
val mm256_andnot_si256 : m256 -> m256 -> m256
val mm256_add_epi8 : m256 -> m256 -> m256
val mm256_add_epi16 : m256 -> m256 -> m256
val mm256_sub_epi8 : m256 -> m256 -> m256
val mm256_sub_epi16 : m256 -> m256 -> m256
val mm256_mulhi_epu16 : m256 -> m256 -> m256
val mm256_mulhrs_epi16 : m256 -> m256 -> m256
val mm256_packus_epi16 : m256 -> m256 -> m256
val mm256_packs_epi16 : m256 -> m256 -> m256
val mm256_maddubs_epi16 : m256 -> m256 -> m256
val mm256_permutevar8x32_epi32 : m256 -> m256 -> m256
val mm256_permute4x64_epi64 : m256 -> int -> m256
val mm256_shuffle_epi8 : m256 -> m256 -> m256
val mm256_srai_epi16 : m256 -> int -> m256
val mm256_srli_epi16 : m256 -> int -> m256
val mm256_cmpgt_epi16 : m256 -> m256 -> m256
val mm256_movemask_epi8 : m256 -> int32
val mm256_unpacklo_epi8 : m256 -> m256 -> m256
val mm256_blend_epi16 : m256 -> m256 -> int -> m256
val mm256_inserti128_si256 : m256 -> m128 -> int -> m256
val mm256_extracti128_si256 : m256 -> int -> m128
