(* -------------------------------------------------------------- *)
type m256

(* -------------------------------------------------------------- *)
type size = [`U8 | `U16 | `U32 | `U64]
type endianess = [`Little | `Big]

val pp_bytes : size:size -> Format.formatter -> bytes -> unit
val pp : size:size -> endianess:endianess -> Format.formatter -> m256 -> unit

(* -------------------------------------------------------------- *)
type 'a pair = 'a * 'a
type 'a quad = 'a * 'a * 'a * 'a

(* -------------------------------------------------------------- *)
type m64x4 = int64 quad
type m32x8 = int32 pair quad
type m16x16 = int pair pair quad
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
val oftuple_64 : m64x4 -> m256
val totuple_64 : m256 -> m64x4

(* -------------------------------------------------------------- *)
val oftuple_32 : m32x8 -> m256
val totuple_32 : m256 -> m32x8

(* -------------------------------------------------------------- *)
val oftuple_16 : m16x16 -> m256
val totuple_16 : m256 -> m16x16

(* -------------------------------------------------------------- *)
val oftuple_8 : m8x32 -> m256
val totuple_8 : m256 -> m8x32

(* -------------------------------------------------------------- *)
val to_bytes : endianess:endianess -> m256 -> bytes
val of_bytes : endianess:endianess -> bytes -> m256

(* -------------------------------------------------------------- *)
val random : unit -> m256

(* -------------------------------------------------------------- *)
val mm256_and_si256 : m256 -> m256 -> m256
val mm256_andnot_si256 : m256 -> m256 -> m256
val mm256_add_epi16 : m256 -> m256 -> m256
val mm256_sub_epi16 : m256 -> m256 -> m256
val mm256_mulhi_epu16 : m256 -> m256 -> m256
val mm256_mulhrs_epi16 : m256 -> m256 -> m256
val mm256_packus_epi16 : m256 -> m256 -> m256
val mm256_maddubs_epi16 : m256 -> m256 -> m256
val mm256_permutexvar_epi32 : m256 -> m256 -> m256
val mm256_srai_epi16 : m256 -> int -> m256