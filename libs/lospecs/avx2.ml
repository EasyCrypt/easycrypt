(* -------------------------------------------------------------- *)
type 'a pair = 'a * 'a
type 'a quad = 'a * 'a * 'a * 'a

(* -------------------------------------------------------------- *)
type m64x4 = int64 quad
type m32x8 = int32 pair quad
type m16x16 = int pair pair quad
type m8x32 = char pair pair pair quad

(* -------------------------------------------------------------- *)
type m256 = m64x4

(* -------------------------------------------------------------- *)
external oftuple_64 : m64x4 -> m256 = "%identity"
external totuple_64 : m256 -> m64x4 = "%identity"

(* -------------------------------------------------------------- *)
type endianess = [`Little | `Big]

(* -------------------------------------------------------------- *)
let to_bytes ~(endianess : endianess) (v : m256) : bytes =
  let w0, w1, w2, w3 = totuple_64 v in
  let b = Buffer.create 32 in

  let () =
    match endianess with
    | `Little ->
      Buffer.add_int64_le b w0;
      Buffer.add_int64_le b w1;
      Buffer.add_int64_le b w2;
      Buffer.add_int64_le b w3;

    | `Big ->
      Buffer.add_int64_be b w3;
      Buffer.add_int64_be b w2;
      Buffer.add_int64_be b w1;
      Buffer.add_int64_be b w0

  in Buffer.to_bytes b

(* -------------------------------------------------------------- *)
let of_bytes ~(endianess : endianess) (v : bytes) : m256 =
  assert (Bytes.length v = 32);

  let w0, w1, w2, w3 =
    match endianess with
      | `Big -> (
        Bytes.get_int64_be v 24,
        Bytes.get_int64_be v 16,
        Bytes.get_int64_be v  8,
        Bytes.get_int64_be v  0
      )
      | `Little -> (
        Bytes.get_int64_le v  0,
        Bytes.get_int64_le v  8,
        Bytes.get_int64_le v 16,
        Bytes.get_int64_le v 24
      )

in oftuple_64 (w0, w1, w2, w3)

(* -------------------------------------------------------------- *)
type size = [`U8 | `U16 | `U32 | `U64]

let width_of_size (s : size) : int =
  match s with
  | `U8  ->  8
  | `U16 -> 16
  | `U32 -> 32
  | `U64 -> 64

(* -------------------------------------------------------------- *)
let pp_bytes
  ~(size : size)
   (fmt : Format.formatter)
   (v : bytes)
=
  let w = width_of_size size  / 8 in

  v |> Bytes.iteri (fun i b ->
    if i <> 0 && i mod w = 0 then
      Format.fprintf fmt "_";
    Format.fprintf fmt "%02x" (Char.code b)
  )

(* -------------------------------------------------------------- *)
let pp
  ~(size : size)
  ~(endianess : endianess)
   (fmt : Format.formatter)
   (v : m256)
=
  Format.fprintf fmt "%a" (pp_bytes ~size) (to_bytes ~endianess v)

(* -------------------------------------------------------------- *)
let map_quad (type a) (type b) 
  (f : a -> b)
  ((x0, x1, x2, x3) : a quad)
=
  (f x0, f x1, f x2, f x3)

(* -------------------------------------------------------------- *)
let map_pair (type a) (type b) (f : a -> b) ((x, y) : a pair) =
  (f x, f y)

(* -------------------------------------------------------------- *)
external m64_to_32x2 : int64 -> int32 pair = "m64_to_32x2"
external m32_to_16x2 : int32 -> int pair = "m32_to_16x2"
external m16_to_8x2  : int -> char pair = "m16_to_8x2"

(* -------------------------------------------------------------- *)
external m64_of_32x2 : int32 pair -> int64 = "m64_of_32x2"
external m32_of_16x2 : int pair -> int32 = "m32_of_16x2"
external m16_of_8x2  : char pair -> int = "m16_of_8x2"
 
(* -------------------------------------------------------------- *)
let oftuple_32 (v : m32x8) : m256 =
  oftuple_64 (map_quad m64_of_32x2 v)

let totuple_32 (v : m256) : m32x8 =
  map_quad m64_to_32x2 (totuple_64 v)

(* -------------------------------------------------------------- *)
let oftuple_16 (v : m16x16) : m256 =
  oftuple_32 (map_quad (map_pair m32_of_16x2) v)

let totuple_16 (v : m256) : m16x16 =
  map_quad (map_pair m32_to_16x2) (totuple_32 v)

(* -------------------------------------------------------------- *)
let oftuple_8 (v : m8x32) : m256 =
  oftuple_16 (map_quad (map_pair (map_pair m16_of_8x2)) v)

let totuple_8 (v : m256) : m8x32 =
  map_quad (map_pair (map_pair m16_to_8x2)) (totuple_16 v)

(* -------------------------------------------------------------- *)
let random () : m256 =
  let w0 = Random.bits64() in
  let w1 = Random.bits64() in
  let w2 = Random.bits64() in
  let w3 = Random.bits64() in
  oftuple_64 (w0, w1, w2, w3)

(* -------------------------------------------------------------- *)
external mm256_and_si256 : m256 -> m256 -> m256 = "caml_mm256_and_si256"
external mm256_andnot_si256 : m256 -> m256 -> m256 = "caml_mm256_andnot_si256"
external mm256_add_epi16 : m256 -> m256 -> m256 = "caml_mm256_add_epi16"
external mm256_sub_epi16 : m256 -> m256 -> m256 = "caml_mm256_sub_epi16"
external mm256_mulhi_epu16 : m256 -> m256 -> m256 = "caml_mm256_mulhi_epu16"
external mm256_mulhrs_epi16 : m256 -> m256 -> m256 = "caml_mm256_mulhrs_epi16"
external mm256_packus_epi16 : m256 -> m256 -> m256 = "caml_mm256_packus_epi16"
external mm256_maddubs_epi16 : m256 -> m256 -> m256 = "caml_mm256_maddubs_epi16"
external mm256_permutevar8x32_epi32 : m256 -> m256 -> m256 = "caml_mm256_permutevar8x32_epi32"
external mm256_srai_epi16 : m256 -> int -> m256 = "caml_mm256_srai_epi16"