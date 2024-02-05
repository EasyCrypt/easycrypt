## See: https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html
UEXT(w1@8) -> @16 =
  uextend<8, 16>(w1)

SEXT(w1@8) -> @16 =
  sextend<8, 16>(w1)

SLL8(w@8, i@4) -> @8 = 
  sll<8>(w, uextend<4, 8>(i))

SRA8(w@8, i@4) -> @8 = 
  sra<8>(w, uextend<4, 8>(i))

SRL8(w@8, i@4) -> @8 = 
  srl<8>(w, uextend<4, 8>(i))

SLL14(w@14, i@4) -> @14 = 
  sll<14>(w, uextend<4, 8>(i))

SRA14(w@14, i@4) -> @14 = 
  sra<14>(w, uextend<4, 8>(i))

SRL14(w@14, i@4) -> @14 = 
  srl<14>(w, uextend<4, 8>(i))

ADD(w1@9, w2@9) -> @9 =
  add<9>(w1, w2)

INCR(w@11) -> @11 =
  incr<11>(w)

SUB(w1@9, w2@9) -> @9 =
  sub<9>(w1, w2)

UMUL(w1@10, w2@10) -> @20 =
  umul<10>(w1, w2)

SMUL(w1@10, w2@10) -> @20 =
  smul<10>(w1, w2)

USMUL(w1@8, w2@8) -> @16 =
  usmul<8>(w1, w2)

SSAT10_4(w@10) -> @4 =
  ssat<10, 4>(w)

SSAT15_7(w@15) -> @7 =
  ssat<15, 7>(w)

SSAT17_16(w@17) -> @16 =
  ssat<17, 16>(w)

USAT10_4(w@10) -> @4 =
  usat<10, 4>(w)

USAT15_7(w@15) -> @7 =
  usat<15, 7>(w)

SGT(w1@10, w2@10) -> @1 =
  sgt<10>(w1, w2)

SGE(w1@10, w2@10) -> @1 =
  sge<10>(w1, w2)

UGT(w1@10, w2@10) -> @1 =
  ugt<10>(w1, w2)

UGE(w1@10, w2@10) -> @1 =
  uge<10>(w1, w2)

# Intel intrinsic: _mm256_permutexvar_epi32
VPERMD(w@256, widx@256) -> @256 =
  map<32, 8>(
    fun idx@32 . let i = idx[0:3] in w[@32|i],
    widx
  )

# Intel intrinsic: _mm256_permute4x64_epi64
VPERMQ(w@256, i@8) -> @256 =
  let permute (i@2) = w[@64|i] in

  concat<64>(
    permute(i[@2|0]),
    permute(i[@2|1]),
    permute(i[@2|2]),
    permute(i[@2|3])
  )

# Intel intrinsic: _mm256_add_epi16
VPADD_16u16(w1@256, w2@256) -> @256 =
  map<16, 16>(add<16>, w1, w2)
#
## Intel intrinsic: _mm256_add_epi8
VPADD_32u8(w1@256, w2@256) -> @256 =
  map<8, 32>(add<8>, w1, w2)
#
## Intel intrinsic: _mm256_sub_epi16
VPSUB_16u16(w1@256, w2@256) -> @256 =
  map<16, 16>(sub<16>, w1, w2)
#
## Intel intrinsic: _mm256_sub_epi16
VPSUB_32u8(w1@256, w2@256) -> @256 =
  map<8, 32>(sub<8>, w1, w2)
#
## Intel intrinsic: _mm256_and_si256
VPAND_256(w1@256, w2@256) -> @256 = 
  and<256>(w1, w2)
#
## Intel intrinsic: _mm256_andnot_si256
VPNAND_256(w1@256, w2@256) -> @256 = 
  not<256>(and<256>(w1, w2))
#
## Intel intrinsic: _mm256_broadcastw_epi16
VPBROADCAST_16u16(w@64) -> @256 = 
  repeat<16>(w[@16|0], 16)
  
## Intel intrinsic: _mm256_mulhi_epu16
VPMULH_16u16(w1@256, w2@256) -> @256 =
  map<16, 16>(umulhi<16>, w1, w2)

## Intel intrinsic: _mm256_mulhrs_epi16
VPMULHRS_16u16(w1@256, w2@256) -> @256 =
  map<16, 16>(
    fun x@16 y@16 .
      let w = smul<16>(x, y) in
      let w = incr<32>(srl<32>(w, 14)) in
      w[1:16],
    w1,
    w2
  )

# Intel intrinsic: _mm256_srai_epi16
VPSRA_16u16(w@256, count@8) -> @256 =
  map<16, 16>(sra<16>(., count), w)
#
# Intel intrinsic: _mm256_srli_epi16
VPSRL_16u16(w@256, count@8) -> @256 =
  map<16, 16>(srl<16>(., count), w)

# Intel intrinsic: _mm256_maddubs_epi16
VPMADDUBSW_256(w1@256, w2@256) -> @256 =
  map<16, 16>(
    fun x@16 y@16 .
      ssadd<16>(
        usmul<8>(x[@8|0], y[@8|0]),
        usmul<8>(x[@8|1], y[@8|1])
      ),
    w1,
    w2
  )

# Intel intrinsic: _mm256_packus_epi16
VPACKUS_16u16(w1@256, w2@256) -> @256 =
  let pack (w@128) = map<16, 8>(usat<16, 8>, w) in

  concat<64>(
    pack(w1[@128|0]),
    pack(w2[@128|0]),
    pack(w1[@128|1]),
    pack(w2[@128|1])
  )

# Intel intrincis: _mm256_packs_epi16
VPACKSS_16u16(w1@256, w2@256) -> @256 =
  let pack (w@128) = map<16, 8>(ssat<16, 8>, w) in

  concat<64>(
    pack(w1[@128|0]),
    pack(w2[@128|0]),
    pack(w1[@128|1]),
    pack(w2[@128|1])
  )

# Intel intrinsic: _mm256_shuffle_epi8
VPSHUFB_256(w@256, widx@256) -> @256 =
  map<128, 2>(
    fun w@128 widx@128 .
      map<8, 16>(
        fun idx@8 . idx[7] ? 0 : w[@8|idx[0:4]],
        widx
      ),
    w,
    widx
  )

# Intel intrinsic: _mm256_blend_epi16
# FIXME: we need an heterogeneous `map' combinator
VPBLEND_16u16(w1@256, w2@256, c@8) -> @256 =
  let c = repeat<8>(c, 2) in
  let c = map<1, 16>(uextend<1, 16>, c) in

  map<16, 16>(
    fun c@16 w1@16 w2@16 . c[0] ? w2 : w1,
    c,
    w1,
    w2
  )

# Intel intrinsic: _mm256_cmpgt_epi16
VPCMPGT_16u16(w1@256, w2@256) -> @256 =
  map<16, 16>(
    fun w1@16 w2@16 . sgt<16>(w1, w2) ? 0xffff@16 : 0x0000@16,
    w1,
    w2
  )

# Intel intrinsic: _mm256_movemask_epi8
VPMOVMSKB_u256u64(w@256) -> @32 =
  map<8, 32>(fun i@8 . i[7], w)

# Intel intrinsic: _mm256_unpacklo_epi8
VPUNPCKL_32u8(w1@256, w2@256) -> @256 =
  let interleave (w1@64, w2@64) =
    map<8, 8>(
      fun w1@8 w2@8 . concat<8>(w1, w2),
      w1,
      w2
    )
  in

  concat<128>(
    interleave(w1[@64|0], w2[@64|0]),
    interleave(w1[@64|2], w2[@64|2])
  )

# Intel intrinsic: _mm256_extracti128_si256
VPEXTRACTI128(w@256, i@8) -> @128 =
  w[@128|i[0]]

# Intel intrinsic: _mm256_inserti128_si256
VPINSERTI128(w@256, m@128, i@8) -> @256 =
  w[@128|i[0] <- m]
