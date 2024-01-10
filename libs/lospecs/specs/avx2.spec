# Intel intrinsic: _mm256_permutexvar_epi32
VPERMD(widx@256, w@256) -> @256 =
  map<32, 8>(
    fun idx@32 . let i = idx[0:3] in w[@32|i],
    widx
  )

# Intel intrinsic: _mm256_add_epi16
VPADD_16u16(w1@256, w2@256) -> @256 =
  map<16, 16>(add<16>, w1, w2)

# Intel intrinsic: _mm256_sub_epi16
VPSUB_16u16(w1@256, w2@256) -> @256 =
  map<16, 16>(sub<16>, w1, w2)

# Intel intrinsic: _mm256_and_si256
VPAND_256(w1@256, w2@256) -> @256 = 
  and<256>(w1, w2)

# Intel intrinsic: _mm256_andnot_si256
VPNAND_256(w1@256, w2@256) -> @256 = 
  not<256>(and<256>(w1, w2))

# Intel intrinsic: _mm256_broadcastw_epi16
VPBROADCAST_16u16(w@16) -> @256 = 
  repeat<16>(w[@16|0], 16)
  
# Intel intrinsic: _mm256_mulhi_epu16
VPMULH_16u16(w1@256, w2@256) -> @256 =
  map<16, 16>(umulhi<16>, w1, w2)

# Intel intrinsic: _mm256_mulhrs_epi16
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
PACKUS_16u16(w1@256, w2@256) -> @256 =
  let pack (w@128) = map<16, 8>(usat<16, 8>, w) in

  concat<64>(
    pack(w1[@128|0]),
    pack(w2[@128|0]),
    pack(w1[@128|1]),
    pack(w2[@128|1])
  )
