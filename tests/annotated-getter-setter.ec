(* -------------------------------------------------------------------- *)
require import AllCore.

type u32, u64.

type key.
type map.

theory GS32.
  op "_.[_]" : map -> key -> u32.
  op "_.[_<-_]" : map -> key -> u32 -> map.
end GS32.

theory GS64.
  op "_.[_]" : map -> key -> u64.
  op "_.[_<-_]" : map -> key -> u64 -> map.
end GS64.

import GS32 GS64.

op myget32 (m : map) k = m.[:(u32) k].

op myset32 (m : map) k v = m.[:(u32) k <- v].

op myget64 (m : map) k = m.[:(u64) k].

op myset64 (m : map) k v = m.[:(u64) k <- v].

module M = {
  proc f32(m : map, k, v) = {
    m.[:(u32) k] <- v;
    return m;
  }

  proc f64(m : map, k, v) = {
    m.[:(u64) k] <- v;
    return m;
  }
}.
