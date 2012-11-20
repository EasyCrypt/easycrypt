(*---------------------------------------------------------------------------
   Copyright (c) 2008-2012 Daniel C. Bünzli. All rights reserved.
   Distributed under a BSD3 license, see license at the end of the file.
   uuidm release 0.9.5
  ---------------------------------------------------------------------------*)

type t = string                                     (* 16 bytes long strings *)
type version = [ `V3 of t * string | `V4 | `V5 of t * string ]

let nil = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
let ns_dns = "\x6b\xa7\xb8\x10\x9d\xad\x11\xd1\x80\xb4\x00\xc0\x4f\xd4\x30\xc8"
let ns_url = "\x6b\xa7\xb8\x11\x9d\xad\x11\xd1\x80\xb4\x00\xc0\x4f\xd4\x30\xc8"
let ns_oid = "\x6b\xa7\xb8\x12\x9d\xad\x11\xd1\x80\xb4\x00\xc0\x4f\xd4\x30\xc8"
let ns_X500 ="\x6b\xa7\xb8\x14\x9d\xad\x11\xd1\x80\xb4\x00\xc0\x4f\xd4\x30\xc8"

let rand s = fun () -> Random.State.bits s                  (* 30 random bits generator. *)
let default_rand = rand (Random.State.make_self_init ())
                              
let md5 = Digest.string

(* sha-1 digest. Based on pseudo-code of RFC 3174.
   Slow and ugly but does the job. *)
let sha_1 s =                            
  let sha_1_pad s = 
    let len = String.length s in
    let blen = 8 * len in
    let rem = len mod 64 in
    let mlen = if rem > 55 then len + 128 - rem else len + 64 - rem in
    let m = String.create mlen in 
    String.blit s 0 m 0 len;
    String.fill m len (mlen - len) '\x00';
    m.[len] <- '\x80';
    if Sys.word_size > 32 then begin
      m.[mlen - 8] <- Char.unsafe_chr (blen lsr 56 land 0xFF);
      m.[mlen - 7] <- Char.unsafe_chr (blen lsr 48 land 0xFF);
      m.[mlen - 6] <- Char.unsafe_chr (blen lsr 40 land 0xFF);
      m.[mlen - 5] <- Char.unsafe_chr (blen lsr 32 land 0xFF);
    end;
    m.[mlen - 4] <- Char.unsafe_chr (blen lsr 24 land 0xFF);
    m.[mlen - 3] <- Char.unsafe_chr (blen lsr 16 land 0xFF);
    m.[mlen - 2] <- Char.unsafe_chr (blen lsr 8 land 0xFF);
    m.[mlen - 1] <- Char.unsafe_chr (blen land 0xFF);
    m
  in
  (* Operations on int32 *)
  let ( &&& ) = ( land ) in
  let ( lor ) = Int32.logor in
  let ( lxor ) = Int32.logxor in
  let ( land ) = Int32.logand in
  let ( ++ ) = Int32.add in
  let lnot = Int32.lognot in
  let sr = Int32.shift_right in
  let sl = Int32.shift_left in
  let cls n x = (sl x n) lor (Int32.shift_right_logical x (32 - n)) in
  (* Start *)
  let m = sha_1_pad s in
  let w = Array.make 16 0l in
  let h0 = ref 0x67452301l in
  let h1 = ref 0xEFCDAB89l in
  let h2 = ref 0x98BADCFEl in
  let h3 = ref 0x10325476l in
  let h4 = ref 0xC3D2E1F0l in
  let a = ref 0l in
  let b = ref 0l in
  let c = ref 0l in
  let d = ref 0l in
  let e = ref 0l in
  for i = 0 to ((String.length m) / 64) - 1 do             (* For each block *) 
    (* Fill w *)
    let base = i * 64 in
    for j = 0 to 15 do 
      let k = base + (j * 4) in
      w.(j) <- sl (Int32.of_int (Char.code m.[k])) 24 lor
               sl (Int32.of_int (Char.code m.[k + 1])) 16 lor
               sl (Int32.of_int (Char.code m.[k + 2])) 8 lor
               (Int32.of_int (Char.code m.[k + 3]))
    done;
    (* Loop *)
    a := !h0; b := !h1; c := !h2; d := !h3; e := !h4;
    for t = 0 to 79 do 
      let f, k = 
        if t <= 19 then (!b land !c) lor ((lnot !b) land !d), 0x5A827999l else
        if t <= 39 then !b lxor !c lxor !d, 0x6ED9EBA1l else
        if t <= 59 then 
	  (!b land !c) lor (!b land !d) lor (!c land !d), 0x8F1BBCDCl 
	else
        !b lxor !c lxor !d, 0xCA62C1D6l
      in
      let s = t &&& 0xF in
      if (t >= 16) then begin
	  w.(s) <- cls 1 begin 
	    w.((s + 13) &&& 0xF) lxor 
	    w.((s + 8) &&& 0xF) lxor 
	    w.((s + 2) &&& 0xF) lxor
	    w.(s)
	  end
      end;
      let temp = (cls 5 !a) ++ f ++ !e ++ w.(s) ++ k in
      e := !d;
      d := !c;
      c := cls 30 !b;
      b := !a;
      a := temp;
    done;
    (* Update *)
    h0 := !h0 ++ !a;
    h1 := !h1 ++ !b;
    h2 := !h2 ++ !c;
    h3 := !h3 ++ !d;
    h4 := !h4 ++ !e
  done;
  let h = String.create 20 in
  let i2s h k i =
    h.[k] <- Char.unsafe_chr ((Int32.to_int (sr i 24)) &&& 0xFF);
    h.[k + 1] <- Char.unsafe_chr ((Int32.to_int (sr i 16)) &&& 0xFF);
    h.[k + 2] <- Char.unsafe_chr ((Int32.to_int (sr i 8)) &&& 0xFF);
    h.[k + 3] <- Char.unsafe_chr ((Int32.to_int i) &&& 0xFF);
  in
  i2s h 0 !h0;
  i2s h 4 !h1;
  i2s h 8 !h2;
  i2s h 12 !h3;
  i2s h 16 !h4;
  h

let msg_uuid v digest ns n = 
  let u = String.sub (digest (ns ^ n)) 0 16 in
  u.[6] <- Char.unsafe_chr ((v lsl 4) lor (Char.code u.[6] land 0b0000_1111));
  u.[8] <- Char.unsafe_chr (0b1000_0000 lor (Char.code u.[8] land 0b0011_1111));
  u

let v3 ns n = msg_uuid 3 md5 ns n  
let v5 ns n = msg_uuid 5 sha_1 ns n  

let v4_uuid rand =
  let r0 = rand () in 
  let r1 = rand () in 
  let r2 = rand () in
  let r3 = rand () in
  let r4 = rand () in
  let u = String.copy nil in
  u.[0] <- Char.unsafe_chr (r0 land 0xFF);
  u.[1] <- Char.unsafe_chr (r0 lsr 8 land 0xFF);
  u.[2] <- Char.unsafe_chr (r0 lsr 16 land 0xFF);
  u.[3] <- Char.unsafe_chr (r1 land 0xFF);
  u.[4] <- Char.unsafe_chr (r1 lsr 8 land 0xFF);
  u.[5] <- Char.unsafe_chr (r1 lsr 16 land 0xFF);
  u.[6] <- Char.unsafe_chr (0b0100_0000 lor (r1 lsr 24 land 0b0000_1111));
  u.[7] <- Char.unsafe_chr (r2 land 0xFF);
  u.[8] <- Char.unsafe_chr (0b1000_0000 lor (r2 lsr 24 land 0b0011_1111));
  u.[9] <- Char.unsafe_chr (r2 lsr 8 land 0xFF);
  u.[10] <- Char.unsafe_chr (r2 lsr 16 land 0xFF);
  u.[11] <- Char.unsafe_chr (r3 land 0xFF);
  u.[12] <- Char.unsafe_chr (r3 lsr 8 land 0xFF);
  u.[13] <- Char.unsafe_chr (r3 lsr 16 land 0xFF);
  u.[14] <- Char.unsafe_chr (r4 land 0xFF);
  u.[15] <- Char.unsafe_chr (r4 lsr 8 land 0xFF);
  u

let v4_gen seed = 
  let rand = rand seed in     
  function () -> v4_uuid rand

let create = function
  | `V4 -> v4_uuid default_rand
  | `V3 (ns, n) -> v3 ns n
  | `V5 (ns, n) -> v5 ns n

let compare : string -> string -> int = Pervasives.compare
let equal u u' = compare u u' = 0

let of_bytes ?(pos = 0) s =
  let len = String.length s in
  if pos + 16 > len then None else
  Some (String.sub s pos 16)

let to_bytes = String.copy
let unsafe_to_bytes u = u

let of_string ?(pos = 0) s =
  let len = String.length s in
  if 
    pos + 36 > len || s.[pos + 8] <> '-' || s.[pos + 13] <> '-' || 
    s.[pos + 18] <> '-' || s.[pos + 23] <> '-' 
  then 
    None 
  else
    try
      let u = String.copy nil in
      let i = ref 0 in
      let j = ref pos in
      let ihex c = 
	let i = Char.code c in 
	if i < 0x30 then raise Exit else 
	if i <= 0x39 then i - 0x30 else
	if i < 0x41 then raise Exit else
	if i <= 0x46 then i - 0x37 else
	if i < 0x61 then raise Exit else
	if i <= 0x66 then i - 0x57 else
	raise Exit
      in
      let byte s j = Char.unsafe_chr (ihex s.[j] lsl 4 lor ihex s.[j + 1]) in
      while (!i < 4) do u.[!i] <- byte s !j; j := !j + 2; incr i done; 
      incr j;
      while (!i < 6) do u.[!i] <- byte s !j; j := !j + 2; incr i done; 
      incr j;
      while (!i < 8) do u.[!i] <- byte s !j; j := !j + 2; incr i done; 
      incr j;
      while (!i < 10) do u.[!i] <- byte s !j; j := !j + 2; incr i done; 
      incr j;
      while (!i < 16) do u.[!i] <- byte s !j; j := !j + 2; incr i done;
      Some u
    with Exit -> None

let to_string ?(upper = false) u =
  let hbase = if upper then 0x37 else 0x57 in
  let hex hbase i = Char.unsafe_chr (if i < 10 then 0x30 + i else hbase + i) in
  let s = String.copy "XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX" in
  let i = ref 0 in
  let j = ref 0 in
  let byte s i c = 
    s.[i] <- hex hbase (c lsr 4);
    s.[i + 1] <- hex hbase (c land 0x0F) 
  in
  while (!j < 4) do byte s !i (Char.code u.[!j]); i := !i + 2; incr j; done;
  incr i;
  while (!j < 6) do byte s !i (Char.code u.[!j]); i := !i + 2; incr j; done;
  incr i;
  while (!j < 8) do byte s !i (Char.code u.[!j]); i := !i + 2; incr j; done;
  incr i;
  while (!j < 10) do byte s !i (Char.code u.[!j]); i := !i + 2; incr j; done;
  incr i;
  while (!j < 16) do byte s !i (Char.code u.[!j]); i := !i + 2; incr j; done;
  s

let print ?upper fmt u = Format.pp_print_string fmt (to_string ?upper u)

(*---------------------------------------------------------------------------
  Copyright (c) 2008-2012 Daniel C. Bünzli
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are
  met:
        
  1. Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.

  2. Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the
     distribution.

  3. Neither the name of Daniel C. Bünzli nor the names of
     contributors may be used to endorse or promote products derived
     from this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  ---------------------------------------------------------------------------*)


