(*---------------------------------------------------------------------------
   Copyright (c) 2008-2012 Daniel C. Bünzli. All rights reserved.
   Distributed under a BSD3 license, see license at the end of the file.
   uuidm release 0.9.5
  ---------------------------------------------------------------------------*)

(** Universally unique identifiers (UUIDs).  

    [Uuidm] implements 128 bits universally unique identifiers version
    3, 5 (name based with MD5, SHA-1 hashing) and 4 (random based)
    according to {{:http://www.ietf.org/rfc/rfc4122.txt}RFC 4122}.

    {e Release 0.9.5 - Daniel Bünzli <daniel.buenzli at erratique.ch> }

    {3 References}
    {ul 
    {- P. Leach et al.
    {e {{:http://www.ietf.org/rfc/rfc4122.txt}A universally unique identifier 
     (UUID) URN Namespace}}, 2005.}} *)

(** {1 UUIDs} *)

type t
(** The type for UUIDs. *)

type version = [ 
  | `V3 of t * string (** Name based with MD5 hashing *)
  | `V4 (** Random based *) 
  | `V5 of t * string (** Name based with SHA-1 hasing *) ]
(** The type for UUID versions and generation parameters. [`V3] and [`V5]
    specify a namespace and a name for the generation. [`V4] is random based 
    with a private state seeded with [Random.State.make_self_init], use 
    {!v4_gen} to specify your own seed. *)

val nil : t
(** [nil] is the nil UUID. *)

val ns_dns : t
(** [ns_dns] is the DNS namespace UUID. *)

val ns_url : t
(** [ns_url] is the URL namespace UUID. *)

val ns_oid : t
(** [ns_oid] is the ISO OID namespace UUID. *)

val ns_X500 : t
(** [ns_dn] is the X.500 DN namespace UUID. *)

val create : version -> t
(** [create version] is an UUID of the given [version]. *)

val v3 : t -> string -> t
(** [v3 ns n] is [create `V3 (ns, n)]. *) 

val v5 : t -> string -> t
(** [v5 ns n] is [create `V5 (ns, n)]. *)

val v4_gen : Random.State.t -> (unit -> t)
(** [v4 seed] is a function that generates random version 4 UUIDs with
    the given [seed]. *)

val compare : t -> t -> int
(** Total order on UUIDs. *)

val equal : t -> t -> bool
(** [equal u u'] is [true] iff [u] and [u'] are equal. *)

val of_bytes : ?pos:int -> string -> t option
(** [of_bytes pos s] is the UUID represented by the 16 bytes starting
    at [pos] in [s] ([pos] defaults to [0]).  Returns [None] if the
    string is not long enough. *)

val to_bytes : t -> string
(** [to_bytes u] is [u] as a 16 bytes long string. *)

(**/**)
val unsafe_to_bytes : t -> string
(**/**) 

val of_string : ?pos:int -> string -> t option
(** [of_string pos s] converts the substring of [s] starting at [pos]
    (defaults to [0]) of the form ["XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX"]
    where X is a lower or upper case hexadecimal number to an
    UUID. Returns [None] if a parse error occured.  *)

val to_string : ?upper:bool -> t -> string
(** [to_string u] is [u] as a string of the form
    ["XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX"] where X is
    a lower case hexadecimal number (or upper if [upper] is
    [true]). *)

val print : ?upper:bool -> Format.formatter -> t -> unit
(** See {!to_string}. *)

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
