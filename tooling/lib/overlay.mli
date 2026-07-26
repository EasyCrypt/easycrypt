(** [OVERLAY_KIND]: a transformation over [(document, sentence_ids)] that
    produces a replacement feed for a scratch session. Owns its own
    forked sentence->uuid map on application (the scratch session carries
    it). Primary is untouched. See plan § "Speculative state — Overlay". *)

(** A sentence in the document as seen by an overlay: the stable id plus
    the source text. The overlay may drop or replace sentences; it must
    not produce output that references identifiers outside the original
    range. *)
type sentence = {
  id : Sentence_id.t;
  source : string;
}

module type OVERLAY_KIND = sig
  val name : string
  (** Stable identifier for the overlay kind (e.g. ["mask-with-admit"]). *)

  type config
  (** Per-overlay-instance configuration. *)

  val apply : config -> sentence list -> string list
  (** Transform the given sentences into a list of source-line feeds to
      send to the scratch session, in order. The returned list may be
      shorter or longer than the input. *)

  val compose :
    config -> config -> (config, Error.t) result
  (** Stack two instances of this kind into a single equivalent one.
      [Error.Overlay_conflict] if they cannot compose. PoC stub impls
      may reject all composition. *)
end
