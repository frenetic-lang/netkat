(** The syntax of NetKAT *)

module type HEADERS = sig
  type hdr
  type hdrVal
  type payload
  val compare_hdr : hdr -> hdr -> int
  val format_hdr : Format.formatter -> hdr -> unit
  val format_hdrVal : Format.formatter -> hdrVal -> unit
end

module type S = sig

  type hdr
  type hdrVal
  type payload

  type pol =
    | Drop
    | Id
    | Test of hdr * hdrVal
    | Set of hdr * hdrVal 
    | Neg of pol
    | Par of pol * pol
    | Seq of pol * pol

  (** A map keyed by headers *)
  module HdrMap : Map.S with type key = hdr

  (* A set of maps from header names to header values *)
  module HdrValSet : Set.S with type elt = hdrVal HdrMap.t

  type pkt = {
    headers : hdrVal HdrMap.t;
    payload : payload
  }

  val format_pol : Format.formatter -> pol -> unit
  val print_pol : Format.formatter -> pol -> unit
end

module Make : functor (Headers : HEADERS) ->
  S with type hdr = Headers.hdr
     and type hdrVal = Headers.hdrVal
     and type payload = Headers.payload