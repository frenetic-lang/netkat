(** The semantics of NetKAT *)

module type S = sig

  type pkt
  type pol

  module PktSet : Set.S with type elt = pkt

  val eval : pkt -> pol -> PktSet.t
end

module Make : functor (Syntax : NetKAT_Syntax.S) ->
  S with type pkt = Syntax.pkt
     and type pol = Syntax.pol
