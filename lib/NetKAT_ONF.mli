module type S = sig

  type hdr
  type hdrVal
  type pol

  module HdrMap : Map.S with type key = hdr

  (* A set of maps from header names to header values *)
  module HdrValSet : Set.S with type elt = hdrVal HdrMap.t


  (** {2 OpenFlow Normal Form}

      This is OpenFlow Normal Form, as defined in the NetKAT submission, with a
      few differences: (1) there is no star-compilation, (2) the grammar is for
      a particular switch, not all switches. Star compilation is forthcoming, but
      a whole-network ONF depends on knowning all switches in advance, which is
      not how we build our system. *)

  (** A conjunction of tests, where each test tests a distinct field and all
      fields are tested. Formally:

      Let [k] be the number of headers (12 for OpenFlow 1.0).

      [pred ::= h_1 = v_1 ; .. ; h_k = v_k]

      where all [k] headers are tested. *)
  type pred = hdrVal HdrMap.t

  (** A sequence of updates, where each update affects a distinct field.
      Therefore, they all commute with each other and can be represented by
      a set. Formally:

      [seq  ::= h_1 -> v_1 ; ... ; h_1 -> v_n]

      where all headers [h] are distinct. *)
  type seq = hdrVal HdrMap.t

  (** A sum of update sequences, where each sequence is distinct. Formally:

        [sum ::= seq_1; ...; seq_n]

      where all subterms [seq] are distinct. *)
  type sum = HdrValSet.t

  (** A cascase of [if .. then .. else] expressions nested under the [else]
      branch.

      [local ::= sum | if pred then sum else sum] *)
  type local =
    | Action of sum
    | ITE of pred * sum * local

  (** {2 NetKAT Compiler}

      Applying [compile pol] will fail if [pol] tries to update [Switch]. However,
      testing the [Switch] is fine. We produce a policy where some clauses are
      guarded by switch tests. These clauses are only emitted to those particular
      switches. {i I think the NetKAT submission's compiler section could
      be refactored to follow this pattern too.} *)
  val compile : pol -> local

  val to_netkat : local -> pol  
end

module Make : functor (Syntax : NetKAT_Syntax.S) ->
  S with type hdr = Syntax.hdr
     and type hdrVal = Syntax.hdrVal
     and type pol = Syntax.pol
     and module HdrMap = Syntax.HdrMap
     and module HdrValSet = Syntax.HdrValSet
