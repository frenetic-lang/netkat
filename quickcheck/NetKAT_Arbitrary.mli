module type ARBITRARY_HEADERS = sig
  type hdr
  type hdrVal
  type payload
  val all_headers : hdr list
  val arbitrary_hdr : hdr QuickCheck.arbitrary
  val arbitrary_hdrVal : hdrVal QuickCheck.arbitrary
  val arbitrary_payload : payload QuickCheck.arbitrary
end

module type S = sig
  type pol
  type pkt
  val arbitrary_pol : pol QuickCheck.arbitrary
  val arbitrary_pkt : pkt QuickCheck.arbitrary
end

module Make :
  functor (Syntax : NetKAT_Syntax.S) -> 
    functor (ArbHdrs : ARBITRARY_HEADERS
               with type hdr = Syntax.hdr
                and type hdrVal = Syntax.hdrVal
                and type payload = Syntax.payload) -> 
      S with type pol = Syntax.pol
         and type pkt = Syntax.pkt