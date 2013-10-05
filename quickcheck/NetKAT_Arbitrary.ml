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

module Make (Syntax : NetKAT_Syntax.S)
            (ArbHdrs : ARBITRARY_HEADERS
                         with type hdr = Syntax.hdr
                          and type hdrVal = Syntax.hdrVal
                          and type payload = Syntax.payload) = struct
  type pol = Syntax.pol
  type pkt = Syntax.pkt

  module Gen = QuickCheck_gen
  open Syntax
  open ArbHdrs

  let gen_atom =
    let open Gen in
    frequency [
      (1, ret_gen Drop);
      (1, ret_gen Id);
      (2, arbitrary_hdr >>= fun h -> 
            arbitrary_hdrVal >>= fun v -> 
              ret_gen (Set (h, v)));
      (2, arbitrary_hdr >>= fun h -> 
            arbitrary_hdrVal >>= fun v -> 
              ret_gen (Test (h, v)))
    ]

  let gen_pred_atom =
    let open Gen in
    oneof [
      ret_gen Drop;
      ret_gen Id;
      arbitrary_hdr >>= fun h -> 
        arbitrary_hdrVal >>= fun v -> 
          ret_gen (Test (h, v))
    ]

  let rec gen_binpol (size : int) : pol Gen.gen =
    let open Gen in
    oneof [
      gen_pol (size - 1) >>= fun e1 -> 
        gen_pol (size - 1) >>= fun e2 -> 
          ret_gen (Par (e1, e2));
      gen_pol (size - 1) >>= fun e1 -> 
        gen_pol (size - 1) >>= fun e2 -> 
          ret_gen (Seq (e1, e2));
      gen_pred (size - 1) >>= fun e -> 
        ret_gen (Neg e)
    ]

  and gen_pred_ctor (size : int) : pol Gen.gen =
    let open Gen in
    frequency [
      (3, gen_pred (size - 1) >>= fun e1 -> 
            gen_pred (size - 1) >>= fun e2 -> 
              ret_gen (Par (e1, e2)));
      (3, gen_pred (size - 1) >>= fun e1 -> 
            gen_pred (size - 1) >>= fun e2 -> 
              ret_gen (Seq (e1, e2)));
      (3, gen_pred (size - 1) >>= fun e -> 
              ret_gen (Neg e))      
    ]

  and gen_pred (size : int) : pol Gen.gen =
    let open Gen in
    if size < 1 then
      gen_pred_atom
    else 
      Gen.oneof [gen_pred_atom; gen_pred_ctor size]

  and gen_pol (size : int) : pol Gen.gen =
    if size < 1 then
      gen_atom
    else
      Gen.oneof [gen_atom; gen_binpol size]

  let num_hdrs = List.length all_headers

  let arbitrary_pkt : pkt Gen.gen = 
    let open Gen in
    listN num_hdrs arbitrary_hdrVal >>= fun vals ->
      arbitrary_payload >>= fun payload ->
      ret_gen {
        headers = List.fold_right2 HdrMap.add all_headers vals HdrMap.empty;
        payload = payload
      }

  let arbitrary_pol = Gen.sized gen_pol

end