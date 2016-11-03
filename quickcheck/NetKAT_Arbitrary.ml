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
    oneof [
      ret_gen Drop;
      ret_gen Id;
      (arbitrary_hdr >>= fun h -> 
        arbitrary_hdrVal >>= fun v -> 
          ret_gen (Set (h, v)));
      arbitrary_hdr >>= fun h -> 
        arbitrary_hdrVal >>= fun v -> 
          ret_gen (Test (h, v))
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

let rec gen_pred_ctor () : pol Gen.gen =
    let open Gen in
    sized (fun n -> resize (n - 1)
      (oneof [
        (gen_pred () >>= fun e1 -> 
           gen_pred () >>= fun e2 -> 
             ret_gen (Par (e1, e2)));
        (gen_pred () >>= fun e1 -> 
           gen_pred () >>= fun e2 -> 
             ret_gen (Seq (e1, e2)));
        (gen_pred () >>= fun e ->
           ret_gen (Neg e))
      ]))

  and gen_pred () : pol Gen.gen =
    let open Gen in
    sized (fun n ->
      frequency [
        (1, gen_pred_atom);
        (n - 1, gen_pred_ctor ())
      ])



  let rec gen_binpol () : pol Gen.gen =
    let open Gen in
    sized (fun n -> resize (n - 1)
      (oneof [
        (gen_pol () >>= fun e1 -> 
           gen_pol () >>= fun e2 -> 
             ret_gen (Par (e1, e2)));
        (gen_pol () >>= fun e1 -> 
           gen_pol () >>= fun e2 -> 
             ret_gen (Seq (e1, e2)));
        (gen_pred () >>= fun e -> 
           ret_gen (Neg e))
      ]))

  and gen_pol () : pol Gen.gen =
    let open Gen in
    sized (fun n ->
      frequency [
        (1, gen_atom);
        (n - 1, gen_binpol ())
      ])

  let num_hdrs = List.length all_headers

  let arbitrary_pkt : pkt Gen.gen = 
    let open Gen in
    listN num_hdrs arbitrary_hdrVal >>= fun vals ->
      arbitrary_payload >>= fun payload ->
      ret_gen {
        headers = List.fold_right2 HdrMap.add all_headers vals HdrMap.empty;
        payload = payload
      }

  let arbitrary_pol = gen_pol ()

end
