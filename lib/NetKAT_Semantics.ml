module type S = sig

  type pkt
  type pol

  module PktSet : Set.S with type elt = pkt

  val eval : pkt -> pol -> PktSet.t
end


module Make (Syntax : NetKAT_Syntax.S)  = struct

  type pkt = Syntax.pkt
  type pol = Syntax.pol

  open Syntax

  module PktSet = Set.Make (struct
      type t = pkt
      (* First compare by headers, then payload. The payload comparison is a
         little questionable. However, this is safe to use in eval, since
         all output packets have the same payload as the input packet. *)
      let compare x y =
        let cmp = HdrMap.compare Pervasives.compare x.headers y.headers in
        if cmp != 0 then
          cmp
        else
          Pervasives.compare x.payload y.payload
    end)

  let rec eval (pkt : pkt) (pol : pol) : PktSet.t = match pol with
    | Drop -> PktSet.empty
    | Id -> PktSet.singleton pkt
    | Test (h, v) -> 
      if HdrMap.find h pkt.headers = v then
        PktSet.singleton pkt
      else
        PktSet.empty
    | Set (h, v) ->
      if HdrMap.mem h pkt.headers then
        PktSet.singleton { pkt with headers = HdrMap.add h v pkt.headers }
      else
        raise Not_found (* for consistency with Test *)
    | Neg p ->
      PktSet.diff (PktSet.singleton pkt) (eval pkt p)
    | Par (pol1, pol2) ->
      PktSet.union (eval pkt pol1) (eval pkt pol2)
    | Seq (pol1, pol2) ->
      let f pkt' set = PktSet.union (eval pkt' pol2) set in
      PktSet.fold f (eval pkt pol1) PktSet.empty

end