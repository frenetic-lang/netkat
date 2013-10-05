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

module Make (Headers : HEADERS)  = struct

  open Headers

  type hdr = Headers.hdr
  type hdrVal = Headers.hdrVal
  type payload = Headers.payload

  module HdrMap = Map.Make (struct
    type t = hdr
    let compare = Pervasives.compare
  end)

  module HdrValSet = Set.Make (struct
   type t = hdrVal HdrMap.t
    let compare x y = HdrMap.compare Pervasives.compare x y
  end)

  type pol =
    | Drop
    | Id
    | Test of hdr * hdrVal
    | Set of hdr * hdrVal 
    | Neg of pol
    | Par of pol * pol
    | Seq of pol * pol

  type pkt = {
    headers : hdrVal HdrMap.t;
    payload : payload
  }

  type pred = hdrVal HdrMap.t
  type seq = hdrVal HdrMap.t
  type sum = HdrValSet.t

  type local =
    | Action of sum
    | ITE of pred * sum * local

  let id : seq = HdrMap.empty

  let drop : sum = HdrValSet.empty

  module Formatting = struct

    open Format

    (* The type of the immediately surrounding context, which guides parenthesis-
       intersion. *)
    type cxt = SEQ | PAR | NEG

    let print_paren (cxt : cxt) (e : pol) : bool = match e with
      | Drop -> false
      | Id -> false
      | Test _ -> false
      | Set _ -> false
      | Neg _ -> cxt < NEG
      | Par _ -> cxt < PAR
      | Seq _ -> cxt < SEQ

    let parens (on : bool) (fmt : formatter) (thunk : unit -> unit) : unit =
      match on with
      | false -> thunk ()
      | true ->
        let open Format in
        pp_open_box fmt 0;
        pp_print_string fmt "(";
        thunk ();
        pp_print_string fmt ")";
        pp_close_box fmt ()

    let rec pol (cxt : cxt) (fmt : formatter) (p : pol) : unit =
      parens (print_paren cxt p) fmt (fun () -> match p with
        | Drop -> fprintf fmt "@[drop@]"
        | Id -> fprintf fmt "@[id@]"
        | Test (h, v) -> fprintf fmt "@[%a = %a@]" format_hdr h format_hdrVal v
        | Set (h, v) -> fprintf fmt "@[%a <- %a@]" format_hdr h format_hdrVal v
        | Neg p' -> fprintf fmt "@[!%a@]" (pol NEG) p'
        | Par (p1, p2) -> fprintf fmt "@[%a + %a@]" (pol PAR) p1 (pol PAR) p2
        | Seq (p1, p2) -> fprintf fmt "@[%a ; %a@]" (pol SEQ) p1 (pol SEQ) p2)

    let rec print_pol (fmt : formatter) (p : pol) : unit =
      match p with
        | Drop -> fprintf fmt "Drop"
        | Id -> fprintf fmt "Id"
        | Test (h, v) -> fprintf fmt "@[Test (%a,%a)@]" format_hdr h format_hdrVal v
        | Set (h, v) -> fprintf fmt "@[Set (%a, %a)@]" format_hdr h format_hdrVal v
        | Neg p' -> fprintf fmt "@[Neg (%a)@]" print_pol p'
        | Par (p1, p2) -> fprintf fmt "@[Par (%a,@  %a)@]" print_pol p1 print_pol p2
        | Seq (p1, p2) -> fprintf fmt "@[Seq (%a,@  %a)@]" print_pol p1 print_pol p2


  end

  let format_pol = Formatting.pol Formatting.NEG

  let print_pol = Formatting.print_pol

end