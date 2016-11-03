type hdr_ = Src | Dst

module Syntax = NetKAT_Syntax.Make (struct
  type hdr = hdr_
  type hdrVal = int
  type payload = unit
  let compare_hdr = Pervasives.compare
  let format_hdr fmt hdr = match hdr with
    | Src -> Format.fprintf fmt "Src"
    | Dst -> Format.fprintf fmt "Dst"
  let format_hdrVal fmt n = Format.fprintf fmt "%d" n
end)

module M = NetKAT_ONF.Make (Syntax)
module Sem = NetKAT_Semantics.Make (Syntax)

let string_of_pol pol =
  let open Format in
  let buf = Buffer.create 100 in
  let fmt = formatter_of_buffer buf in
  pp_set_margin fmt 80;
  Syntax.print_pol fmt pol;
  fprintf fmt "@?";
  Buffer.contents buf

module ONFQuickChecker = NetKAT_Arbitrary.Make (Syntax)
  (struct
    type hdr = hdr_
    type hdrVal = int
    type payload = unit
    let all_headers = [ Src; Dst ]
    let arbitrary_hdr = QuickCheck_gen.elements [ Src; Dst ]
    let arbitrary_hdrVal = QuickCheck_gen.choose_int0 2
    let arbitrary_payload = QuickCheck_gen.ret_gen ()
  end)

open Syntax

(* Quick-checking *)

let testable_pol_pkt_to_bool =
  let open QuickCheck in
  let open QuickCheck_gen in
  let open ONFQuickChecker in
  testable_fun 
    (resize 10
     (arbitrary_pol >>= fun pol ->
        arbitrary_pkt >>= fun pkt ->
          ret_gen (pol, pkt)))
    (fun (pol,pkt) -> string_of_pol pol)
    testable_bool

let prop_compile_ok (pol, pkt) = 
  let open Sem in
  PktSet.compare (eval pkt pol) (eval pkt (M.to_netkat (M.compile pol))) = 0

let qc () =
  Format.printf "prop_compile_ok:\n";
  let cfg = { QuickCheck.verbose with QuickCheck.maxTest = 1000 } in
  let _ = QuickCheck.check testable_pol_pkt_to_bool cfg prop_compile_ok in
  ()

let _ = qc ()

(* Unit testing *)

let test_compile lhs rhs =
  let lhs' = M.to_netkat (M.compile lhs) in
  if lhs' = rhs then
    true
  else
    begin
      Format.printf "compile @,%a@, produced %a@,,@,expected %a\n%!"
      format_pol lhs format_pol lhs' format_pol rhs;
      false
    end

let ite (pred : pol) (then_pol : pol) (else_pol : pol) : pol =
  Par (Seq (pred, then_pol), Seq (Neg pred, else_pol))

let%test "compile drop" =
  test_compile Drop Drop

let%test "compile !drop" = 
  test_compile 
    (Neg (Neg (Seq (Seq (Id,
                              Par (Par (Seq (Seq (Seq (Test (Dst,0),
                                                   Test (Src,1)),
                                              Drop),
                                         Par (Test (Src,1),  Drop)),
                                    Id),
                               Par (Seq (Test (Dst,0),
                                     Neg (Seq (Neg (Test (Src,0)),
                                           Par (Drop,  Test (Dst,0))))),
                                Drop))),
                         Par (Id,  Seq (Test (Src,0),  Id))))))
    Drop

(* !Dst = 1 + (drop + id + (!drop) + drop ; drop) ; drop *)

let%test "compile test" =
  let pr = Test (Src, 100) in
  test_compile pr (ite pr Id Drop)

let%test "compile negation" =
  let pr = Test (Src, 200) in
  test_compile (Neg pr) (ite pr Drop Id)

let%test "compile negation of sum" =
  let pr = Seq (Test (Src, 0), Test (Dst, 0)) in
  test_compile
    (Neg pr)
    (* order flipped, a canonical ordering from to_netkat would be great *)
    (ite (Seq (Test (Dst, 0), Test (Src, 0)))
       Drop
       (* trivial optimization *)
       (ite (Test (Src, 0)) Id Id))

(* TODO(arjun): Prove that this is true using the axioms of NetKAT. *)
let%test "commute test annihilator" =
  test_compile
    (Seq (Set (Src, 1), Test (Src, 0)))
    Drop

let%test "commute test different fields" =
  test_compile
    (Seq (Set (Src, 1), Test (Dst, 0)))
    (ite (Test (Dst, 0))
       (Set (Src, 1))
       Drop)

(* trivial optimization possible *)
let%test "commute same field" =
  test_compile
    (Seq (Set (Src, 1), Test (Src, 1)))
    (ite Id
       (Set (Src, 1))
       Drop)

(* trivial optimization possible *)
let%test "same field, two values = drop" =
  test_compile
    (Seq (Test (Src, 1), Test (Src, 0)))
    (ite (Test (Src, 1)) Drop Drop)

