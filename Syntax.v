Set Implicit Arguments.

Inductive field : Type :=
  | Src : field
  | Dst : field.

Record packet := Packet {
  pktSrc : nat;
  pktDst : nat
}.

(*
Axiom k : nat.

Axiom v : Type.

Inductive packet := 
 | Packet : forall (lst : list v), length lst = k -> packet.
*) 

Inductive history : Type := 
 | OneHist : packet -> history
 | ConsHist : packet -> history -> history.

Inductive exp :=
 | Drop : exp
 | Id : exp
 | Match : field -> nat -> exp
 | Par : exp -> exp -> exp
 | Seq : exp -> exp -> exp
 | Neg : exp -> exp
 | Mod : field -> nat -> exp
 | Star : exp -> exp
 | Obs : exp.

Inductive pred : exp -> Prop := 
  | PrDrop : pred Drop
  | PrId : pred Id
  | PrMatch : forall (f : field) (v : nat), pred (Match f v)
  | PrPar : forall (e1 e2 : exp),
      pred e1 ->
      pred e2 ->
      pred (Par e1 e2)
  | PrSeq : forall (e1 e2 : exp),
      pred e1 -> 
      pred e2 ->
      pred (Seq e1 e2)
  | PrNeg : forall (e1 : exp),
      pred e1 ->
      pred (Neg e1).

Inductive pol : exp -> Prop :=
  | PolPred : forall (e1 : exp),
      pred e1 -> 
      pol e1
  | PolMod : forall (f : field) (v : nat),
      pol (Mod f v)
  | PolPar : forall (e1 e2 : exp),
      pol e1 -> 
      pol e2 ->
      pol (Par e1 e2)
  | PolSeq : forall (e1 e2 : exp),
      pol e1 ->
      pol e2 ->
      pol (Seq e1 e2)
  | PolStar : forall (e1 : exp),
      pol e1 ->
      pol (Star e1)
  | PolObs : pol Obs.

Hint Constructors pol pred.

