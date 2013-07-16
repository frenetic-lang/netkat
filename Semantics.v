Set Implicit Arguments.

Require Import Syntax.
Require Import Sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Equivalence.

Definition get_Field (pkt : packet) (fld : field) : nat :=
  match fld with
    | Src => pktSrc pkt
    | Dst => pktDst pkt
  end.

Definition set_field (h : history) (fld : field) (n : nat) : history :=
  match h with
    | OneHist p => match fld with
             | Src => OneHist (Packet n (get_Field p Dst))
             | Dst => OneHist (Packet (get_Field p Src) n)
             end
    | ConsHist p hst => match fld with
                  | Src => ConsHist (Packet n (get_Field p Dst)) hst
                  | Dst => ConsHist (Packet (get_Field p Src) n) hst
                  end
    end.        

Definition get_Packet (hst : history) : packet :=
  match hst with
    | OneHist p => p
    | ConsHist p h => p
  end.

Definition Kleisli {A : Type} (rel1 rel2 : A -> A -> Prop) (ina outa : A) : Prop :=
  exists (x : A), (rel1 ina x) /\ (rel2 x outa).

Fixpoint iter (rel : history -> history -> Prop) (i : nat) (inh : history) : set history :=
  match i with
   | O => singleton inh
   | S n => (Kleisli rel (iter rel (n))) inh
  end.

Fixpoint eval (e : exp) (h : history) : set history :=
  match e with
   | Drop => @empty history
   | Id => singleton h
   | Match f v => match beq_nat (get_Field (get_Packet h) f) v with 
                    | true => singleton h
                    | false => @empty history
                  end
   | Mod f v => singleton (set_field h f v)
   | Par e1 e2 => (union (eval e1 h) (eval e2 h))
   | Neg e1 => (set_minus (singleton h) (eval e1 h))
   | Obs => singleton (ConsHist (get_Packet h) h)
   | Seq e1 e2 => Kleisli (eval e1) (eval e2) h
   | Star e1 => fun (y : history) => exists (i : nat), (iter (eval e1) i h y)
  end.

Definition equiv_exp (e1 : exp) (e2 : exp) : Prop := 
  forall (h : history), equiv (eval e1 h) (eval e2 h).
 
