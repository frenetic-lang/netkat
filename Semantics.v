Set Implicit Arguments.

Require Import Syntax.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Arith.EqNat.

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

Check Singleton.

Check In_singleton.
Fixpoint iter (rel : history -> history -> Prop) (i : nat) (inh : history) : Ensemble history :=
  match i with
   | O => Singleton history inh
   | S n => (Kleisli rel (iter rel (n))) inh
  end.

Fixpoint eval (e : exp) (h : history) : Ensemble history :=
  match e with
   | Drop => @Empty_set history
   | Id => Singleton _ h
   | Match f v => match beq_nat (get_Field (get_Packet h) f) v with 
                    | true => Singleton _ h
                    | false => @Empty_set history
                  end
   | Mod f v => Singleton _ (set_field h f v)
   | Par e1 e2 => Union _ (eval e1 h) (eval e2 h)
   | Neg e1 => Setminus _ (Singleton _ h) (eval e1 h)
   | Obs => Singleton _ (ConsHist (get_Packet h) h)
   | Seq e1 e2 => Kleisli (eval e1) (eval e2) h
   | Star e1 => fun (y : history) => exists (i : nat), (iter (eval e1) i h y)
  end.

Definition equiv_exp (e1 : exp) (e2 : exp) : Prop := 
  forall (h : history),  (eval e1 h) = (eval e2 h).
 
