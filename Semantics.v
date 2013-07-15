Set Implicit Arguments.

Require Import Syntax.
Require Import Sets.
Require Import Coq.Arith.EqNat.


Axiom get_Field : packet -> field -> nat.

Axiom set_field : history -> field -> nat -> history.

Definition get_Packet (hst : history) : packet :=
  match hst with
    | OneHist p => p
    | ConsHist p h => p
  end.
Check empty.

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
  | _ => @empty history
  end.
