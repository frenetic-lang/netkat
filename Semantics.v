Set Implicit Arguments.

Require Import Relation.
Require Import Syntax.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.

  Definition get_Field (pkt : packet) (fld : field) : nat :=
    match fld with
      | Src => pktSrc pkt
      | Dst => pktDst pkt
    end.
  
  Definition set_field_p (p : packet) (fld : field) (n : nat) : packet :=
    match fld with 
      | Src => Packet n (get_Field p Dst)
      | Dst => Packet (get_Field p Src) n
    end.
  
  Definition set_field (h : history) (fld : field) (n : nat) : history :=
    match h with
      | OneHist p => OneHist (set_field_p p fld n)
      | ConsHist p hst => ConsHist (set_field_p p fld n) hst
    end.        

  Definition get_Packet (hst : history) : packet :=
    match hst with
      | OneHist p => p
      | ConsHist p h => p
    end.

  Fixpoint eval (e : exp) : relation history :=
    match e with
      | Drop => @empty history
      | Id => @id history
      | Match f v => 
        fun (h r : history) =>
          match beq_nat (get_Field (get_Packet h) f) v with 
            | true => h = r
            | false => False
          end
      | Mod f v => 
        fun (h r : history) => r = set_field h f v
      | Par e1 e2 => union (eval e1) (eval e2)
      | Neg e1 => inv (eval e1)
      | Obs => fun (h r : history) => r = (ConsHist (get_Packet h) h)
      | Seq e1 e2 => join (eval e1) (eval e2)
      | Star e1 => star (eval e1)
    end.

  Existing Instances Equivalence_equiv.
  Local Open Scope equiv_scope.

  Definition equiv_exp (e1 : exp) (e2 : exp) : Prop := 
    (eval e1) === (eval e2).

  Instance Equivalence_exp : Equivalence equiv_exp.
  Proof with auto.
    unfold equiv_exp.
    split.
    + unfold Reflexive.
      intros.
      apply reflexivity.
    + unfold Symmetric.
      intros.
      apply symmetry...
    + unfold Transitive.
      intros.
      eapply transitivity; eauto.
  Qed.
 
  Definition contains_exp (e1 e2 : exp) : Prop :=
    (contains (eval e1) (eval e2)).
