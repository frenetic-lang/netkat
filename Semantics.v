Set Implicit Arguments.

Require Import Relation.
Require Import Packet.
Require Import Syntax.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
  
  Definition set_field (h : history) (fld : field) (n : val) : history :=
    match h with
      | OneHist p => OneHist (Packet.set_field fld n p)
      | ConsHist p hst => ConsHist (Packet.set_field fld n p) hst
    end.        
  
  Definition get_packet (hst : history) : packet :=
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
          match Packet.beq_val (Packet.get_field f (get_packet h)) v with 
            | true => h = r
            | false => False
          end
      | Mod f v => 
        fun (h r : history) => r = set_field h f v
      | Par e1 e2 => union (eval e1) (eval e2)
      | Neg e1 => inv (eval e1)
      | Obs => fun (h r : history) => r = (ConsHist (get_packet h) h)
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
