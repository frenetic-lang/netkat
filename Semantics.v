Set Implicit Arguments.

Require Import Syntax.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.

Module Relation.

  Section Defs.

    Variable A : Type.
    
    Definition relation := A -> A -> Prop.
    
    Definition union (R1 R2 : relation) : relation :=
      fun (x y : A) => R1 x y \/ R2 x y.
    
    Definition join (R1 R2 : relation) : relation :=
      fun (x y : A) => exists (z : A), R1 x z /\ R2 z y.
    
    Definition empty : relation :=
      fun (x y : A) => False.
    
    Definition id : relation :=
      fun (x y : A) => x = y.
    
    Fixpoint expt (R : relation) (n : nat) : relation :=
      match n with
        | 0 => id
        | S m => join R (expt R m)
      end.
    
    Definition star (R : relation) : relation :=
      fun (x y : A) => exists n, (expt R n) x y.

    Definition inv (R : relation) : relation :=
      fun (x y : A) => R x y -> False /\ (R x y -> False) -> True.

    Definition equiv (R1 R2 : relation) :=
      forall (x y : A), R1 x y <-> R2 x y.

  End Defs.

  Instance Equivalence_equiv `(A : Type) : Equivalence (@equiv A).
  Proof with auto.
    split; unfold equiv.
    + unfold Reflexive.
      intros. intuition.
    + unfold Symmetric.
      intros. symmetry. apply H.
    + unfold Transitive.
      intros.
      split... 
      - intros.
        apply H0.
        apply H...
      - intros.
        apply H.
        apply H0...
  Qed.

End Relation.

Module Semantics.

  Import Relation.

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

  Locate exp.
  Check exp.
  Check relation.
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
      | Obs => fun (h r : history) => r= (ConsHist (get_Packet h) h)
      | Seq e1 e2 => join (eval e1) (eval e2)
      | Star e1 => star (eval e1)
    end.

  Definition equiv_exp (e1 : exp) (e2 : exp) : Prop := 
    equiv (eval e1) (eval e2).

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

End Semantics.

Module BooleanAlgebra.

  Import Semantics.
  Import Syntax.
  Import Relation.

  Existing Instances Equivalence_exp.
  Local Open Scope equiv_scope.


  (* Predicates are either identity or empty *)
  Lemma bool_spec : forall (e : exp),
    pred e ->
    forall (h r : history),
      eval e h r -> (False \/ h = r).
  Proof with auto.
    intros.
    induction H...
  Admitted.

  Lemma BA_Plus_One : 
    forall (e : exp),
      pred e ->
      (Par e Id) === Id.
  Proof with auto.
    intros.
    split.
    + intros. simpl in *. 
      unfold union in H0.
      destruct H0...
      destruct (bool_spec H x y H0)...
      contradiction.
    + intros.
      simpl in *.
      unfold union...
  Qed.

  Lemma BA_Excl_Mid : 
    