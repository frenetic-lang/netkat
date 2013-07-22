Set Implicit Arguments.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.

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
    
    (* JNF: minor, but suggest calling this 'iter' *)
    Fixpoint expt (R : relation) (n : nat) : relation :=
      match n with
        | 0 => id
        | S m => join R (expt R m)
      end.
    
    Definition star (R : relation) : relation :=
      fun (x y : A) => exists n, (expt R n) x y.

    Definition equiv (R1 R2 : relation) :=
      forall (x y : A), R1 x y <-> R2 x y.

   (* JNF: Let's change the name. Calling this 'inv' is confusing. *)
   Definition inv (R : relation) : relation :=
     fun (x y : A) => ((R x y) /\ False) \/ (~(R x y) /\ (x = y)).
  
  Definition contains (R1 R2 : relation) : Prop :=
     forall (x y : A), R1 x y -> R2 x y.

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