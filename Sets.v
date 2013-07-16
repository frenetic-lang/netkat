Set Implicit Arguments.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Section Sets.
  
  Variable A : Type.
  
  Definition set := A -> Prop.

  Definition singleton (a : A) : set := fun (b : A) => a = b.

  Definition empty : set := fun (_ : A) => False.

  Definition union (set1 set2 : set) : set := fun (y : A) => set1 y \/ set2 y.

  Definition set_minus (set1 set2 : set) : set := fun (y : A) => set1 y /\ ~set2 y.

  Definition indexed_union (f : nat -> set) : set := fun (y : A) => exists (n : nat), f n y.

  Definition subset (set1 set2 : set) : Prop := forall (a : A), set1 a -> set2 a.

  Definition equiv (set1 set2 : set) : Prop := forall (a : A), set1 a -> set2 a /\ set2 a -> set1 a.

  Hint Unfold singleton empty union subset set_minus indexed_union.

  Instance Set_equiv : Equivalence equiv.
  Proof with auto.
    split.
    + unfold Reflexive.
      intros. unfold equiv. auto.
    + unfold Symmetric.
      intros. unfold equiv. auto.
    + unfold Transitive.
      intros. unfold equiv. auto.
      Qed.

  Instance union_m : 
    Proper (equiv ==> equiv ==> equiv) union.
  Proof with auto.
    unfold Proper.
    unfold respectful.
    intros.
    unfold equiv in *.
    intros.
    apply H1.
  Qed.

  Add Morphism union with signature
    equiv ++> equiv ++> equiv as union_s_m.
  Proof. 
   apply union_m.
  Qed.

End Sets.

Add Parametric Morphism (A : Type) : (@union A) with signature
  @equiv A ++> @equiv A ++> @equiv A as union_s_m_x.
  Proof.
  intros.
  apply union_m. auto. auto.
  Qed.
  