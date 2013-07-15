Set Implicit Arguments.
Require Import Coq.Classes.Equivalence.

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

End Sets.

